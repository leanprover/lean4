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
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_isRecCore(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
lean_object* lean_array_uget(lean_object*, size_t);
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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqLiteral_beq(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t l_Lean_Literal_hash(lean_object*);
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
lean_object* l_Array_instInhabited___redArg();
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
static const lean_array_object l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__1;
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2;
static const lean_array_object l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg();
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___redArg();
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie(lean_object*);
static const lean_array_object l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg();
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Trie_pushPending___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Trie_pushPending(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabited___redArg();
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0;
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
static const lean_array_object l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg();
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___redArg();
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___redArg___boxed(lean_object*);
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
static const lean_closure_object l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend___redArg();
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend___redArg___boxed(lean_object*);
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
static const lean_array_object l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__7;
static const lean_ctor_object l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__8_value;
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__9;
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10;
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11;
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12;
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___redArg();
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_append(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_LazyDiscrTree_InitResults_append, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___redArg();
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___redArg___boxed(lean_object*);
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
lean_object* v___y_780_; uint8_t v___y_790_; lean_object* v___y_791_; uint8_t v___y_792_; lean_object* v___y_793_; lean_object* v___y_794_; lean_object* v_toCold_799_; lean_object* v_currRecDepth_800_; lean_object* v_ref_801_; uint8_t v_diag_802_; uint8_t v_suppressElabErrors_803_; lean_object* v_maxRecDepth_804_; lean_object* v_cancelTk_x3f_805_; 
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
v___x_796_ = lean_nat_add(v___y_791_, v___x_795_);
lean_inc_ref(v___y_794_);
v___x_797_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_797_, 0, v___y_794_);
lean_ctor_set(v___x_797_, 1, v___x_796_);
lean_ctor_set(v___x_797_, 2, v___y_793_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*3, v___y_790_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*3 + 1, v___y_792_);
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
v___y_790_ = v_diag_802_;
v___y_791_ = v_currRecDepth_800_;
v___y_792_ = v_suppressElabErrors_803_;
v___y_793_ = v_ref_801_;
v___y_794_ = v_toCold_799_;
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
v___y_790_ = v_diag_802_;
v___y_791_ = v_currRecDepth_800_;
v___y_792_ = v_suppressElabErrors_803_;
v___y_793_ = v_ref_801_;
v___y_794_ = v_toCold_799_;
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
lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v_nbuckets_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_920_ = lean_array_get_size(v_data_919_);
v___x_921_ = lean_unsigned_to_nat(2u);
v_nbuckets_922_ = lean_nat_mul(v___x_920_, v___x_921_);
v___x_923_ = lean_unsigned_to_nat(0u);
v___x_924_ = lean_box(0);
v___x_925_ = lean_mk_array(v_nbuckets_922_, v___x_924_);
v___x_926_ = lean_array_propagate_mark(v_data_919_, v___x_925_);
v___x_927_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v___x_923_, v_data_919_, v___x_926_);
return v___x_927_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(lean_object* v_a_928_, lean_object* v_x_929_){
_start:
{
if (lean_obj_tag(v_x_929_) == 0)
{
uint8_t v___x_930_; 
v___x_930_ = 0;
return v___x_930_;
}
else
{
lean_object* v_key_931_; lean_object* v_tail_932_; uint8_t v___x_933_; 
v_key_931_ = lean_ctor_get(v_x_929_, 0);
v_tail_932_ = lean_ctor_get(v_x_929_, 2);
v___x_933_ = l_Lean_ExprStructEq_beq(v_key_931_, v_a_928_);
if (v___x_933_ == 0)
{
v_x_929_ = v_tail_932_;
goto _start;
}
else
{
return v___x_933_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg___boxed(lean_object* v_a_935_, lean_object* v_x_936_){
_start:
{
uint8_t v_res_937_; lean_object* v_r_938_; 
v_res_937_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(v_a_935_, v_x_936_);
lean_dec(v_x_936_);
lean_dec_ref(v_a_935_);
v_r_938_ = lean_box(v_res_937_);
return v_r_938_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6___redArg(lean_object* v_m_939_, lean_object* v_a_940_, lean_object* v_b_941_){
_start:
{
lean_object* v_size_942_; lean_object* v_buckets_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_986_; 
v_size_942_ = lean_ctor_get(v_m_939_, 0);
v_buckets_943_ = lean_ctor_get(v_m_939_, 1);
v_isSharedCheck_986_ = !lean_is_exclusive(v_m_939_);
if (v_isSharedCheck_986_ == 0)
{
v___x_945_ = v_m_939_;
v_isShared_946_ = v_isSharedCheck_986_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_buckets_943_);
lean_inc(v_size_942_);
lean_dec(v_m_939_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_986_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_947_; uint64_t v___x_948_; uint64_t v___x_949_; uint64_t v___x_950_; uint64_t v_fold_951_; uint64_t v___x_952_; uint64_t v___x_953_; uint64_t v___x_954_; size_t v___x_955_; size_t v___x_956_; size_t v___x_957_; size_t v___x_958_; size_t v___x_959_; lean_object* v_bkt_960_; uint8_t v___x_961_; 
v___x_947_ = lean_array_get_size(v_buckets_943_);
v___x_948_ = l_Lean_ExprStructEq_hash(v_a_940_);
v___x_949_ = 32ULL;
v___x_950_ = lean_uint64_shift_right(v___x_948_, v___x_949_);
v_fold_951_ = lean_uint64_xor(v___x_948_, v___x_950_);
v___x_952_ = 16ULL;
v___x_953_ = lean_uint64_shift_right(v_fold_951_, v___x_952_);
v___x_954_ = lean_uint64_xor(v_fold_951_, v___x_953_);
v___x_955_ = lean_uint64_to_usize(v___x_954_);
v___x_956_ = lean_usize_of_nat(v___x_947_);
v___x_957_ = ((size_t)1ULL);
v___x_958_ = lean_usize_sub(v___x_956_, v___x_957_);
v___x_959_ = lean_usize_land(v___x_955_, v___x_958_);
v_bkt_960_ = lean_array_uget_borrowed(v_buckets_943_, v___x_959_);
v___x_961_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(v_a_940_, v_bkt_960_);
if (v___x_961_ == 0)
{
lean_object* v___x_962_; lean_object* v_size_x27_963_; lean_object* v___x_964_; lean_object* v_buckets_x27_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; uint8_t v___x_971_; 
v___x_962_ = lean_unsigned_to_nat(1u);
v_size_x27_963_ = lean_nat_add(v_size_942_, v___x_962_);
lean_dec(v_size_942_);
lean_inc(v_bkt_960_);
v___x_964_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_964_, 0, v_a_940_);
lean_ctor_set(v___x_964_, 1, v_b_941_);
lean_ctor_set(v___x_964_, 2, v_bkt_960_);
v_buckets_x27_965_ = lean_array_uset(v_buckets_943_, v___x_959_, v___x_964_);
v___x_966_ = lean_unsigned_to_nat(4u);
v___x_967_ = lean_nat_mul(v_size_x27_963_, v___x_966_);
v___x_968_ = lean_unsigned_to_nat(3u);
v___x_969_ = lean_nat_div(v___x_967_, v___x_968_);
lean_dec(v___x_967_);
v___x_970_ = lean_array_get_size(v_buckets_x27_965_);
v___x_971_ = lean_nat_dec_le(v___x_969_, v___x_970_);
lean_dec(v___x_969_);
if (v___x_971_ == 0)
{
lean_object* v_val_972_; lean_object* v___x_974_; 
v_val_972_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11___redArg(v_buckets_x27_965_);
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 1, v_val_972_);
lean_ctor_set(v___x_945_, 0, v_size_x27_963_);
v___x_974_ = v___x_945_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_size_x27_963_);
lean_ctor_set(v_reuseFailAlloc_975_, 1, v_val_972_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
else
{
lean_object* v___x_977_; 
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 1, v_buckets_x27_965_);
lean_ctor_set(v___x_945_, 0, v_size_x27_963_);
v___x_977_ = v___x_945_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_size_x27_963_);
lean_ctor_set(v_reuseFailAlloc_978_, 1, v_buckets_x27_965_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
else
{
lean_object* v___x_979_; lean_object* v_buckets_x27_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_984_; 
lean_inc(v_bkt_960_);
v___x_979_ = lean_box(0);
v_buckets_x27_980_ = lean_array_uset(v_buckets_943_, v___x_959_, v___x_979_);
v___x_981_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12___redArg(v_a_940_, v_b_941_, v_bkt_960_);
v___x_982_ = lean_array_uset(v_buckets_x27_980_, v___x_959_, v___x_981_);
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 1, v___x_982_);
v___x_984_ = v___x_945_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_size_942_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v___x_982_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2(lean_object* v_a_987_, lean_object* v_e_988_, lean_object* v_a_989_){
_start:
{
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_991_ = lean_st_ref_take(v_a_987_);
v___x_992_ = lean_box(0);
v___x_993_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6___redArg(v___x_991_, v_e_988_, v_a_989_);
v___x_994_ = lean_st_ref_put(v_a_987_, v___x_993_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2___boxed(lean_object* v_a_995_, lean_object* v_e_996_, lean_object* v_a_997_, lean_object* v___y_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2(v_a_995_, v_e_996_, v_a_997_);
lean_dec(v_a_995_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_1000_, lean_object* v_x_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1005_ = lean_apply_1(v_x_1001_, lean_box(0));
v___x_1006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1007_, lean_object* v_x_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(v_00_u03b1_1007_, v_x_1008_, v___y_1009_, v___y_1010_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
return v_res_1012_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0(void){
_start:
{
lean_object* v___x_1014_; lean_object* v_dummy_1015_; 
v___x_1014_ = lean_box(0);
v_dummy_1015_ = l_Lean_Expr_sort___override(v___x_1014_);
return v_dummy_1015_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1(lean_object* v_pre_1016_, lean_object* v_post_1017_, size_t v_sz_1018_, size_t v_i_1019_, lean_object* v_bs_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
uint8_t v___x_1025_; 
v___x_1025_ = lean_usize_dec_lt(v_i_1019_, v_sz_1018_);
if (v___x_1025_ == 0)
{
lean_object* v___x_1026_; 
lean_dec_ref(v_post_1017_);
lean_dec_ref(v_pre_1016_);
v___x_1026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1026_, 0, v_bs_1020_);
return v___x_1026_;
}
else
{
lean_object* v_v_1027_; lean_object* v___x_1028_; lean_object* v_bs_x27_1029_; lean_object* v___x_1030_; 
v_v_1027_ = lean_array_uget(v_bs_1020_, v_i_1019_);
v___x_1028_ = lean_unsigned_to_nat(0u);
v_bs_x27_1029_ = lean_array_uset(v_bs_1020_, v_i_1019_, v___x_1028_);
lean_inc_ref(v_post_1017_);
lean_inc_ref(v_pre_1016_);
v___x_1030_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1016_, v_post_1017_, v_v_1027_, v___y_1021_, v___y_1022_, v___y_1023_);
if (lean_obj_tag(v___x_1030_) == 0)
{
lean_object* v_a_1031_; size_t v___x_1032_; size_t v___x_1033_; lean_object* v___x_1034_; 
v_a_1031_ = lean_ctor_get(v___x_1030_, 0);
lean_inc(v_a_1031_);
lean_dec_ref_known(v___x_1030_, 1);
v___x_1032_ = ((size_t)1ULL);
v___x_1033_ = lean_usize_add(v_i_1019_, v___x_1032_);
v___x_1034_ = lean_array_uset(v_bs_x27_1029_, v_i_1019_, v_a_1031_);
v_i_1019_ = v___x_1033_;
v_bs_1020_ = v___x_1034_;
goto _start;
}
else
{
lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1043_; 
lean_dec_ref(v_bs_x27_1029_);
lean_dec_ref(v_post_1017_);
lean_dec_ref(v_pre_1016_);
v_a_1036_ = lean_ctor_get(v___x_1030_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1038_ = v___x_1030_;
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_dec(v___x_1030_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1041_; 
if (v_isShared_1039_ == 0)
{
v___x_1041_ = v___x_1038_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_a_1036_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4(lean_object* v_pre_1044_, lean_object* v_post_1045_, lean_object* v_x_1046_, lean_object* v_x_1047_, lean_object* v_x_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
if (lean_obj_tag(v_x_1046_) == 5)
{
lean_object* v_fn_1053_; lean_object* v_arg_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
v_fn_1053_ = lean_ctor_get(v_x_1046_, 0);
lean_inc_ref(v_fn_1053_);
v_arg_1054_ = lean_ctor_get(v_x_1046_, 1);
lean_inc_ref(v_arg_1054_);
lean_dec_ref_known(v_x_1046_, 2);
v___x_1055_ = lean_array_set(v_x_1047_, v_x_1048_, v_arg_1054_);
v___x_1056_ = lean_unsigned_to_nat(1u);
v___x_1057_ = lean_nat_sub(v_x_1048_, v___x_1056_);
lean_dec(v_x_1048_);
v_x_1046_ = v_fn_1053_;
v_x_1047_ = v___x_1055_;
v_x_1048_ = v___x_1057_;
goto _start;
}
else
{
lean_object* v___x_1059_; 
lean_dec(v_x_1048_);
lean_inc_ref(v_post_1045_);
lean_inc_ref(v_pre_1044_);
v___x_1059_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1044_, v_post_1045_, v_x_1046_, v___y_1049_, v___y_1050_, v___y_1051_);
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_object* v_a_1060_; size_t v_sz_1061_; size_t v___x_1062_; lean_object* v___x_1063_; 
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
lean_inc(v_a_1060_);
lean_dec_ref_known(v___x_1059_, 1);
v_sz_1061_ = lean_array_size(v_x_1047_);
v___x_1062_ = ((size_t)0ULL);
lean_inc_ref(v_post_1045_);
lean_inc_ref(v_pre_1044_);
v___x_1063_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1(v_pre_1044_, v_post_1045_, v_sz_1061_, v___x_1062_, v_x_1047_, v___y_1049_, v___y_1050_, v___y_1051_);
if (lean_obj_tag(v___x_1063_) == 0)
{
lean_object* v_a_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; 
v_a_1064_ = lean_ctor_get(v___x_1063_, 0);
lean_inc(v_a_1064_);
lean_dec_ref_known(v___x_1063_, 1);
v___x_1065_ = l_Lean_mkAppN(v_a_1060_, v_a_1064_);
lean_dec(v_a_1064_);
v___x_1066_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1044_, v_post_1045_, v___x_1065_, v___y_1049_, v___y_1050_, v___y_1051_);
return v___x_1066_;
}
else
{
lean_object* v_a_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1074_; 
lean_dec(v_a_1060_);
lean_dec_ref(v_post_1045_);
lean_dec_ref(v_pre_1044_);
v_a_1067_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1069_ = v___x_1063_;
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_a_1067_);
lean_dec(v___x_1063_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1072_; 
if (v_isShared_1070_ == 0)
{
v___x_1072_ = v___x_1069_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_a_1067_);
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
else
{
lean_dec_ref(v_x_1047_);
lean_dec_ref(v_post_1045_);
lean_dec_ref(v_pre_1044_);
return v___x_1059_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1(lean_object* v___x_1075_, lean_object* v_pre_1076_, lean_object* v_e_1077_, lean_object* v_post_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_){
_start:
{
lean_object* v___x_1083_; 
v___x_1083_ = l_Lean_Core_checkSystem(v___x_1075_, v___y_1080_, v___y_1081_);
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_object* v___x_1084_; 
lean_dec_ref_known(v___x_1083_, 1);
lean_inc_ref(v_pre_1076_);
lean_inc(v___y_1081_);
lean_inc_ref(v___y_1080_);
lean_inc_ref(v_e_1077_);
v___x_1084_ = lean_apply_4(v_pre_1076_, v_e_1077_, v___y_1080_, v___y_1081_, lean_box(0));
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1200_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1087_ = v___x_1084_;
v_isShared_1088_ = v_isSharedCheck_1200_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1084_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1200_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___y_1090_; 
switch(lean_obj_tag(v_a_1085_))
{
case 0:
{
lean_object* v_e_1190_; lean_object* v___x_1192_; 
lean_dec_ref(v_post_1078_);
lean_dec_ref(v_e_1077_);
lean_dec_ref(v_pre_1076_);
v_e_1190_ = lean_ctor_get(v_a_1085_, 0);
lean_inc_ref(v_e_1190_);
lean_dec_ref_known(v_a_1085_, 1);
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 0, v_e_1190_);
v___x_1192_ = v___x_1087_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_e_1190_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
case 1:
{
lean_object* v_e_1194_; lean_object* v___x_1195_; 
lean_del_object(v___x_1087_);
lean_dec_ref(v_e_1077_);
v_e_1194_ = lean_ctor_get(v_a_1085_, 0);
lean_inc_ref(v_e_1194_);
lean_dec_ref_known(v_a_1085_, 1);
lean_inc_ref(v_post_1078_);
lean_inc_ref(v_pre_1076_);
v___x_1195_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1076_, v_post_1078_, v_e_1194_, v___y_1079_, v___y_1080_, v___y_1081_);
if (lean_obj_tag(v___x_1195_) == 0)
{
lean_object* v_a_1196_; lean_object* v___x_1197_; 
v_a_1196_ = lean_ctor_get(v___x_1195_, 0);
lean_inc(v_a_1196_);
lean_dec_ref_known(v___x_1195_, 1);
v___x_1197_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1076_, v_post_1078_, v_a_1196_, v___y_1079_, v___y_1080_, v___y_1081_);
return v___x_1197_;
}
else
{
lean_dec_ref(v_post_1078_);
lean_dec_ref(v_pre_1076_);
return v___x_1195_;
}
}
default: 
{
lean_object* v_e_x3f_1198_; 
lean_del_object(v___x_1087_);
v_e_x3f_1198_ = lean_ctor_get(v_a_1085_, 0);
lean_inc(v_e_x3f_1198_);
lean_dec_ref_known(v_a_1085_, 1);
if (lean_obj_tag(v_e_x3f_1198_) == 0)
{
v___y_1090_ = v_e_1077_;
goto v___jp_1089_;
}
else
{
lean_object* v_val_1199_; 
lean_dec_ref(v_e_1077_);
v_val_1199_ = lean_ctor_get(v_e_x3f_1198_, 0);
lean_inc(v_val_1199_);
lean_dec_ref_known(v_e_x3f_1198_, 1);
v___y_1090_ = v_val_1199_;
goto v___jp_1089_;
}
}
}
v___jp_1089_:
{
switch(lean_obj_tag(v___y_1090_))
{
case 7:
{
lean_object* v_binderName_1091_; lean_object* v_binderType_1092_; lean_object* v_body_1093_; uint8_t v_binderInfo_1094_; lean_object* v___x_1095_; 
v_binderName_1091_ = lean_ctor_get(v___y_1090_, 0);
v_binderType_1092_ = lean_ctor_get(v___y_1090_, 1);
v_body_1093_ = lean_ctor_get(v___y_1090_, 2);
v_binderInfo_1094_ = lean_ctor_get_uint8(v___y_1090_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1092_);
lean_inc_ref(v_post_1078_);
lean_inc_ref(v_pre_1076_);
v___x_1095_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1076_, v_post_1078_, v_binderType_1092_, v___y_1079_, v___y_1080_, v___y_1081_);
if (lean_obj_tag(v___x_1095_) == 0)
{
lean_object* v_a_1096_; lean_object* v___x_1097_; 
v_a_1096_ = lean_ctor_get(v___x_1095_, 0);
lean_inc(v_a_1096_);
lean_dec_ref_known(v___x_1095_, 1);
lean_inc_ref(v_body_1093_);
lean_inc_ref(v_post_1078_);
lean_inc_ref(v_pre_1076_);
v___x_1097_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1076_, v_post_1078_, v_body_1093_, v___y_1079_, v___y_1080_, v___y_1081_);
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_object* v_a_1098_; size_t v___x_1099_; size_t v___x_1100_; uint8_t v___x_1101_; 
v_a_1098_ = lean_ctor_get(v___x_1097_, 0);
lean_inc(v_a_1098_);
lean_dec_ref_known(v___x_1097_, 1);
v___x_1099_ = lean_ptr_addr(v_binderType_1092_);
v___x_1100_ = lean_ptr_addr(v_a_1096_);
v___x_1101_ = lean_usize_dec_eq(v___x_1099_, v___x_1100_);
if (v___x_1101_ == 0)
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
lean_inc(v_binderName_1091_);
lean_dec_ref_known(v___y_1090_, 3);
v___x_1102_ = l_Lean_Expr_forallE___override(v_binderName_1091_, v_a_1096_, v_a_1098_, v_binderInfo_1094_);
v___x_1103_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1076_, v_post_1078_, v___x_1102_, v___y_1079_, v___y_1080_, v___y_1081_);
return v___x_1103_;
}
else
{
size_t v___x_1104_; size_t v___x_1105_; uint8_t v___x_1106_; 
v___x_1104_ = lean_ptr_addr(v_body_1093_);
v___x_1105_ = lean_ptr_addr(v_a_1098_);
v___x_1106_ = lean_usize_dec_eq(v___x_1104_, v___x_1105_);
if (v___x_1106_ == 0)
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
lean_inc(v_binderName_1091_);
lean_dec_ref_known(v___y_1090_, 3);
v___x_1107_ = l_Lean_Expr_forallE___override(v_binderName_1091_, v_a_1096_, v_a_1098_, v_binderInfo_1094_);
v___x_1108_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1076_, v_post_1078_, v___x_1107_, v___y_1079_, v___y_1080_, v___y_1081_);
return v___x_1108_;
}
else
{
uint8_t v___x_1109_; 
v___x_1109_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1094_, v_binderInfo_1094_);
if (v___x_1109_ == 0)
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
lean_inc(v_binderName_1091_);
lean_dec_ref_known(v___y_1090_, 3);
v___x_1110_ = l_Lean_Expr_forallE___override(v_binderName_1091_, v_a_1096_, v_a_1098_, v_binderInfo_1094_);
v___x_1111_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1076_, v_post_1078_, v___x_1110_, v___y_1079_, v___y_1080_, v___y_1081_);
return v___x_1111_;
}
else
{
lean_object* v___x_1112_; 
lean_dec(v_a_1098_);
lean_dec(v_a_1096_);
v___x_1112_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1076_, v_post_1078_, v___y_1090_, v___y_1079_, v___y_1080_, v___y_1081_);
return v___x_1112_;
}
}
}
}
else
{
lean_dec(v_a_1096_);
lean_dec_ref_known(v___y_1090_, 3);
lean_dec_ref(v_post_1078_);
lean_dec_ref(v_pre_1076_);
return v___x_1097_;
}
}
else
{
lean_dec_ref_known(v___y_1090_, 3);
lean_dec_ref(v_post_1078_);
lean_dec_ref(v_pre_1076_);
return v___x_1095_;
}
}
case 6:
{
lean_object* v_binderName_1113_; lean_object* v_binderType_1114_; lean_object* v_body_1115_; uint8_t v_binderInfo_1116_; lean_object* v___x_1117_; 
v_binderName_1113_ = lean_ctor_get(v___y_1090_, 0);
v_binderType_1114_ = lean_ctor_get(v___y_1090_, 1);
v_body_1115_ = lean_ctor_get(v___y_1090_, 2);
v_binderInfo_1116_ = lean_ctor_get_uint8(v___y_1090_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1114_);
lean_inc_ref(v_post_1078_);
lean_inc_ref(v_pre_1076_);
v___x_1117_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1076_, v_post_1078_, v_binderType_1114_, v___y_1079_, v___y_1080_, v___y_1081_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; lean_object* v___x_1119_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
lean_inc(v_a_1118_);
lean_dec_ref_known(v___x_1117_, 1);
lean_inc_ref(v_body_1115_);
lean_inc_ref(v_post_1078_);
lean_inc_ref(v_pre_1076_);
v___x_1119_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1076_, v_post_1078_, v_body_1115_, v___y_1079_, v___y_1080_, v___y_1081_);
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v_a_1120_; size_t v___x_1121_; size_t v___x_1122_; uint8_t v___x_1123_; 
v_a_1120_ = lean_ctor_get(v___x_1119_, 0);
lean_inc(v_a_1120_);
lean_dec_ref_known(v___x_1119_, 1);
v___x_1121_ = lean_ptr_addr(v_binderType_1114_);
v___x_1122_ = lean_ptr_addr(v_a_1118_);
v___x_1123_ = lean_usize_dec_eq(v___x_1121_, v___x_1122_);
if (v___x_1123_ == 0)
{
lean_object* v___x_1124_; lean_object* v___x_1125_; 
lean_inc(v_binderName_1113_);
lean_dec_ref_known(v___y_1090_, 3);
v___x_1124_ = l_Lean_Expr_lam___override(v_binderName_1113_, v_a_1118_, v_a_1120_, v_binderInfo_1116_);
v___x_1125_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1076_, v_post_1078_, v___x_1124_, v___y_1079_, v___y_1080_, v___y_1081_);
return v___x_1125_;
}
else
{
size_t v___x_1126_; size_t v___x_1127_; uint8_t v___x_1128_; 
v___x_1126_ = lean_ptr_addr(v_body_1115_);
v___x_1127_ = lean_ptr_addr(v_a_1120_);
v___x_1128_ = lean_usize_dec_eq(v___x_1126_, v___x_1127_);
if (v___x_1128_ == 0)
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
lean_inc(v_binderName_1113_);
lean_dec_ref_known(v___y_1090_, 3);
v___x_1129_ = l_Lean_Expr_lam___override(v_binderName_1113_, v_a_1118_, v_a_1120_, v_binderInfo_1116_);
v___x_1130_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1076_, v_post_1078_, v___x_1129_, v___y_1079_, v___y_1080_, v___y_1081_);
return v___x_1130_;
}
else
{
uint8_t v___x_1131_; 
v___x_1131_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1116_, v_binderInfo_1116_);
if (v___x_1131_ == 0)
{
lean_object* v___x_1132_; lean_object* v___x_1133_; 
lean_inc(v_binderName_1113_);
lean_dec_ref_known(v___y_1090_, 3);
v___x_1132_ = l_Lean_Expr_lam___override(v_binderName_1113_, v_a_1118_, v_a_1120_, v_binderInfo_1116_);
v___x_1133_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1076_, v_post_1078_, v___x_1132_, v___y_1079_, v___y_1080_, v___y_1081_);
return v___x_1133_;
}
else
{
lean_object* v___x_1134_; 
lean_dec(v_a_1120_);
lean_dec(v_a_1118_);
v___x_1134_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1076_, v_post_1078_, v___y_1090_, v___y_1079_, v___y_1080_, v___y_1081_);
return v___x_1134_;
}
}
}
}
else
{
lean_dec(v_a_1118_);
lean_dec_ref_known(v___y_1090_, 3);
lean_dec_ref(v_post_1078_);
lean_dec_ref(v_pre_1076_);
return v___x_1119_;
}
}
else
{
lean_dec_ref_known(v___y_1090_, 3);
lean_dec_ref(v_post_1078_);
lean_dec_ref(v_pre_1076_);
return v___x_1117_;
}
}
case 8:
{
lean_object* v_declName_1135_; lean_object* v_type_1136_; lean_object* v_value_1137_; lean_object* v_body_1138_; uint8_t v_nondep_1139_; lean_object* v___x_1140_; 
v_declName_1135_ = lean_ctor_get(v___y_1090_, 0);
v_type_1136_ = lean_ctor_get(v___y_1090_, 1);
v_value_1137_ = lean_ctor_get(v___y_1090_, 2);
v_body_1138_ = lean_ctor_get(v___y_1090_, 3);
v_nondep_1139_ = lean_ctor_get_uint8(v___y_1090_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_1136_);
lean_inc_ref(v_post_1078_);
lean_inc_ref(v_pre_1076_);
v___x_1140_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1076_, v_post_1078_, v_type_1136_, v___y_1079_, v___y_1080_, v___y_1081_);
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_object* v_a_1141_; lean_object* v___x_1142_; 
v_a_1141_ = lean_ctor_get(v___x_1140_, 0);
lean_inc(v_a_1141_);
lean_dec_ref_known(v___x_1140_, 1);
lean_inc_ref(v_value_1137_);
lean_inc_ref(v_post_1078_);
lean_inc_ref(v_pre_1076_);
v___x_1142_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1076_, v_post_1078_, v_value_1137_, v___y_1079_, v___y_1080_, v___y_1081_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_object* v_a_1143_; lean_object* v___x_1144_; 
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
lean_inc(v_a_1143_);
lean_dec_ref_known(v___x_1142_, 1);
lean_inc_ref(v_body_1138_);
lean_inc_ref(v_post_1078_);
lean_inc_ref(v_pre_1076_);
v___x_1144_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1076_, v_post_1078_, v_body_1138_, v___y_1079_, v___y_1080_, v___y_1081_);
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_object* v_a_1145_; size_t v___x_1146_; size_t v___x_1147_; uint8_t v___x_1148_; 
v_a_1145_ = lean_ctor_get(v___x_1144_, 0);
lean_inc(v_a_1145_);
lean_dec_ref_known(v___x_1144_, 1);
v___x_1146_ = lean_ptr_addr(v_type_1136_);
v___x_1147_ = lean_ptr_addr(v_a_1141_);
v___x_1148_ = lean_usize_dec_eq(v___x_1146_, v___x_1147_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
lean_inc(v_declName_1135_);
lean_dec_ref_known(v___y_1090_, 4);
v___x_1149_ = l_Lean_Expr_letE___override(v_declName_1135_, v_a_1141_, v_a_1143_, v_a_1145_, v_nondep_1139_);
v___x_1150_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1076_, v_post_1078_, v___x_1149_, v___y_1079_, v___y_1080_, v___y_1081_);
return v___x_1150_;
}
else
{
size_t v___x_1151_; size_t v___x_1152_; uint8_t v___x_1153_; 
v___x_1151_ = lean_ptr_addr(v_value_1137_);
v___x_1152_ = lean_ptr_addr(v_a_1143_);
v___x_1153_ = lean_usize_dec_eq(v___x_1151_, v___x_1152_);
if (v___x_1153_ == 0)
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
lean_inc(v_declName_1135_);
lean_dec_ref_known(v___y_1090_, 4);
v___x_1154_ = l_Lean_Expr_letE___override(v_declName_1135_, v_a_1141_, v_a_1143_, v_a_1145_, v_nondep_1139_);
v___x_1155_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1076_, v_post_1078_, v___x_1154_, v___y_1079_, v___y_1080_, v___y_1081_);
return v___x_1155_;
}
else
{
size_t v___x_1156_; size_t v___x_1157_; uint8_t v___x_1158_; 
v___x_1156_ = lean_ptr_addr(v_body_1138_);
v___x_1157_ = lean_ptr_addr(v_a_1145_);
v___x_1158_ = lean_usize_dec_eq(v___x_1156_, v___x_1157_);
if (v___x_1158_ == 0)
{
lean_object* v___x_1159_; lean_object* v___x_1160_; 
lean_inc(v_declName_1135_);
lean_dec_ref_known(v___y_1090_, 4);
v___x_1159_ = l_Lean_Expr_letE___override(v_declName_1135_, v_a_1141_, v_a_1143_, v_a_1145_, v_nondep_1139_);
v___x_1160_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1076_, v_post_1078_, v___x_1159_, v___y_1079_, v___y_1080_, v___y_1081_);
return v___x_1160_;
}
else
{
lean_object* v___x_1161_; 
lean_dec(v_a_1145_);
lean_dec(v_a_1143_);
lean_dec(v_a_1141_);
v___x_1161_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1076_, v_post_1078_, v___y_1090_, v___y_1079_, v___y_1080_, v___y_1081_);
return v___x_1161_;
}
}
}
}
else
{
lean_dec(v_a_1143_);
lean_dec(v_a_1141_);
lean_dec_ref_known(v___y_1090_, 4);
lean_dec_ref(v_post_1078_);
lean_dec_ref(v_pre_1076_);
return v___x_1144_;
}
}
else
{
lean_dec(v_a_1141_);
lean_dec_ref_known(v___y_1090_, 4);
lean_dec_ref(v_post_1078_);
lean_dec_ref(v_pre_1076_);
return v___x_1142_;
}
}
else
{
lean_dec_ref_known(v___y_1090_, 4);
lean_dec_ref(v_post_1078_);
lean_dec_ref(v_pre_1076_);
return v___x_1140_;
}
}
case 5:
{
lean_object* v_dummy_1162_; lean_object* v_nargs_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
v_dummy_1162_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0);
v_nargs_1163_ = l_Lean_Expr_getAppNumArgs(v___y_1090_);
lean_inc(v_nargs_1163_);
v___x_1164_ = lean_mk_array(v_nargs_1163_, v_dummy_1162_);
v___x_1165_ = lean_unsigned_to_nat(1u);
v___x_1166_ = lean_nat_sub(v_nargs_1163_, v___x_1165_);
lean_dec(v_nargs_1163_);
v___x_1167_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4(v_pre_1076_, v_post_1078_, v___y_1090_, v___x_1164_, v___x_1166_, v___y_1079_, v___y_1080_, v___y_1081_);
return v___x_1167_;
}
case 10:
{
lean_object* v_data_1168_; lean_object* v_expr_1169_; lean_object* v___x_1170_; 
v_data_1168_ = lean_ctor_get(v___y_1090_, 0);
v_expr_1169_ = lean_ctor_get(v___y_1090_, 1);
lean_inc_ref(v_expr_1169_);
lean_inc_ref(v_post_1078_);
lean_inc_ref(v_pre_1076_);
v___x_1170_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1076_, v_post_1078_, v_expr_1169_, v___y_1079_, v___y_1080_, v___y_1081_);
if (lean_obj_tag(v___x_1170_) == 0)
{
lean_object* v_a_1171_; size_t v___x_1172_; size_t v___x_1173_; uint8_t v___x_1174_; 
v_a_1171_ = lean_ctor_get(v___x_1170_, 0);
lean_inc(v_a_1171_);
lean_dec_ref_known(v___x_1170_, 1);
v___x_1172_ = lean_ptr_addr(v_expr_1169_);
v___x_1173_ = lean_ptr_addr(v_a_1171_);
v___x_1174_ = lean_usize_dec_eq(v___x_1172_, v___x_1173_);
if (v___x_1174_ == 0)
{
lean_object* v___x_1175_; lean_object* v___x_1176_; 
lean_inc(v_data_1168_);
lean_dec_ref_known(v___y_1090_, 2);
v___x_1175_ = l_Lean_Expr_mdata___override(v_data_1168_, v_a_1171_);
v___x_1176_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1076_, v_post_1078_, v___x_1175_, v___y_1079_, v___y_1080_, v___y_1081_);
return v___x_1176_;
}
else
{
lean_object* v___x_1177_; 
lean_dec(v_a_1171_);
v___x_1177_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1076_, v_post_1078_, v___y_1090_, v___y_1079_, v___y_1080_, v___y_1081_);
return v___x_1177_;
}
}
else
{
lean_dec_ref_known(v___y_1090_, 2);
lean_dec_ref(v_post_1078_);
lean_dec_ref(v_pre_1076_);
return v___x_1170_;
}
}
case 11:
{
lean_object* v_typeName_1178_; lean_object* v_idx_1179_; lean_object* v_struct_1180_; lean_object* v___x_1181_; 
v_typeName_1178_ = lean_ctor_get(v___y_1090_, 0);
v_idx_1179_ = lean_ctor_get(v___y_1090_, 1);
v_struct_1180_ = lean_ctor_get(v___y_1090_, 2);
lean_inc_ref(v_struct_1180_);
lean_inc_ref(v_post_1078_);
lean_inc_ref(v_pre_1076_);
v___x_1181_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1076_, v_post_1078_, v_struct_1180_, v___y_1079_, v___y_1080_, v___y_1081_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v_a_1182_; size_t v___x_1183_; size_t v___x_1184_; uint8_t v___x_1185_; 
v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
lean_inc(v_a_1182_);
lean_dec_ref_known(v___x_1181_, 1);
v___x_1183_ = lean_ptr_addr(v_struct_1180_);
v___x_1184_ = lean_ptr_addr(v_a_1182_);
v___x_1185_ = lean_usize_dec_eq(v___x_1183_, v___x_1184_);
if (v___x_1185_ == 0)
{
lean_object* v___x_1186_; lean_object* v___x_1187_; 
lean_inc(v_idx_1179_);
lean_inc(v_typeName_1178_);
lean_dec_ref_known(v___y_1090_, 3);
v___x_1186_ = l_Lean_Expr_proj___override(v_typeName_1178_, v_idx_1179_, v_a_1182_);
v___x_1187_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1076_, v_post_1078_, v___x_1186_, v___y_1079_, v___y_1080_, v___y_1081_);
return v___x_1187_;
}
else
{
lean_object* v___x_1188_; 
lean_dec(v_a_1182_);
v___x_1188_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1076_, v_post_1078_, v___y_1090_, v___y_1079_, v___y_1080_, v___y_1081_);
return v___x_1188_;
}
}
else
{
lean_dec_ref_known(v___y_1090_, 3);
lean_dec_ref(v_post_1078_);
lean_dec_ref(v_pre_1076_);
return v___x_1181_;
}
}
default: 
{
lean_object* v___x_1189_; 
v___x_1189_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1076_, v_post_1078_, v___y_1090_, v___y_1079_, v___y_1080_, v___y_1081_);
return v___x_1189_;
}
}
}
}
}
else
{
lean_object* v_a_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1208_; 
lean_dec_ref(v_post_1078_);
lean_dec_ref(v_e_1077_);
lean_dec_ref(v_pre_1076_);
v_a_1201_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1203_ = v___x_1084_;
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_a_1201_);
lean_dec(v___x_1084_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1206_; 
if (v_isShared_1204_ == 0)
{
v___x_1206_ = v___x_1203_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_a_1201_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
}
else
{
lean_object* v_a_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1216_; 
lean_dec_ref(v_post_1078_);
lean_dec_ref(v_e_1077_);
lean_dec_ref(v_pre_1076_);
v_a_1209_ = lean_ctor_get(v___x_1083_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1211_ = v___x_1083_;
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_a_1209_);
lean_dec(v___x_1083_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1214_; 
if (v_isShared_1212_ == 0)
{
v___x_1214_ = v___x_1211_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_a_1209_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___boxed(lean_object* v___x_1217_, lean_object* v_pre_1218_, lean_object* v_e_1219_, lean_object* v_post_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1(v___x_1217_, v_pre_1218_, v_e_1219_, v_post_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1221_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(lean_object* v_pre_1226_, lean_object* v_post_1227_, lean_object* v_e_1228_, lean_object* v_a_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; 
lean_inc(v_a_1229_);
v___x_1233_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1233_, 0, lean_box(0));
lean_closure_set(v___x_1233_, 1, lean_box(0));
lean_closure_set(v___x_1233_, 2, v_a_1229_);
v___x_1234_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(lean_box(0), v___x_1233_, v___y_1230_, v___y_1231_);
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_object* v_a_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1266_; 
v_a_1235_ = lean_ctor_get(v___x_1234_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1237_ = v___x_1234_;
v_isShared_1238_ = v_isSharedCheck_1266_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_a_1235_);
lean_dec(v___x_1234_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1266_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1239_; 
v___x_1239_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg(v_a_1235_, v_e_1228_);
lean_dec(v_a_1235_);
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_object* v___x_1240_; lean_object* v___f_1241_; lean_object* v___x_1242_; 
lean_del_object(v___x_1237_);
v___x_1240_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___closed__0));
lean_inc_ref(v_e_1228_);
v___f_1241_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___boxed), 8, 4);
lean_closure_set(v___f_1241_, 0, v___x_1240_);
lean_closure_set(v___f_1241_, 1, v_pre_1226_);
lean_closure_set(v___f_1241_, 2, v_e_1228_);
lean_closure_set(v___f_1241_, 3, v_post_1227_);
v___x_1242_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg(v___f_1241_, v_a_1229_, v___y_1230_, v___y_1231_);
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_object* v_a_1243_; lean_object* v___f_1244_; lean_object* v___x_1245_; 
v_a_1243_ = lean_ctor_get(v___x_1242_, 0);
lean_inc_n(v_a_1243_, 2);
lean_dec_ref_known(v___x_1242_, 1);
lean_inc(v_a_1229_);
v___f_1244_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1244_, 0, v_a_1229_);
lean_closure_set(v___f_1244_, 1, v_e_1228_);
lean_closure_set(v___f_1244_, 2, v_a_1243_);
v___x_1245_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(lean_box(0), v___f_1244_, v___y_1230_, v___y_1231_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1252_; 
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1252_ == 0)
{
lean_object* v_unused_1253_; 
v_unused_1253_ = lean_ctor_get(v___x_1245_, 0);
lean_dec(v_unused_1253_);
v___x_1247_ = v___x_1245_;
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
else
{
lean_dec(v___x_1245_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 0, v_a_1243_);
v___x_1250_ = v___x_1247_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_a_1243_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
else
{
lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1261_; 
lean_dec(v_a_1243_);
v_a_1254_ = lean_ctor_get(v___x_1245_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1256_ = v___x_1245_;
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_dec(v___x_1245_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1259_; 
if (v_isShared_1257_ == 0)
{
v___x_1259_ = v___x_1256_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_a_1254_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
}
else
{
lean_dec_ref(v_e_1228_);
return v___x_1242_;
}
}
else
{
lean_object* v_val_1262_; lean_object* v___x_1264_; 
lean_dec_ref(v_e_1228_);
lean_dec_ref(v_post_1227_);
lean_dec_ref(v_pre_1226_);
v_val_1262_ = lean_ctor_get(v___x_1239_, 0);
lean_inc(v_val_1262_);
lean_dec_ref_known(v___x_1239_, 1);
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 0, v_val_1262_);
v___x_1264_ = v___x_1237_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_val_1262_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
}
}
else
{
lean_object* v_a_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1274_; 
lean_dec_ref(v_e_1228_);
lean_dec_ref(v_post_1227_);
lean_dec_ref(v_pre_1226_);
v_a_1267_ = lean_ctor_get(v___x_1234_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1269_ = v___x_1234_;
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_a_1267_);
lean_dec(v___x_1234_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1272_; 
if (v_isShared_1270_ == 0)
{
v___x_1272_ = v___x_1269_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_a_1267_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(lean_object* v_pre_1275_, lean_object* v_post_1276_, lean_object* v_e_1277_, lean_object* v_a_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v___x_1282_; 
lean_inc_ref(v_post_1276_);
lean_inc(v___y_1280_);
lean_inc_ref(v___y_1279_);
lean_inc_ref(v_e_1277_);
v___x_1282_ = lean_apply_4(v_post_1276_, v_e_1277_, v___y_1279_, v___y_1280_, lean_box(0));
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1301_; 
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1285_ = v___x_1282_;
v_isShared_1286_ = v_isSharedCheck_1301_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1282_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1301_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
switch(lean_obj_tag(v_a_1283_))
{
case 0:
{
lean_object* v_e_1287_; lean_object* v___x_1289_; 
lean_dec_ref(v_e_1277_);
lean_dec_ref(v_post_1276_);
lean_dec_ref(v_pre_1275_);
v_e_1287_ = lean_ctor_get(v_a_1283_, 0);
lean_inc_ref(v_e_1287_);
lean_dec_ref_known(v_a_1283_, 1);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 0, v_e_1287_);
v___x_1289_ = v___x_1285_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_e_1287_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
case 1:
{
lean_object* v_e_1291_; lean_object* v___x_1292_; 
lean_del_object(v___x_1285_);
lean_dec_ref(v_e_1277_);
v_e_1291_ = lean_ctor_get(v_a_1283_, 0);
lean_inc_ref(v_e_1291_);
lean_dec_ref_known(v_a_1283_, 1);
v___x_1292_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1275_, v_post_1276_, v_e_1291_, v_a_1278_, v___y_1279_, v___y_1280_);
return v___x_1292_;
}
default: 
{
lean_object* v_e_x3f_1293_; 
lean_dec_ref(v_post_1276_);
lean_dec_ref(v_pre_1275_);
v_e_x3f_1293_ = lean_ctor_get(v_a_1283_, 0);
lean_inc(v_e_x3f_1293_);
lean_dec_ref_known(v_a_1283_, 1);
if (lean_obj_tag(v_e_x3f_1293_) == 0)
{
lean_object* v___x_1295_; 
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 0, v_e_1277_);
v___x_1295_ = v___x_1285_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_e_1277_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
else
{
lean_object* v_val_1297_; lean_object* v___x_1299_; 
lean_dec_ref(v_e_1277_);
v_val_1297_ = lean_ctor_get(v_e_x3f_1293_, 0);
lean_inc(v_val_1297_);
lean_dec_ref_known(v_e_x3f_1293_, 1);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 0, v_val_1297_);
v___x_1299_ = v___x_1285_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_val_1297_);
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
}
}
else
{
lean_object* v_a_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1309_; 
lean_dec_ref(v_e_1277_);
lean_dec_ref(v_post_1276_);
lean_dec_ref(v_pre_1275_);
v_a_1302_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1309_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1309_ == 0)
{
v___x_1304_ = v___x_1282_;
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_a_1302_);
lean_dec(v___x_1282_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v___x_1307_; 
if (v_isShared_1305_ == 0)
{
v___x_1307_ = v___x_1304_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v_a_1302_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
return v___x_1307_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_1310_, lean_object* v_post_1311_, lean_object* v_e_1312_, lean_object* v_a_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1310_, v_post_1311_, v_e_1312_, v_a_1313_, v___y_1314_, v___y_1315_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
lean_dec(v_a_1313_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_1318_, lean_object* v_post_1319_, lean_object* v_sz_1320_, lean_object* v_i_1321_, lean_object* v_bs_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
size_t v_sz_boxed_1327_; size_t v_i_boxed_1328_; lean_object* v_res_1329_; 
v_sz_boxed_1327_ = lean_unbox_usize(v_sz_1320_);
lean_dec(v_sz_1320_);
v_i_boxed_1328_ = lean_unbox_usize(v_i_1321_);
lean_dec(v_i_1321_);
v_res_1329_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1(v_pre_1318_, v_post_1319_, v_sz_boxed_1327_, v_i_boxed_1328_, v_bs_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec(v___y_1323_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_1330_, lean_object* v_post_1331_, lean_object* v_x_1332_, lean_object* v_x_1333_, lean_object* v_x_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
lean_object* v_res_1339_; 
v_res_1339_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4(v_pre_1330_, v_post_1331_, v_x_1332_, v_x_1333_, v_x_1334_, v___y_1335_, v___y_1336_, v___y_1337_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
lean_dec(v___y_1335_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___boxed(lean_object* v_pre_1340_, lean_object* v_post_1341_, lean_object* v_e_1342_, lean_object* v_a_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_){
_start:
{
lean_object* v_res_1347_; 
v_res_1347_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1340_, v_post_1341_, v_e_1342_, v_a_1343_, v___y_1344_, v___y_1345_);
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
lean_dec(v_a_1343_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(lean_object* v_00_u03b1_1348_, lean_object* v_x_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_){
_start:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; 
v___x_1353_ = lean_apply_1(v_x_1349_, lean_box(0));
v___x_1354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1354_, 0, v___x_1353_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1355_, lean_object* v_x_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(v_00_u03b1_1355_, v_x_1356_, v___y_1357_, v___y_1358_);
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
return v_res_1360_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1361_ = lean_box(0);
v___x_1362_ = lean_unsigned_to_nat(16u);
v___x_1363_ = lean_mk_array(v___x_1362_, v___x_1361_);
return v___x_1363_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; 
v___x_1364_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0, &l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0);
v___x_1365_ = lean_unsigned_to_nat(0u);
v___x_1366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1365_);
lean_ctor_set(v___x_1366_, 1, v___x_1364_);
return v___x_1366_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1367_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1, &l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1_once, _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1);
v___x_1368_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1368_, 0, lean_box(0));
lean_closure_set(v___x_1368_, 1, lean_box(0));
lean_closure_set(v___x_1368_, 2, v___x_1367_);
return v___x_1368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0(lean_object* v_input_1369_, lean_object* v_pre_1370_, lean_object* v_post_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_){
_start:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v_a_1377_; lean_object* v___x_1378_; 
v___x_1375_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2);
v___x_1376_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(lean_box(0), v___x_1375_, v___y_1372_, v___y_1373_);
v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
lean_inc(v_a_1377_);
lean_dec_ref(v___x_1376_);
v___x_1378_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1370_, v_post_1371_, v_input_1369_, v_a_1377_, v___y_1372_, v___y_1373_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v_a_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1388_; 
v_a_1379_ = lean_ctor_get(v___x_1378_, 0);
lean_inc(v_a_1379_);
lean_dec_ref_known(v___x_1378_, 1);
v___x_1380_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1380_, 0, lean_box(0));
lean_closure_set(v___x_1380_, 1, lean_box(0));
lean_closure_set(v___x_1380_, 2, v_a_1377_);
v___x_1381_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(lean_box(0), v___x_1380_, v___y_1372_, v___y_1373_);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1388_ == 0)
{
lean_object* v_unused_1389_; 
v_unused_1389_ = lean_ctor_get(v___x_1381_, 0);
lean_dec(v_unused_1389_);
v___x_1383_ = v___x_1381_;
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
else
{
lean_dec(v___x_1381_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1386_; 
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 0, v_a_1379_);
v___x_1386_ = v___x_1383_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_a_1379_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
}
else
{
lean_dec(v_a_1377_);
return v___x_1378_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___boxed(lean_object* v_input_1390_, lean_object* v_pre_1391_, lean_object* v_post_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0(v_input_1390_, v_pre_1391_, v_post_1392_, v___y_1393_, v___y_1394_);
lean_dec(v___y_1394_);
lean_dec_ref(v___y_1393_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(lean_object* v_e_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_){
_start:
{
lean_object* v___f_1403_; lean_object* v___f_1404_; lean_object* v___x_1405_; 
v___f_1403_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___closed__0));
v___f_1404_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___closed__1));
v___x_1405_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0(v_e_1399_, v___f_1403_, v___f_1404_, v_a_1400_, v_a_1401_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___boxed(lean_object* v_e_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_){
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(v_e_1406_, v_a_1407_, v_a_1408_);
lean_dec(v_a_1408_);
lean_dec_ref(v_a_1407_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1411_, lean_object* v_m_1412_, lean_object* v_a_1413_){
_start:
{
lean_object* v___x_1414_; 
v___x_1414_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg(v_m_1412_, v_a_1413_);
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1415_, lean_object* v_m_1416_, lean_object* v_a_1417_){
_start:
{
lean_object* v_res_1418_; 
v_res_1418_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3(v_00_u03b2_1415_, v_m_1416_, v_a_1417_);
lean_dec_ref(v_a_1417_);
lean_dec_ref(v_m_1416_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_1419_, lean_object* v_ref_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_){
_start:
{
lean_object* v___x_1424_; 
v___x_1424_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1420_);
return v___x_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1425_, lean_object* v_ref_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
lean_object* v_res_1430_; 
v_res_1430_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_1425_, v_ref_1426_, v___y_1427_, v___y_1428_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8(lean_object* v_00_u03b1_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_){
_start:
{
lean_object* v___x_1435_; 
v___x_1435_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg();
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_){
_start:
{
lean_object* v_res_1440_; 
v_res_1440_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8(v_00_u03b1_1436_, v___y_1437_, v___y_1438_);
lean_dec(v___y_1438_);
lean_dec_ref(v___y_1437_);
return v_res_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_1441_, lean_object* v_x_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
lean_object* v___x_1447_; 
v___x_1447_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg(v_x_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_1448_, lean_object* v_x_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_){
_start:
{
lean_object* v_res_1454_; 
v_res_1454_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5(v_00_u03b1_1448_, v_x_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
lean_dec(v___y_1452_);
lean_dec_ref(v___y_1451_);
lean_dec(v___y_1450_);
return v_res_1454_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_1455_, lean_object* v_m_1456_, lean_object* v_a_1457_, lean_object* v_b_1458_){
_start:
{
lean_object* v___x_1459_; 
v___x_1459_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6___redArg(v_m_1456_, v_a_1457_, v_b_1458_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_1460_, lean_object* v_a_1461_, lean_object* v_x_1462_){
_start:
{
lean_object* v___x_1463_; 
v___x_1463_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1461_, v_x_1462_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1464_, lean_object* v_a_1465_, lean_object* v_x_1466_){
_start:
{
lean_object* v_res_1467_; 
v_res_1467_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_1464_, v_a_1465_, v_x_1466_);
lean_dec(v_x_1466_);
lean_dec_ref(v_a_1465_);
return v_res_1467_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_1468_, lean_object* v_a_1469_, lean_object* v_x_1470_){
_start:
{
uint8_t v___x_1471_; 
v___x_1471_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1469_, v_x_1470_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___boxed(lean_object* v_00_u03b2_1472_, lean_object* v_a_1473_, lean_object* v_x_1474_){
_start:
{
uint8_t v_res_1475_; lean_object* v_r_1476_; 
v_res_1475_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10(v_00_u03b2_1472_, v_a_1473_, v_x_1474_);
lean_dec(v_x_1474_);
lean_dec_ref(v_a_1473_);
v_r_1476_ = lean_box(v_res_1475_);
return v_r_1476_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_1477_, lean_object* v_data_1478_){
_start:
{
lean_object* v___x_1479_; 
v___x_1479_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11___redArg(v_data_1478_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12(lean_object* v_00_u03b2_1480_, lean_object* v_a_1481_, lean_object* v_b_1482_, lean_object* v_x_1483_){
_start:
{
lean_object* v___x_1484_; 
v___x_1484_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1481_, v_b_1482_, v_x_1483_);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12(lean_object* v_00_u03b2_1485_, lean_object* v_i_1486_, lean_object* v_source_1487_, lean_object* v_target_1488_){
_start:
{
lean_object* v___x_1489_; 
v___x_1489_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v_i_1486_, v_source_1487_, v_target_1488_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_1490_, lean_object* v_x_1491_, lean_object* v_x_1492_){
_start:
{
lean_object* v___x_1493_; 
v___x_1493_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_x_1491_, v_x_1492_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(lean_object* v_declName_1494_, lean_object* v___y_1495_){
_start:
{
lean_object* v___x_1497_; lean_object* v_env_1498_; uint8_t v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1497_ = lean_st_ref_get(v___y_1495_);
v_env_1498_ = lean_ctor_get(v___x_1497_, 0);
lean_inc_ref(v_env_1498_);
lean_dec(v___x_1497_);
v___x_1499_ = l_Lean_isRecCore(v_env_1498_, v_declName_1494_);
v___x_1500_ = lean_box(v___x_1499_);
v___x_1501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1501_, 0, v___x_1500_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg___boxed(lean_object* v_declName_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(v_declName_1502_, v___y_1503_);
lean_dec(v___y_1503_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2(lean_object* v_declName_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
lean_object* v___x_1512_; 
v___x_1512_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(v_declName_1506_, v___y_1510_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___boxed(lean_object* v_declName_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2(v_declName_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(lean_object* v_declName_1520_, lean_object* v___y_1521_){
_start:
{
lean_object* v___x_1523_; lean_object* v_env_1524_; uint8_t v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1523_ = lean_st_ref_get(v___y_1521_);
v_env_1524_ = lean_ctor_get(v___x_1523_, 0);
lean_inc_ref(v_env_1524_);
lean_dec(v___x_1523_);
v___x_1525_ = l_Lean_getReducibilityStatusCore(v_env_1524_, v_declName_1520_);
v___x_1526_ = lean_box(v___x_1525_);
v___x_1527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1526_);
return v___x_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg___boxed(lean_object* v_declName_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(v_declName_1528_, v___y_1529_);
lean_dec(v___y_1529_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0(lean_object* v_declName_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_){
_start:
{
lean_object* v___x_1538_; lean_object* v_a_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1554_; 
v___x_1538_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(v_declName_1532_, v___y_1536_);
v_a_1539_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1541_ = v___x_1538_;
v_isShared_1542_ = v_isSharedCheck_1554_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_a_1539_);
lean_dec(v___x_1538_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1554_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
uint8_t v___x_1543_; 
v___x_1543_ = lean_unbox(v_a_1539_);
lean_dec(v_a_1539_);
if (v___x_1543_ == 0)
{
uint8_t v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1547_; 
v___x_1544_ = 1;
v___x_1545_ = lean_box(v___x_1544_);
if (v_isShared_1542_ == 0)
{
lean_ctor_set(v___x_1541_, 0, v___x_1545_);
v___x_1547_ = v___x_1541_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v___x_1545_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
return v___x_1547_;
}
}
else
{
uint8_t v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1552_; 
v___x_1549_ = 0;
v___x_1550_ = lean_box(v___x_1549_);
if (v_isShared_1542_ == 0)
{
lean_ctor_set(v___x_1541_, 0, v___x_1550_);
v___x_1552_ = v___x_1541_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v___x_1550_);
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
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0___boxed(lean_object* v_declName_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_){
_start:
{
lean_object* v_res_1561_; 
v_res_1561_ = l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0(v_declName_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
lean_dec(v___y_1557_);
lean_dec_ref(v___y_1556_);
return v_res_1561_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(lean_object* v_a_1562_, lean_object* v_b_1563_){
_start:
{
lean_object* v_array_1565_; lean_object* v_start_1566_; lean_object* v_stop_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1584_; 
v_array_1565_ = lean_ctor_get(v_a_1562_, 0);
v_start_1566_ = lean_ctor_get(v_a_1562_, 1);
v_stop_1567_ = lean_ctor_get(v_a_1562_, 2);
v_isSharedCheck_1584_ = !lean_is_exclusive(v_a_1562_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1569_ = v_a_1562_;
v_isShared_1570_ = v_isSharedCheck_1584_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_stop_1567_);
lean_inc(v_start_1566_);
lean_inc(v_array_1565_);
lean_dec(v_a_1562_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1584_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
uint8_t v___x_1571_; 
v___x_1571_ = lean_nat_dec_lt(v_start_1566_, v_stop_1567_);
if (v___x_1571_ == 0)
{
lean_object* v___x_1572_; 
lean_del_object(v___x_1569_);
lean_dec(v_stop_1567_);
lean_dec(v_start_1566_);
lean_dec_ref(v_array_1565_);
v___x_1572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1572_, 0, v_b_1563_);
return v___x_1572_;
}
else
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1577_; 
v___x_1573_ = lean_box(0);
v___x_1574_ = lean_unsigned_to_nat(1u);
v___x_1575_ = lean_nat_add(v_start_1566_, v___x_1574_);
lean_inc_ref(v_array_1565_);
if (v_isShared_1570_ == 0)
{
lean_ctor_set(v___x_1569_, 1, v___x_1575_);
v___x_1577_ = v___x_1569_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_array_1565_);
lean_ctor_set(v_reuseFailAlloc_1583_, 1, v___x_1575_);
lean_ctor_set(v_reuseFailAlloc_1583_, 2, v_stop_1567_);
v___x_1577_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
lean_object* v___x_1578_; uint8_t v___x_1579_; 
v___x_1578_ = lean_array_fget(v_array_1565_, v_start_1566_);
lean_dec(v_start_1566_);
lean_dec_ref(v_array_1565_);
v___x_1579_ = l_Lean_Expr_hasExprMVar(v___x_1578_);
lean_dec(v___x_1578_);
if (v___x_1579_ == 0)
{
v_a_1562_ = v___x_1577_;
v_b_1563_ = v___x_1573_;
goto _start;
}
else
{
lean_object* v___x_1581_; 
v___x_1581_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_dec_ref_known(v___x_1581_, 1);
v_a_1562_ = v___x_1577_;
v_b_1563_ = v___x_1573_;
goto _start;
}
else
{
lean_dec_ref(v___x_1577_);
return v___x_1581_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg___boxed(lean_object* v_a_1585_, lean_object* v_b_1586_, lean_object* v___y_1587_){
_start:
{
lean_object* v_res_1588_; 
v_res_1588_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(v_a_1585_, v_b_1586_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(lean_object* v_e_1597_, uint8_t v_isMatch_1598_, uint8_t v_root_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_){
_start:
{
lean_object* v___y_1606_; lean_object* v_b_1607_; lean_object* v___x_1618_; 
v___x_1618_ = l_Lean_Meta_DiscrTree_reduceDT(v_e_1597_, v_root_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_);
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1781_; 
v_a_1619_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1781_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1621_ = v___x_1618_;
v_isShared_1622_ = v_isSharedCheck_1781_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1618_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1781_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___y_1624_; lean_object* v___y_1634_; lean_object* v___y_1635_; lean_object* v___y_1636_; lean_object* v___y_1637_; 
if (v_root_1599_ == 0)
{
lean_object* v___x_1769_; 
lean_inc(v_a_1619_);
v___x_1769_ = l_Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f(v_a_1619_);
if (lean_obj_tag(v___x_1769_) == 1)
{
lean_object* v_val_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1780_; 
lean_del_object(v___x_1621_);
lean_dec(v_a_1619_);
v_val_1770_ = lean_ctor_get(v___x_1769_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1772_ = v___x_1769_;
v_isShared_1773_ = v_isSharedCheck_1780_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_val_1770_);
lean_dec(v___x_1769_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1780_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1775_; 
if (v_isShared_1773_ == 0)
{
lean_ctor_set_tag(v___x_1772_, 2);
v___x_1775_ = v___x_1772_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_val_1770_);
v___x_1775_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1776_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
v___x_1777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1775_);
lean_ctor_set(v___x_1777_, 1, v___x_1776_);
v___x_1778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1778_, 0, v___x_1777_);
return v___x_1778_;
}
}
}
else
{
lean_dec(v___x_1769_);
v___y_1634_ = v_a_1600_;
v___y_1635_ = v_a_1601_;
v___y_1636_ = v_a_1602_;
v___y_1637_ = v_a_1603_;
goto v___jp_1633_;
}
}
else
{
v___y_1634_ = v_a_1600_;
v___y_1635_ = v_a_1601_;
v___y_1636_ = v_a_1602_;
v___y_1637_ = v_a_1603_;
goto v___jp_1633_;
}
v___jp_1623_:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1631_; 
v___x_1625_ = l_Lean_Expr_getAppNumArgs(v_a_1619_);
lean_inc(v___x_1625_);
v___x_1626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1626_, 0, v___y_1624_);
lean_ctor_set(v___x_1626_, 1, v___x_1625_);
v___x_1627_ = lean_mk_empty_array_with_capacity(v___x_1625_);
lean_dec(v___x_1625_);
v___x_1628_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1619_, v___x_1627_);
v___x_1629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1626_);
lean_ctor_set(v___x_1629_, 1, v___x_1628_);
if (v_isShared_1622_ == 0)
{
lean_ctor_set(v___x_1621_, 0, v___x_1629_);
v___x_1631_ = v___x_1621_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v___x_1629_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
v___jp_1633_:
{
lean_object* v___x_1638_; 
v___x_1638_ = l_Lean_Expr_getAppFn(v_a_1619_);
switch(lean_obj_tag(v___x_1638_))
{
case 1:
{
lean_object* v_fvarId_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; 
lean_del_object(v___x_1621_);
v_fvarId_1639_ = lean_ctor_get(v___x_1638_, 0);
lean_inc(v_fvarId_1639_);
lean_dec_ref_known(v___x_1638_, 1);
v___x_1640_ = l_Lean_Expr_getAppNumArgs(v_a_1619_);
lean_inc(v___x_1640_);
v___x_1641_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1641_, 0, v_fvarId_1639_);
lean_ctor_set(v___x_1641_, 1, v___x_1640_);
v___x_1642_ = lean_mk_empty_array_with_capacity(v___x_1640_);
lean_dec(v___x_1640_);
v___x_1643_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1619_, v___x_1642_);
v___x_1644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1641_);
lean_ctor_set(v___x_1644_, 1, v___x_1643_);
v___x_1645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1644_);
return v___x_1645_;
}
case 2:
{
lean_del_object(v___x_1621_);
lean_dec(v_a_1619_);
if (v_isMatch_1598_ == 0)
{
lean_object* v_mvarId_1646_; lean_object* v___x_1647_; uint8_t v_isDefEqStuckEx_1648_; 
v_mvarId_1646_ = lean_ctor_get(v___x_1638_, 0);
lean_inc(v_mvarId_1646_);
lean_dec_ref_known(v___x_1638_, 1);
v___x_1647_ = l_Lean_Meta_Context_config(v___y_1634_);
v_isDefEqStuckEx_1648_ = lean_ctor_get_uint8(v___x_1647_, 4);
lean_dec_ref(v___x_1647_);
if (v_isDefEqStuckEx_1648_ == 0)
{
lean_object* v___x_1649_; 
v___x_1649_ = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(v_mvarId_1646_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_);
if (lean_obj_tag(v___x_1649_) == 0)
{
lean_object* v_a_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1663_; 
v_a_1650_ = lean_ctor_get(v___x_1649_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1649_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1652_ = v___x_1649_;
v_isShared_1653_ = v_isSharedCheck_1663_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_a_1650_);
lean_dec(v___x_1649_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1663_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
uint8_t v___x_1654_; 
v___x_1654_ = lean_unbox(v_a_1650_);
lean_dec(v_a_1650_);
if (v___x_1654_ == 0)
{
lean_object* v___x_1655_; lean_object* v___x_1657_; 
v___x_1655_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__2));
if (v_isShared_1653_ == 0)
{
lean_ctor_set(v___x_1652_, 0, v___x_1655_);
v___x_1657_ = v___x_1652_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v___x_1655_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
else
{
lean_object* v___x_1659_; lean_object* v___x_1661_; 
v___x_1659_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
if (v_isShared_1653_ == 0)
{
lean_ctor_set(v___x_1652_, 0, v___x_1659_);
v___x_1661_ = v___x_1652_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v___x_1659_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
}
else
{
lean_object* v_a_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1671_; 
v_a_1664_ = lean_ctor_get(v___x_1649_, 0);
v_isSharedCheck_1671_ = !lean_is_exclusive(v___x_1649_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1666_ = v___x_1649_;
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_a_1664_);
lean_dec(v___x_1649_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1669_; 
if (v_isShared_1667_ == 0)
{
v___x_1669_ = v___x_1666_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_a_1664_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
}
}
else
{
lean_object* v___x_1672_; lean_object* v___x_1673_; 
lean_dec(v_mvarId_1646_);
v___x_1672_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__2));
v___x_1673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1672_);
return v___x_1673_;
}
}
else
{
lean_object* v___x_1674_; lean_object* v___x_1675_; 
lean_dec_ref_known(v___x_1638_, 1);
v___x_1674_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
v___x_1675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1674_);
return v___x_1675_;
}
}
case 4:
{
lean_object* v_declName_1676_; lean_object* v___x_1677_; uint8_t v_isDefEqStuckEx_1678_; 
v_declName_1676_ = lean_ctor_get(v___x_1638_, 0);
lean_inc(v_declName_1676_);
lean_dec_ref_known(v___x_1638_, 2);
v___x_1677_ = l_Lean_Meta_Context_config(v___y_1634_);
v_isDefEqStuckEx_1678_ = lean_ctor_get_uint8(v___x_1677_, 4);
lean_dec_ref(v___x_1677_);
if (v_isDefEqStuckEx_1678_ == 0)
{
v___y_1624_ = v_declName_1676_;
goto v___jp_1623_;
}
else
{
uint8_t v___x_1679_; 
v___x_1679_ = l_Lean_Expr_hasExprMVar(v_a_1619_);
if (v___x_1679_ == 0)
{
v___y_1624_ = v_declName_1676_;
goto v___jp_1623_;
}
else
{
lean_object* v___x_1680_; 
lean_inc(v_declName_1676_);
v___x_1680_ = l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0(v_declName_1676_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_);
if (lean_obj_tag(v___x_1680_) == 0)
{
lean_object* v_a_1681_; uint8_t v___x_1682_; 
v_a_1681_ = lean_ctor_get(v___x_1680_, 0);
lean_inc(v_a_1681_);
lean_dec_ref_known(v___x_1680_, 1);
v___x_1682_ = lean_unbox(v_a_1681_);
lean_dec(v_a_1681_);
if (v___x_1682_ == 0)
{
lean_object* v___x_1683_; lean_object* v_env_1684_; lean_object* v___x_1685_; 
v___x_1683_ = lean_st_ref_get(v___y_1637_);
v_env_1684_ = lean_ctor_get(v___x_1683_, 0);
lean_inc_ref(v_env_1684_);
lean_dec(v___x_1683_);
v___x_1685_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_1684_, v_a_1619_);
if (lean_obj_tag(v___x_1685_) == 1)
{
lean_object* v_val_1686_; lean_object* v_numDiscrs_1687_; lean_object* v_nargs_1688_; lean_object* v_dummy_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
v_val_1686_ = lean_ctor_get(v___x_1685_, 0);
lean_inc(v_val_1686_);
lean_dec_ref_known(v___x_1685_, 1);
v_numDiscrs_1687_ = lean_ctor_get(v_val_1686_, 1);
lean_inc(v_numDiscrs_1687_);
v_nargs_1688_ = l_Lean_Expr_getAppNumArgs(v_a_1619_);
v_dummy_1689_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0);
lean_inc(v_nargs_1688_);
v___x_1690_ = lean_mk_array(v_nargs_1688_, v_dummy_1689_);
v___x_1691_ = lean_unsigned_to_nat(1u);
v___x_1692_ = lean_nat_sub(v_nargs_1688_, v___x_1691_);
lean_dec(v_nargs_1688_);
lean_inc(v_a_1619_);
v___x_1693_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1619_, v___x_1690_, v___x_1692_);
v___x_1694_ = l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(v_val_1686_);
lean_dec(v_val_1686_);
v___x_1695_ = lean_nat_add(v___x_1694_, v_numDiscrs_1687_);
lean_dec(v_numDiscrs_1687_);
v___x_1696_ = l_Array_toSubarray___redArg(v___x_1693_, v___x_1694_, v___x_1695_);
v___x_1697_ = lean_box(0);
v___x_1698_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(v___x_1696_, v___x_1697_);
if (lean_obj_tag(v___x_1698_) == 0)
{
lean_dec_ref_known(v___x_1698_, 1);
v___y_1624_ = v_declName_1676_;
goto v___jp_1623_;
}
else
{
lean_object* v_a_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1706_; 
lean_dec(v_declName_1676_);
lean_del_object(v___x_1621_);
lean_dec(v_a_1619_);
v_a_1699_ = lean_ctor_get(v___x_1698_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1701_ = v___x_1698_;
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_a_1699_);
lean_dec(v___x_1698_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1704_; 
if (v_isShared_1702_ == 0)
{
v___x_1704_ = v___x_1701_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_a_1699_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
}
}
else
{
lean_object* v___x_1707_; lean_object* v_a_1708_; uint8_t v___x_1709_; 
lean_dec(v___x_1685_);
lean_inc(v_declName_1676_);
v___x_1707_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(v_declName_1676_, v___y_1637_);
v_a_1708_ = lean_ctor_get(v___x_1707_, 0);
lean_inc(v_a_1708_);
lean_dec_ref(v___x_1707_);
v___x_1709_ = lean_unbox(v_a_1708_);
lean_dec(v_a_1708_);
if (v___x_1709_ == 0)
{
v___y_1624_ = v_declName_1676_;
goto v___jp_1623_;
}
else
{
lean_object* v___x_1710_; 
v___x_1710_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1710_) == 0)
{
lean_dec_ref_known(v___x_1710_, 1);
v___y_1624_ = v_declName_1676_;
goto v___jp_1623_;
}
else
{
lean_object* v_a_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1718_; 
lean_dec(v_declName_1676_);
lean_del_object(v___x_1621_);
lean_dec(v_a_1619_);
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
}
}
else
{
lean_object* v___x_1719_; 
v___x_1719_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1719_) == 0)
{
lean_dec_ref_known(v___x_1719_, 1);
v___y_1624_ = v_declName_1676_;
goto v___jp_1623_;
}
else
{
lean_object* v_a_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1727_; 
lean_dec(v_declName_1676_);
lean_del_object(v___x_1621_);
lean_dec(v_a_1619_);
v_a_1720_ = lean_ctor_get(v___x_1719_, 0);
v_isSharedCheck_1727_ = !lean_is_exclusive(v___x_1719_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1722_ = v___x_1719_;
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_a_1720_);
lean_dec(v___x_1719_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v___x_1725_; 
if (v_isShared_1723_ == 0)
{
v___x_1725_ = v___x_1722_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_a_1720_);
v___x_1725_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
return v___x_1725_;
}
}
}
}
}
else
{
lean_object* v_a_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1735_; 
lean_dec(v_declName_1676_);
lean_del_object(v___x_1621_);
lean_dec(v_a_1619_);
v_a_1728_ = lean_ctor_get(v___x_1680_, 0);
v_isSharedCheck_1735_ = !lean_is_exclusive(v___x_1680_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1730_ = v___x_1680_;
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_a_1728_);
lean_dec(v___x_1680_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1733_; 
if (v_isShared_1731_ == 0)
{
v___x_1733_ = v___x_1730_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_a_1728_);
v___x_1733_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
return v___x_1733_;
}
}
}
}
}
}
case 7:
{
lean_object* v_binderType_1736_; lean_object* v_body_1737_; uint8_t v___x_1738_; 
lean_del_object(v___x_1621_);
lean_dec(v_a_1619_);
v_binderType_1736_ = lean_ctor_get(v___x_1638_, 1);
lean_inc_ref(v_binderType_1736_);
v_body_1737_ = lean_ctor_get(v___x_1638_, 2);
lean_inc_ref(v_body_1737_);
lean_dec_ref_known(v___x_1638_, 3);
v___x_1738_ = l_Lean_Expr_hasLooseBVars(v_body_1737_);
if (v___x_1738_ == 0)
{
v___y_1606_ = v_binderType_1736_;
v_b_1607_ = v_body_1737_;
goto v___jp_1605_;
}
else
{
lean_object* v___x_1739_; 
v___x_1739_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(v_body_1737_, v___y_1636_, v___y_1637_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_object* v_a_1740_; 
v_a_1740_ = lean_ctor_get(v___x_1739_, 0);
lean_inc(v_a_1740_);
lean_dec_ref_known(v___x_1739_, 1);
v___y_1606_ = v_binderType_1736_;
v_b_1607_ = v_a_1740_;
goto v___jp_1605_;
}
else
{
lean_object* v_a_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1748_; 
lean_dec_ref(v_binderType_1736_);
v_a_1741_ = lean_ctor_get(v___x_1739_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1743_ = v___x_1739_;
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_a_1741_);
lean_dec(v___x_1739_);
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
}
case 9:
{
lean_object* v_a_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
lean_del_object(v___x_1621_);
lean_dec(v_a_1619_);
v_a_1749_ = lean_ctor_get(v___x_1638_, 0);
lean_inc_ref(v_a_1749_);
lean_dec_ref_known(v___x_1638_, 1);
v___x_1750_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1750_, 0, v_a_1749_);
v___x_1751_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
v___x_1752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1752_, 0, v___x_1750_);
lean_ctor_set(v___x_1752_, 1, v___x_1751_);
v___x_1753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1752_);
return v___x_1753_;
}
case 11:
{
lean_object* v_typeName_1754_; lean_object* v_idx_1755_; lean_object* v_struct_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
lean_del_object(v___x_1621_);
v_typeName_1754_ = lean_ctor_get(v___x_1638_, 0);
lean_inc(v_typeName_1754_);
v_idx_1755_ = lean_ctor_get(v___x_1638_, 1);
lean_inc(v_idx_1755_);
v_struct_1756_ = lean_ctor_get(v___x_1638_, 2);
lean_inc_ref(v_struct_1756_);
lean_dec_ref_known(v___x_1638_, 3);
v___x_1757_ = l_Lean_Expr_getAppNumArgs(v_a_1619_);
lean_inc(v___x_1757_);
v___x_1758_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_1758_, 0, v_typeName_1754_);
lean_ctor_set(v___x_1758_, 1, v_idx_1755_);
lean_ctor_set(v___x_1758_, 2, v___x_1757_);
v___x_1759_ = lean_unsigned_to_nat(1u);
v___x_1760_ = lean_mk_empty_array_with_capacity(v___x_1759_);
v___x_1761_ = lean_array_push(v___x_1760_, v_struct_1756_);
v___x_1762_ = lean_mk_empty_array_with_capacity(v___x_1757_);
lean_dec(v___x_1757_);
v___x_1763_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1619_, v___x_1762_);
v___x_1764_ = l_Array_append___redArg(v___x_1761_, v___x_1763_);
lean_dec_ref(v___x_1763_);
v___x_1765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1758_);
lean_ctor_set(v___x_1765_, 1, v___x_1764_);
v___x_1766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1766_, 0, v___x_1765_);
return v___x_1766_;
}
default: 
{
lean_object* v___x_1767_; lean_object* v___x_1768_; 
lean_dec_ref(v___x_1638_);
lean_del_object(v___x_1621_);
lean_dec(v_a_1619_);
v___x_1767_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
v___x_1768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1767_);
return v___x_1768_;
}
}
}
}
}
else
{
lean_object* v_a_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1789_; 
v_a_1782_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1784_ = v___x_1618_;
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_a_1782_);
lean_dec(v___x_1618_);
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
v___jp_1605_:
{
uint8_t v___x_1608_; 
v___x_1608_ = l_Lean_Expr_hasLooseBVars(v_b_1607_);
if (v___x_1608_ == 0)
{
lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1609_ = lean_box(5);
v___x_1610_ = lean_unsigned_to_nat(2u);
v___x_1611_ = lean_mk_empty_array_with_capacity(v___x_1610_);
v___x_1612_ = lean_array_push(v___x_1611_, v___y_1606_);
v___x_1613_ = lean_array_push(v___x_1612_, v_b_1607_);
v___x_1614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1609_);
lean_ctor_set(v___x_1614_, 1, v___x_1613_);
v___x_1615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1614_);
return v___x_1615_;
}
else
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
lean_dec_ref(v_b_1607_);
lean_dec_ref(v___y_1606_);
v___x_1616_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
v___x_1617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1616_);
return v___x_1617_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___boxed(lean_object* v_e_1790_, lean_object* v_isMatch_1791_, lean_object* v_root_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_){
_start:
{
uint8_t v_isMatch_boxed_1798_; uint8_t v_root_boxed_1799_; lean_object* v_res_1800_; 
v_isMatch_boxed_1798_ = lean_unbox(v_isMatch_1791_);
v_root_boxed_1799_ = lean_unbox(v_root_1792_);
v_res_1800_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_1790_, v_isMatch_boxed_1798_, v_root_boxed_1799_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_);
lean_dec(v_a_1796_);
lean_dec_ref(v_a_1795_);
lean_dec(v_a_1794_);
lean_dec_ref(v_a_1793_);
return v_res_1800_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0(lean_object* v_declName_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_){
_start:
{
lean_object* v___x_1807_; 
v___x_1807_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(v_declName_1801_, v___y_1805_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___boxed(lean_object* v_declName_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_){
_start:
{
lean_object* v_res_1814_; 
v_res_1814_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0(v_declName_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1(lean_object* v_inst_1815_, lean_object* v_R_1816_, lean_object* v_a_1817_, lean_object* v_b_1818_, lean_object* v_c_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_){
_start:
{
lean_object* v___x_1825_; 
v___x_1825_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(v_a_1817_, v_b_1818_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___boxed(lean_object* v_inst_1826_, lean_object* v_R_1827_, lean_object* v_a_1828_, lean_object* v_b_1829_, lean_object* v_c_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_){
_start:
{
lean_object* v_res_1836_; 
v_res_1836_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1(v_inst_1826_, v_R_1827_, v_a_1828_, v_b_1829_, v_c_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
return v_res_1836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getMatchKeyArgs(lean_object* v_e_1837_, uint8_t v_root_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_){
_start:
{
uint8_t v___x_1844_; lean_object* v___x_1845_; 
v___x_1844_ = 1;
v___x_1845_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_1837_, v___x_1844_, v_root_1838_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getMatchKeyArgs___boxed(lean_object* v_e_1846_, lean_object* v_root_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_){
_start:
{
uint8_t v_root_boxed_1853_; lean_object* v_res_1854_; 
v_root_boxed_1853_ = lean_unbox(v_root_1847_);
v_res_1854_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getMatchKeyArgs(v_e_1846_, v_root_boxed_1853_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_);
lean_dec(v_a_1851_);
lean_dec_ref(v_a_1850_);
lean_dec(v_a_1849_);
lean_dec_ref(v_a_1848_);
return v_res_1854_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__1(void){
_start:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; 
v___x_1857_ = lean_box(0);
v___x_1858_ = lean_unsigned_to_nat(16u);
v___x_1859_ = lean_mk_array(v___x_1858_, v___x_1857_);
return v___x_1859_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2(void){
_start:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___x_1860_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__1);
v___x_1861_ = lean_unsigned_to_nat(0u);
v___x_1862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1861_);
lean_ctor_set(v___x_1862_, 1, v___x_1860_);
return v___x_1862_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__4(void){
_start:
{
lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1865_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__3));
v___x_1866_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2);
v___x_1867_ = lean_unsigned_to_nat(0u);
v___x_1868_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__0));
v___x_1869_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1868_);
lean_ctor_set(v___x_1869_, 1, v___x_1867_);
lean_ctor_set(v___x_1869_, 2, v___x_1866_);
lean_ctor_set(v___x_1869_, 3, v___x_1865_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg(){
_start:
{
lean_object* v___x_1871_; 
v___x_1871_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__4);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___boxed(lean_object* v___dummy_1872_){
_start:
{
lean_object* v_res_1873_; 
v_res_1873_ = l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg();
return v_res_1873_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0(void){
_start:
{
lean_object* v___x_1874_; 
v___x_1874_ = l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg();
return v___x_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default(lean_object* v_00_u03b1_1875_){
_start:
{
lean_object* v___x_1876_; 
v___x_1876_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___redArg(){
_start:
{
lean_object* v___x_1878_; 
v___x_1878_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___redArg___boxed(lean_object* v___dummy_1879_){
_start:
{
lean_object* v_res_1880_; 
v_res_1880_ = l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___redArg();
return v_res_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie(lean_object* v_a_1881_){
_start:
{
lean_object* v___x_1882_; 
v___x_1882_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0);
return v___x_1882_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__1(void){
_start:
{
lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1885_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2);
v___x_1886_ = lean_unsigned_to_nat(0u);
v___x_1887_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___x_1888_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1887_);
lean_ctor_set(v___x_1888_, 1, v___x_1886_);
lean_ctor_set(v___x_1888_, 2, v___x_1885_);
lean_ctor_set(v___x_1888_, 3, v___x_1887_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg(){
_start:
{
lean_object* v___x_1890_; 
v___x_1890_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__1);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___boxed(lean_object* v___dummy_1891_){
_start:
{
lean_object* v_res_1892_; 
v_res_1892_ = l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg();
return v_res_1892_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0(void){
_start:
{
lean_object* v___x_1893_; 
v___x_1893_ = l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg();
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie(lean_object* v_00_u03b1_1894_){
_start:
{
lean_object* v___x_1895_; 
v___x_1895_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0, &l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0);
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Trie_pushPending___redArg(lean_object* v_x_1896_, lean_object* v_x_1897_){
_start:
{
lean_object* v_values_1898_; lean_object* v_star_1899_; lean_object* v_children_1900_; lean_object* v_pending_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1909_; 
v_values_1898_ = lean_ctor_get(v_x_1896_, 0);
v_star_1899_ = lean_ctor_get(v_x_1896_, 1);
v_children_1900_ = lean_ctor_get(v_x_1896_, 2);
v_pending_1901_ = lean_ctor_get(v_x_1896_, 3);
v_isSharedCheck_1909_ = !lean_is_exclusive(v_x_1896_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1903_ = v_x_1896_;
v_isShared_1904_ = v_isSharedCheck_1909_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_pending_1901_);
lean_inc(v_children_1900_);
lean_inc(v_star_1899_);
lean_inc(v_values_1898_);
lean_dec(v_x_1896_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1909_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1905_; lean_object* v___x_1907_; 
v___x_1905_ = lean_array_push(v_pending_1901_, v_x_1897_);
if (v_isShared_1904_ == 0)
{
lean_ctor_set(v___x_1903_, 3, v___x_1905_);
v___x_1907_ = v___x_1903_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_values_1898_);
lean_ctor_set(v_reuseFailAlloc_1908_, 1, v_star_1899_);
lean_ctor_set(v_reuseFailAlloc_1908_, 2, v_children_1900_);
lean_ctor_set(v_reuseFailAlloc_1908_, 3, v___x_1905_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Trie_pushPending(lean_object* v_00_u03b1_1910_, lean_object* v_x_1911_, lean_object* v_x_1912_){
_start:
{
lean_object* v___x_1913_; 
v___x_1913_ = l_Lean_Meta_LazyDiscrTree_Trie_pushPending___redArg(v_x_1911_, v_x_1912_);
return v___x_1913_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__0(void){
_start:
{
lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1914_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0);
v___x_1915_ = lean_unsigned_to_nat(1u);
v___x_1916_ = lean_mk_empty_array_with_capacity(v___x_1915_);
v___x_1917_ = lean_array_push(v___x_1916_, v___x_1914_);
return v___x_1917_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__1(void){
_start:
{
lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1918_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2);
v___x_1919_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__0);
v___x_1920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1919_);
lean_ctor_set(v___x_1920_, 1, v___x_1918_);
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabited___redArg(){
_start:
{
lean_object* v___x_1922_; 
v___x_1922_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__1);
return v___x_1922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___boxed(lean_object* v___dummy_1923_){
_start:
{
lean_object* v_res_1924_; 
v_res_1924_ = l_Lean_Meta_LazyDiscrTree_instInhabited___redArg();
return v_res_1924_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_1925_; 
v___x_1925_ = l_Lean_Meta_LazyDiscrTree_instInhabited___redArg();
return v___x_1925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabited(lean_object* v_00_u03b1_1926_){
_start:
{
lean_object* v___x_1927_; 
v___x_1927_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0);
return v___x_1927_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(lean_object* v_msgData_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_){
_start:
{
lean_object* v___x_1934_; lean_object* v_env_1935_; lean_object* v___x_1936_; lean_object* v_toCold_1937_; lean_object* v_mctx_1938_; lean_object* v_lctx_1939_; lean_object* v_options_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; 
v___x_1934_ = lean_st_ref_get(v___y_1932_);
v_env_1935_ = lean_ctor_get(v___x_1934_, 0);
lean_inc_ref(v_env_1935_);
lean_dec(v___x_1934_);
v___x_1936_ = lean_st_ref_get(v___y_1930_);
v_toCold_1937_ = lean_ctor_get(v___y_1931_, 0);
v_mctx_1938_ = lean_ctor_get(v___x_1936_, 0);
lean_inc_ref(v_mctx_1938_);
lean_dec(v___x_1936_);
v_lctx_1939_ = lean_ctor_get(v___y_1929_, 2);
v_options_1940_ = lean_ctor_get(v_toCold_1937_, 2);
lean_inc_ref(v_options_1940_);
lean_inc_ref(v_lctx_1939_);
v___x_1941_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1941_, 0, v_env_1935_);
lean_ctor_set(v___x_1941_, 1, v_mctx_1938_);
lean_ctor_set(v___x_1941_, 2, v_lctx_1939_);
lean_ctor_set(v___x_1941_, 3, v_options_1940_);
v___x_1942_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1941_);
lean_ctor_set(v___x_1942_, 1, v_msgData_1928_);
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
v_ref_1957_ = lean_ctor_get(v___y_1954_, 2);
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
lean_object* v_v_1987_; uint8_t v___x_1991_; 
v___x_1991_ = l_Lean_Meta_DiscrTree_hasNoindexAnnotation(v_e_1980_);
if (v___x_1991_ == 0)
{
lean_object* v___x_1992_; 
v___x_1992_ = l_Lean_Meta_DiscrTree_reduceDT(v_e_1980_, v_root_1978_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_);
if (lean_obj_tag(v___x_1992_) == 0)
{
lean_object* v_a_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2135_; 
v_a_1993_ = lean_ctor_get(v___x_1992_, 0);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_1995_ = v___x_1992_;
v_isShared_1996_ = v_isSharedCheck_2135_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_a_1993_);
lean_dec(v___x_1992_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2135_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v___x_1997_; lean_object* v_k_1999_; lean_object* v_nargs_2000_; lean_object* v_todo_2001_; lean_object* v___y_2002_; lean_object* v___y_2003_; lean_object* v___y_2004_; lean_object* v___y_2005_; 
v___x_1997_ = l_Lean_Expr_getAppFn(v_a_1993_);
switch(lean_obj_tag(v___x_1997_))
{
case 9:
{
lean_object* v_a_2044_; 
lean_del_object(v___x_1995_);
lean_dec(v_a_1993_);
v_a_2044_ = lean_ctor_get(v___x_1997_, 0);
lean_inc_ref(v_a_2044_);
lean_dec_ref_known(v___x_1997_, 1);
v_v_1987_ = v_a_2044_;
goto v___jp_1986_;
}
case 4:
{
lean_object* v_declName_2045_; lean_object* v___y_2047_; lean_object* v___y_2048_; lean_object* v___y_2049_; lean_object* v___y_2050_; 
lean_del_object(v___x_1995_);
v_declName_2045_ = lean_ctor_get(v___x_1997_, 0);
lean_inc(v_declName_2045_);
if (v_root_1978_ == 0)
{
lean_object* v___x_2053_; 
lean_inc(v_a_1993_);
v___x_2053_ = l_Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f(v_a_1993_);
if (lean_obj_tag(v___x_2053_) == 1)
{
lean_object* v_val_2054_; 
lean_dec(v_declName_2045_);
lean_dec_ref_known(v___x_1997_, 2);
lean_dec(v_a_1993_);
v_val_2054_ = lean_ctor_get(v___x_2053_, 0);
lean_inc(v_val_2054_);
lean_dec_ref_known(v___x_2053_, 1);
v_v_1987_ = v_val_2054_;
goto v___jp_1986_;
}
else
{
lean_object* v___x_2055_; 
lean_dec(v___x_2053_);
v___x_2055_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset(v_declName_2045_, v_a_1993_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2066_; 
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2058_ = v___x_2055_;
v_isShared_2059_ = v_isSharedCheck_2066_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_2055_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2066_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
uint8_t v___x_2060_; 
v___x_2060_ = lean_unbox(v_a_2056_);
lean_dec(v_a_2056_);
if (v___x_2060_ == 0)
{
lean_del_object(v___x_2058_);
v___y_2047_ = v_a_1981_;
v___y_2048_ = v_a_1982_;
v___y_2049_ = v_a_1983_;
v___y_2050_ = v_a_1984_;
goto v___jp_2046_;
}
else
{
lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2064_; 
lean_dec(v_declName_2045_);
lean_dec_ref_known(v___x_1997_, 2);
lean_dec(v_a_1993_);
v___x_2061_ = lean_box(3);
v___x_2062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2062_, 0, v___x_2061_);
lean_ctor_set(v___x_2062_, 1, v_todo_1979_);
if (v_isShared_2059_ == 0)
{
lean_ctor_set(v___x_2058_, 0, v___x_2062_);
v___x_2064_ = v___x_2058_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v___x_2062_);
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
else
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2074_; 
lean_dec(v_declName_2045_);
lean_dec_ref_known(v___x_1997_, 2);
lean_dec(v_a_1993_);
lean_dec_ref(v_todo_1979_);
v_a_2067_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2069_ = v___x_2055_;
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2055_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2072_; 
if (v_isShared_2070_ == 0)
{
v___x_2072_ = v___x_2069_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_a_2067_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
}
}
else
{
v___y_2047_ = v_a_1981_;
v___y_2048_ = v_a_1982_;
v___y_2049_ = v_a_1983_;
v___y_2050_ = v_a_1984_;
goto v___jp_2046_;
}
v___jp_2046_:
{
lean_object* v___x_2051_; lean_object* v___x_2052_; 
v___x_2051_ = l_Lean_Expr_getAppNumArgs(v_a_1993_);
lean_inc(v___x_2051_);
v___x_2052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2052_, 0, v_declName_2045_);
lean_ctor_set(v___x_2052_, 1, v___x_2051_);
v_k_1999_ = v___x_2052_;
v_nargs_2000_ = v___x_2051_;
v_todo_2001_ = v_todo_1979_;
v___y_2002_ = v___y_2047_;
v___y_2003_ = v___y_2048_;
v___y_2004_ = v___y_2049_;
v___y_2005_ = v___y_2050_;
goto v___jp_1998_;
}
}
case 11:
{
lean_object* v_typeName_2075_; lean_object* v_idx_2076_; lean_object* v_struct_2077_; lean_object* v___x_2078_; lean_object* v___y_2080_; lean_object* v_env_2084_; uint8_t v___x_2085_; 
lean_del_object(v___x_1995_);
v_typeName_2075_ = lean_ctor_get(v___x_1997_, 0);
lean_inc(v_typeName_2075_);
v_idx_2076_ = lean_ctor_get(v___x_1997_, 1);
lean_inc(v_idx_2076_);
v_struct_2077_ = lean_ctor_get(v___x_1997_, 2);
lean_inc_ref(v_struct_2077_);
v___x_2078_ = lean_st_ref_get(v_a_1984_);
v_env_2084_ = lean_ctor_get(v___x_2078_, 0);
lean_inc_ref(v_env_2084_);
lean_dec(v___x_2078_);
v___x_2085_ = l_Lean_isClass(v_env_2084_, v_typeName_2075_);
if (v___x_2085_ == 0)
{
v___y_2080_ = v_struct_2077_;
goto v___jp_2079_;
}
else
{
lean_object* v___x_2086_; 
v___x_2086_ = l_Lean_Meta_DiscrTree_mkNoindexAnnotation(v_struct_2077_);
v___y_2080_ = v___x_2086_;
goto v___jp_2079_;
}
v___jp_2079_:
{
lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2081_ = l_Lean_Expr_getAppNumArgs(v_a_1993_);
lean_inc(v___x_2081_);
v___x_2082_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_2082_, 0, v_typeName_2075_);
lean_ctor_set(v___x_2082_, 1, v_idx_2076_);
lean_ctor_set(v___x_2082_, 2, v___x_2081_);
v___x_2083_ = lean_array_push(v_todo_1979_, v___y_2080_);
v_k_1999_ = v___x_2082_;
v_nargs_2000_ = v___x_2081_;
v_todo_2001_ = v___x_2083_;
v___y_2002_ = v_a_1981_;
v___y_2003_ = v_a_1982_;
v___y_2004_ = v_a_1983_;
v___y_2005_ = v_a_1984_;
goto v___jp_1998_;
}
}
case 1:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2090_; 
lean_dec_ref_known(v___x_1997_, 1);
lean_dec(v_a_1993_);
v___x_2087_ = lean_box(3);
v___x_2088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2087_);
lean_ctor_set(v___x_2088_, 1, v_todo_1979_);
if (v_isShared_1996_ == 0)
{
lean_ctor_set(v___x_1995_, 0, v___x_2088_);
v___x_2090_ = v___x_1995_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v___x_2088_);
v___x_2090_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
return v___x_2090_;
}
}
case 2:
{
lean_object* v_mvarId_2092_; lean_object* v___x_2093_; uint8_t v___x_2094_; 
lean_dec(v_a_1993_);
v_mvarId_2092_ = lean_ctor_get(v___x_1997_, 0);
lean_inc(v_mvarId_2092_);
lean_dec_ref_known(v___x_1997_, 1);
v___x_2093_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_tmpMVarId));
v___x_2094_ = l_Lean_instBEqMVarId_beq(v_mvarId_2092_, v___x_2093_);
lean_dec(v_mvarId_2092_);
if (v___x_2094_ == 0)
{
lean_object* v___x_2095_; lean_object* v___x_2096_; 
lean_del_object(v___x_1995_);
lean_dec_ref(v_todo_1979_);
v___x_2095_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1, &l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1);
v___x_2096_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(v___x_2095_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_);
return v___x_2096_;
}
else
{
lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2100_; 
v___x_2097_ = lean_box(3);
v___x_2098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2097_);
lean_ctor_set(v___x_2098_, 1, v_todo_1979_);
if (v_isShared_1996_ == 0)
{
lean_ctor_set(v___x_1995_, 0, v___x_2098_);
v___x_2100_ = v___x_1995_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v___x_2098_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
}
case 7:
{
lean_object* v_binderType_2102_; lean_object* v_body_2103_; lean_object* v_b_2105_; uint8_t v___x_2119_; 
lean_dec(v_a_1993_);
v_binderType_2102_ = lean_ctor_get(v___x_1997_, 1);
lean_inc_ref(v_binderType_2102_);
v_body_2103_ = lean_ctor_get(v___x_1997_, 2);
lean_inc_ref(v_body_2103_);
lean_dec_ref_known(v___x_1997_, 3);
v___x_2119_ = l_Lean_Expr_hasLooseBVars(v_body_2103_);
if (v___x_2119_ == 0)
{
v_b_2105_ = v_body_2103_;
goto v___jp_2104_;
}
else
{
lean_object* v___x_2120_; 
v___x_2120_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(v_body_2103_, v_a_1983_, v_a_1984_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v_a_2121_; 
v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
lean_inc(v_a_2121_);
lean_dec_ref_known(v___x_2120_, 1);
v_b_2105_ = v_a_2121_;
goto v___jp_2104_;
}
else
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2129_; 
lean_dec_ref(v_binderType_2102_);
lean_del_object(v___x_1995_);
lean_dec_ref(v_todo_1979_);
v_a_2122_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2124_ = v___x_2120_;
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2120_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2127_; 
if (v_isShared_2125_ == 0)
{
v___x_2127_ = v___x_2124_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_a_2122_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
}
}
v___jp_2104_:
{
uint8_t v___x_2106_; 
v___x_2106_ = l_Lean_Expr_hasLooseBVars(v_b_2105_);
if (v___x_2106_ == 0)
{
lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2112_; 
v___x_2107_ = lean_box(5);
v___x_2108_ = lean_array_push(v_todo_1979_, v_binderType_2102_);
v___x_2109_ = lean_array_push(v___x_2108_, v_b_2105_);
v___x_2110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2107_);
lean_ctor_set(v___x_2110_, 1, v___x_2109_);
if (v_isShared_1996_ == 0)
{
lean_ctor_set(v___x_1995_, 0, v___x_2110_);
v___x_2112_ = v___x_1995_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v___x_2110_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
return v___x_2112_;
}
}
else
{
lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2117_; 
lean_dec_ref(v_b_2105_);
lean_dec_ref(v_binderType_2102_);
v___x_2114_ = lean_box(4);
v___x_2115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2114_);
lean_ctor_set(v___x_2115_, 1, v_todo_1979_);
if (v_isShared_1996_ == 0)
{
lean_ctor_set(v___x_1995_, 0, v___x_2115_);
v___x_2117_ = v___x_1995_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v___x_2115_);
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
default: 
{
lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2133_; 
lean_dec_ref(v___x_1997_);
lean_dec(v_a_1993_);
v___x_2130_ = lean_box(4);
v___x_2131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2130_);
lean_ctor_set(v___x_2131_, 1, v_todo_1979_);
if (v_isShared_1996_ == 0)
{
lean_ctor_set(v___x_1995_, 0, v___x_2131_);
v___x_2133_ = v___x_1995_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v___x_2131_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
return v___x_2133_;
}
}
}
v___jp_1998_:
{
lean_object* v___x_2006_; 
lean_inc(v_nargs_2000_);
v___x_2006_ = l_Lean_Meta_getFunInfoNArgs(v___x_1997_, v_nargs_2000_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_);
if (lean_obj_tag(v___x_2006_) == 0)
{
lean_object* v_a_2007_; lean_object* v_paramInfo_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2034_; 
v_a_2007_ = lean_ctor_get(v___x_2006_, 0);
lean_inc(v_a_2007_);
lean_dec_ref_known(v___x_2006_, 1);
v_paramInfo_2008_ = lean_ctor_get(v_a_2007_, 0);
v_isSharedCheck_2034_ = !lean_is_exclusive(v_a_2007_);
if (v_isSharedCheck_2034_ == 0)
{
lean_object* v_unused_2035_; 
v_unused_2035_ = lean_ctor_get(v_a_2007_, 1);
lean_dec(v_unused_2035_);
v___x_2010_ = v_a_2007_;
v_isShared_2011_ = v_isSharedCheck_2034_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_paramInfo_2008_);
lean_dec(v_a_2007_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2034_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; 
v___x_2012_ = lean_unsigned_to_nat(1u);
v___x_2013_ = lean_nat_sub(v_nargs_2000_, v___x_2012_);
lean_dec(v_nargs_2000_);
v___x_2014_ = l_Lean_Meta_LazyDiscrTree_MatchClone_pushArgsAux(v_paramInfo_2008_, v___x_2013_, v_a_1993_, v_todo_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_);
lean_dec_ref(v_paramInfo_2008_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v_a_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2025_; 
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2017_ = v___x_2014_;
v_isShared_2018_ = v_isSharedCheck_2025_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_a_2015_);
lean_dec(v___x_2014_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2025_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2020_; 
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 1, v_a_2015_);
lean_ctor_set(v___x_2010_, 0, v_k_1999_);
v___x_2020_ = v___x_2010_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_k_1999_);
lean_ctor_set(v_reuseFailAlloc_2024_, 1, v_a_2015_);
v___x_2020_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
lean_object* v___x_2022_; 
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 0, v___x_2020_);
v___x_2022_ = v___x_2017_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v___x_2020_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
}
else
{
lean_object* v_a_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2033_; 
lean_del_object(v___x_2010_);
lean_dec(v_k_1999_);
v_a_2026_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2028_ = v___x_2014_;
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_a_2026_);
lean_dec(v___x_2014_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2031_; 
if (v_isShared_2029_ == 0)
{
v___x_2031_ = v___x_2028_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_a_2026_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
}
}
}
}
}
else
{
lean_object* v_a_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2043_; 
lean_dec_ref(v_todo_2001_);
lean_dec(v_nargs_2000_);
lean_dec(v_k_1999_);
lean_dec(v_a_1993_);
v_a_2036_ = lean_ctor_get(v___x_2006_, 0);
v_isSharedCheck_2043_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2038_ = v___x_2006_;
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_a_2036_);
lean_dec(v___x_2006_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2041_; 
if (v_isShared_2039_ == 0)
{
v___x_2041_ = v___x_2038_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v_a_2036_);
v___x_2041_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
return v___x_2041_;
}
}
}
}
}
}
else
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2143_; 
lean_dec_ref(v_todo_1979_);
v_a_2136_ = lean_ctor_get(v___x_1992_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2138_ = v___x_1992_;
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_1992_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2141_; 
if (v_isShared_2139_ == 0)
{
v___x_2141_ = v___x_2138_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_a_2136_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
}
}
else
{
lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
lean_dec_ref(v_e_1980_);
v___x_2144_ = lean_box(3);
v___x_2145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2145_, 0, v___x_2144_);
lean_ctor_set(v___x_2145_, 1, v_todo_1979_);
v___x_2146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2146_, 0, v___x_2145_);
return v___x_2146_;
}
v___jp_1986_:
{
lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1988_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1988_, 0, v_v_1987_);
v___x_1989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1988_);
lean_ctor_set(v___x_1989_, 1, v_todo_1979_);
v___x_1990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1990_, 0, v___x_1989_);
return v___x_1990_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushArgs___boxed(lean_object* v_root_2147_, lean_object* v_todo_2148_, lean_object* v_e_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_){
_start:
{
uint8_t v_root_boxed_2155_; lean_object* v_res_2156_; 
v_root_boxed_2155_ = lean_unbox(v_root_2147_);
v_res_2156_ = l_Lean_Meta_LazyDiscrTree_pushArgs(v_root_boxed_2155_, v_todo_2148_, v_e_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_);
lean_dec(v_a_2153_);
lean_dec_ref(v_a_2152_);
lean_dec(v_a_2151_);
lean_dec_ref(v_a_2150_);
return v_res_2156_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0(lean_object* v_00_u03b1_2157_, lean_object* v_msg_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_){
_start:
{
lean_object* v___x_2164_; 
v___x_2164_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(v_msg_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_);
return v___x_2164_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___boxed(lean_object* v_00_u03b1_2165_, lean_object* v_msg_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_){
_start:
{
lean_object* v_res_2172_; 
v_res_2172_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0(v_00_u03b1_2165_, v_msg_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_);
lean_dec(v___y_2170_);
lean_dec_ref(v___y_2169_);
lean_dec(v___y_2168_);
lean_dec_ref(v___y_2167_);
return v_res_2172_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_initCapacity(void){
_start:
{
lean_object* v___x_2173_; 
v___x_2173_ = lean_unsigned_to_nat(8u);
return v___x_2173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_rootKey(lean_object* v_e_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_){
_start:
{
uint8_t v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
v___x_2180_ = 1;
v___x_2181_ = lean_unsigned_to_nat(8u);
v___x_2182_ = lean_mk_empty_array_with_capacity(v___x_2181_);
v___x_2183_ = l_Lean_Meta_LazyDiscrTree_pushArgs(v___x_2180_, v___x_2182_, v_e_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_);
return v___x_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_rootKey___boxed(lean_object* v_e_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_){
_start:
{
lean_object* v_res_2190_; 
v_res_2190_ = l_Lean_Meta_LazyDiscrTree_rootKey(v_e_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_);
lean_dec(v_a_2188_);
lean_dec_ref(v_a_2187_);
lean_dec(v_a_2186_);
lean_dec_ref(v_a_2185_);
return v_res_2190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_buildPath(lean_object* v_op_2191_, uint8_t v_root_2192_, lean_object* v_todo_2193_, lean_object* v_keys_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_){
_start:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; uint8_t v___x_2202_; 
v___x_2200_ = lean_array_get_size(v_todo_2193_);
v___x_2201_ = lean_unsigned_to_nat(0u);
v___x_2202_ = lean_nat_dec_eq(v___x_2200_, v___x_2201_);
if (v___x_2202_ == 0)
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v_e_2206_; lean_object* v_todo_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2203_ = l_Lean_instInhabitedExpr;
v___x_2204_ = lean_unsigned_to_nat(1u);
v___x_2205_ = lean_nat_sub(v___x_2200_, v___x_2204_);
v_e_2206_ = lean_array_get(v___x_2203_, v_todo_2193_, v___x_2205_);
lean_dec(v___x_2205_);
v_todo_2207_ = lean_array_pop(v_todo_2193_);
v___x_2208_ = lean_box(v_root_2192_);
lean_inc_ref(v_op_2191_);
lean_inc(v_a_2198_);
lean_inc_ref(v_a_2197_);
lean_inc(v_a_2196_);
lean_inc_ref(v_a_2195_);
v___x_2209_ = lean_apply_8(v_op_2191_, v___x_2208_, v_todo_2207_, v_e_2206_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, lean_box(0));
if (lean_obj_tag(v___x_2209_) == 0)
{
lean_object* v_a_2210_; lean_object* v_fst_2211_; lean_object* v_snd_2212_; lean_object* v___x_2213_; 
v_a_2210_ = lean_ctor_get(v___x_2209_, 0);
lean_inc(v_a_2210_);
lean_dec_ref_known(v___x_2209_, 1);
v_fst_2211_ = lean_ctor_get(v_a_2210_, 0);
lean_inc(v_fst_2211_);
v_snd_2212_ = lean_ctor_get(v_a_2210_, 1);
lean_inc(v_snd_2212_);
lean_dec(v_a_2210_);
v___x_2213_ = lean_array_push(v_keys_2194_, v_fst_2211_);
v_root_2192_ = v___x_2202_;
v_todo_2193_ = v_snd_2212_;
v_keys_2194_ = v___x_2213_;
goto _start;
}
else
{
lean_object* v_a_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2222_; 
lean_dec_ref(v_keys_2194_);
lean_dec_ref(v_op_2191_);
v_a_2215_ = lean_ctor_get(v___x_2209_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2209_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2217_ = v___x_2209_;
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_a_2215_);
lean_dec(v___x_2209_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2220_; 
if (v_isShared_2218_ == 0)
{
v___x_2220_ = v___x_2217_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v_a_2215_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
}
}
else
{
lean_object* v___x_2223_; 
lean_dec_ref(v_todo_2193_);
lean_dec_ref(v_op_2191_);
v___x_2223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2223_, 0, v_keys_2194_);
return v___x_2223_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_buildPath___boxed(lean_object* v_op_2224_, lean_object* v_root_2225_, lean_object* v_todo_2226_, lean_object* v_keys_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_){
_start:
{
uint8_t v_root_boxed_2233_; lean_object* v_res_2234_; 
v_root_boxed_2233_ = lean_unbox(v_root_2225_);
v_res_2234_ = l_Lean_Meta_LazyDiscrTree_buildPath(v_op_2224_, v_root_boxed_2233_, v_todo_2226_, v_keys_2227_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_);
lean_dec(v_a_2231_);
lean_dec_ref(v_a_2230_);
lean_dec(v_a_2229_);
lean_dec_ref(v_a_2228_);
return v_res_2234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_patternPath(lean_object* v_e_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_){
_start:
{
lean_object* v_op_2242_; lean_object* v___x_2243_; lean_object* v_todo_2244_; uint8_t v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; 
v_op_2242_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_patternPath___closed__0));
v___x_2243_ = lean_unsigned_to_nat(8u);
v_todo_2244_ = lean_mk_empty_array_with_capacity(v___x_2243_);
v___x_2245_ = 1;
lean_inc_ref(v_todo_2244_);
v___x_2246_ = lean_array_push(v_todo_2244_, v_e_2236_);
v___x_2247_ = l_Lean_Meta_LazyDiscrTree_buildPath(v_op_2242_, v___x_2245_, v___x_2246_, v_todo_2244_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_);
return v___x_2247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_patternPath___boxed(lean_object* v_e_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_){
_start:
{
lean_object* v_res_2254_; 
v_res_2254_ = l_Lean_Meta_LazyDiscrTree_patternPath(v_e_2248_, v_a_2249_, v_a_2250_, v_a_2251_, v_a_2252_);
lean_dec(v_a_2252_);
lean_dec_ref(v_a_2251_);
lean_dec(v_a_2250_);
lean_dec_ref(v_a_2249_);
return v_res_2254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath___lam__0(uint8_t v_root_2255_, lean_object* v_todo_2256_, lean_object* v_e_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_){
_start:
{
uint8_t v___x_2263_; lean_object* v___x_2264_; 
v___x_2263_ = 1;
v___x_2264_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_2257_, v___x_2263_, v_root_2255_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_);
if (lean_obj_tag(v___x_2264_) == 0)
{
lean_object* v_a_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2282_; 
v_a_2265_ = lean_ctor_get(v___x_2264_, 0);
v_isSharedCheck_2282_ = !lean_is_exclusive(v___x_2264_);
if (v_isSharedCheck_2282_ == 0)
{
v___x_2267_ = v___x_2264_;
v_isShared_2268_ = v_isSharedCheck_2282_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_a_2265_);
lean_dec(v___x_2264_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2282_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v_fst_2269_; lean_object* v_snd_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2281_; 
v_fst_2269_ = lean_ctor_get(v_a_2265_, 0);
v_snd_2270_ = lean_ctor_get(v_a_2265_, 1);
v_isSharedCheck_2281_ = !lean_is_exclusive(v_a_2265_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2272_ = v_a_2265_;
v_isShared_2273_ = v_isSharedCheck_2281_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_snd_2270_);
lean_inc(v_fst_2269_);
lean_dec(v_a_2265_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2281_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v___x_2274_; lean_object* v___x_2276_; 
v___x_2274_ = l_Array_append___redArg(v_todo_2256_, v_snd_2270_);
lean_dec(v_snd_2270_);
if (v_isShared_2273_ == 0)
{
lean_ctor_set(v___x_2272_, 1, v___x_2274_);
v___x_2276_ = v___x_2272_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v_fst_2269_);
lean_ctor_set(v_reuseFailAlloc_2280_, 1, v___x_2274_);
v___x_2276_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
lean_object* v___x_2278_; 
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 0, v___x_2276_);
v___x_2278_ = v___x_2267_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v___x_2276_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
}
}
}
else
{
lean_dec_ref(v_todo_2256_);
return v___x_2264_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath___lam__0___boxed(lean_object* v_root_2283_, lean_object* v_todo_2284_, lean_object* v_e_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_){
_start:
{
uint8_t v_root_boxed_2291_; lean_object* v_res_2292_; 
v_root_boxed_2291_ = lean_unbox(v_root_2283_);
v_res_2292_ = l_Lean_Meta_LazyDiscrTree_targetPath___lam__0(v_root_boxed_2291_, v_todo_2284_, v_e_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
lean_dec(v___y_2289_);
lean_dec_ref(v___y_2288_);
lean_dec(v___y_2287_);
lean_dec_ref(v___y_2286_);
return v_res_2292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath(lean_object* v_e_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_){
_start:
{
lean_object* v_op_2300_; lean_object* v___x_2301_; lean_object* v_todo_2302_; uint8_t v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; 
v_op_2300_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_targetPath___closed__0));
v___x_2301_ = lean_unsigned_to_nat(8u);
v_todo_2302_ = lean_mk_empty_array_with_capacity(v___x_2301_);
v___x_2303_ = 1;
lean_inc_ref(v_todo_2302_);
v___x_2304_ = lean_array_push(v_todo_2302_, v_e_2294_);
v___x_2305_ = l_Lean_Meta_LazyDiscrTree_buildPath(v_op_2300_, v___x_2303_, v___x_2304_, v_todo_2302_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_);
return v___x_2305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath___boxed(lean_object* v_e_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_){
_start:
{
lean_object* v_res_2312_; 
v_res_2312_ = l_Lean_Meta_LazyDiscrTree_targetPath(v_e_2306_, v_a_2307_, v_a_2308_, v_a_2309_, v_a_2310_);
lean_dec(v_a_2310_);
lean_dec_ref(v_a_2309_);
lean_dec(v_a_2308_);
lean_dec_ref(v_a_2307_);
return v_res_2312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___redArg___lam__0(lean_object* v_tries_2313_, lean_object* v_m_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_){
_start:
{
lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___x_2320_ = lean_st_mk_ref(v_tries_2313_);
lean_inc(v___x_2320_);
v___x_2321_ = lean_apply_6(v_m_2314_, v___x_2320_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, lean_box(0));
if (lean_obj_tag(v___x_2321_) == 0)
{
lean_object* v_a_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2331_; 
v_a_2322_ = lean_ctor_get(v___x_2321_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2321_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2324_ = v___x_2321_;
v_isShared_2325_ = v_isSharedCheck_2331_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_a_2322_);
lean_dec(v___x_2321_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2331_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2329_; 
v___x_2326_ = lean_st_ref_get(v___x_2320_);
lean_dec(v___x_2320_);
v___x_2327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2327_, 0, v_a_2322_);
lean_ctor_set(v___x_2327_, 1, v___x_2326_);
if (v_isShared_2325_ == 0)
{
lean_ctor_set(v___x_2324_, 0, v___x_2327_);
v___x_2329_ = v___x_2324_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v___x_2327_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
}
}
}
else
{
lean_object* v_a_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2339_; 
lean_dec(v___x_2320_);
v_a_2332_ = lean_ctor_get(v___x_2321_, 0);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2321_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2334_ = v___x_2321_;
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_a_2332_);
lean_dec(v___x_2321_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v___x_2337_; 
if (v_isShared_2335_ == 0)
{
v___x_2337_ = v___x_2334_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_a_2332_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
return v___x_2337_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___redArg___lam__0___boxed(lean_object* v_tries_2340_, lean_object* v_m_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_){
_start:
{
lean_object* v_res_2347_; 
v_res_2347_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg___lam__0(v_tries_2340_, v_m_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_);
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___redArg(lean_object* v_d_2348_, lean_object* v_m_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_){
_start:
{
lean_object* v_tries_2355_; lean_object* v_roots_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2409_; 
v_tries_2355_ = lean_ctor_get(v_d_2348_, 0);
v_roots_2356_ = lean_ctor_get(v_d_2348_, 1);
v_isSharedCheck_2409_ = !lean_is_exclusive(v_d_2348_);
if (v_isSharedCheck_2409_ == 0)
{
v___x_2358_ = v_d_2348_;
v_isShared_2359_ = v_isSharedCheck_2409_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_roots_2356_);
lean_inc(v_tries_2355_);
lean_dec(v_d_2348_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2409_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v___y_2361_; lean_object* v___x_2390_; uint8_t v_transparency_2391_; uint8_t v___x_2392_; uint8_t v___x_2393_; 
v___x_2390_ = l_Lean_Meta_Context_config(v_a_2350_);
v_transparency_2391_ = lean_ctor_get_uint8(v___x_2390_, 9);
lean_dec_ref(v___x_2390_);
v___x_2392_ = 2;
v___x_2393_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2391_, v___x_2392_);
if (v___x_2393_ == 0)
{
lean_object* v_keyedConfig_2394_; uint8_t v_trackZetaDelta_2395_; lean_object* v_zetaDeltaSet_2396_; lean_object* v_lctx_2397_; lean_object* v_localInstances_2398_; lean_object* v_defEqCtx_x3f_2399_; lean_object* v_synthPendingDepth_2400_; lean_object* v_customCanUnfoldPredicate_x3f_2401_; uint8_t v_univApprox_2402_; uint8_t v_inTypeClassResolution_2403_; uint8_t v_cacheInferType_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; 
v_keyedConfig_2394_ = lean_ctor_get(v_a_2350_, 0);
v_trackZetaDelta_2395_ = lean_ctor_get_uint8(v_a_2350_, sizeof(void*)*7);
v_zetaDeltaSet_2396_ = lean_ctor_get(v_a_2350_, 1);
v_lctx_2397_ = lean_ctor_get(v_a_2350_, 2);
v_localInstances_2398_ = lean_ctor_get(v_a_2350_, 3);
v_defEqCtx_x3f_2399_ = lean_ctor_get(v_a_2350_, 4);
v_synthPendingDepth_2400_ = lean_ctor_get(v_a_2350_, 5);
v_customCanUnfoldPredicate_x3f_2401_ = lean_ctor_get(v_a_2350_, 6);
v_univApprox_2402_ = lean_ctor_get_uint8(v_a_2350_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2403_ = lean_ctor_get_uint8(v_a_2350_, sizeof(void*)*7 + 2);
v_cacheInferType_2404_ = lean_ctor_get_uint8(v_a_2350_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2394_);
v___x_2405_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2392_, v_keyedConfig_2394_);
lean_inc(v_customCanUnfoldPredicate_x3f_2401_);
lean_inc(v_synthPendingDepth_2400_);
lean_inc(v_defEqCtx_x3f_2399_);
lean_inc_ref(v_localInstances_2398_);
lean_inc_ref(v_lctx_2397_);
lean_inc(v_zetaDeltaSet_2396_);
v___x_2406_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2406_, 0, v___x_2405_);
lean_ctor_set(v___x_2406_, 1, v_zetaDeltaSet_2396_);
lean_ctor_set(v___x_2406_, 2, v_lctx_2397_);
lean_ctor_set(v___x_2406_, 3, v_localInstances_2398_);
lean_ctor_set(v___x_2406_, 4, v_defEqCtx_x3f_2399_);
lean_ctor_set(v___x_2406_, 5, v_synthPendingDepth_2400_);
lean_ctor_set(v___x_2406_, 6, v_customCanUnfoldPredicate_x3f_2401_);
lean_ctor_set_uint8(v___x_2406_, sizeof(void*)*7, v_trackZetaDelta_2395_);
lean_ctor_set_uint8(v___x_2406_, sizeof(void*)*7 + 1, v_univApprox_2402_);
lean_ctor_set_uint8(v___x_2406_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2403_);
lean_ctor_set_uint8(v___x_2406_, sizeof(void*)*7 + 3, v_cacheInferType_2404_);
lean_inc(v_a_2353_);
lean_inc_ref(v_a_2352_);
lean_inc(v_a_2351_);
v___x_2407_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg___lam__0(v_tries_2355_, v_m_2349_, v___x_2406_, v_a_2351_, v_a_2352_, v_a_2353_);
v___y_2361_ = v___x_2407_;
goto v___jp_2360_;
}
else
{
lean_object* v___x_2408_; 
lean_inc(v_a_2353_);
lean_inc_ref(v_a_2352_);
lean_inc(v_a_2351_);
lean_inc_ref(v_a_2350_);
v___x_2408_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg___lam__0(v_tries_2355_, v_m_2349_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_);
v___y_2361_ = v___x_2408_;
goto v___jp_2360_;
}
v___jp_2360_:
{
if (lean_obj_tag(v___y_2361_) == 0)
{
lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2381_; 
v_a_2362_ = lean_ctor_get(v___y_2361_, 0);
v_isSharedCheck_2381_ = !lean_is_exclusive(v___y_2361_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2364_ = v___y_2361_;
v_isShared_2365_ = v_isSharedCheck_2381_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v___y_2361_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2381_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v_fst_2366_; lean_object* v_snd_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2380_; 
v_fst_2366_ = lean_ctor_get(v_a_2362_, 0);
v_snd_2367_ = lean_ctor_get(v_a_2362_, 1);
v_isSharedCheck_2380_ = !lean_is_exclusive(v_a_2362_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2369_ = v_a_2362_;
v_isShared_2370_ = v_isSharedCheck_2380_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_snd_2367_);
lean_inc(v_fst_2366_);
lean_dec(v_a_2362_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2380_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2372_; 
if (v_isShared_2359_ == 0)
{
lean_ctor_set(v___x_2358_, 0, v_snd_2367_);
v___x_2372_ = v___x_2358_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_snd_2367_);
lean_ctor_set(v_reuseFailAlloc_2379_, 1, v_roots_2356_);
v___x_2372_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
lean_object* v___x_2374_; 
if (v_isShared_2370_ == 0)
{
lean_ctor_set(v___x_2369_, 1, v___x_2372_);
v___x_2374_ = v___x_2369_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_fst_2366_);
lean_ctor_set(v_reuseFailAlloc_2378_, 1, v___x_2372_);
v___x_2374_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
lean_object* v___x_2376_; 
if (v_isShared_2365_ == 0)
{
lean_ctor_set(v___x_2364_, 0, v___x_2374_);
v___x_2376_ = v___x_2364_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v___x_2374_);
v___x_2376_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
return v___x_2376_;
}
}
}
}
}
}
else
{
lean_object* v_a_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2389_; 
lean_del_object(v___x_2358_);
lean_dec_ref(v_roots_2356_);
v_a_2382_ = lean_ctor_get(v___y_2361_, 0);
v_isSharedCheck_2389_ = !lean_is_exclusive(v___y_2361_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2384_ = v___y_2361_;
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_a_2382_);
lean_dec(v___y_2361_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v___x_2387_; 
if (v_isShared_2385_ == 0)
{
v___x_2387_ = v___x_2384_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v_a_2382_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___redArg___boxed(lean_object* v_d_2410_, lean_object* v_m_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_){
_start:
{
lean_object* v_res_2417_; 
v_res_2417_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_d_2410_, v_m_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_);
lean_dec(v_a_2415_);
lean_dec_ref(v_a_2414_);
lean_dec(v_a_2413_);
lean_dec_ref(v_a_2412_);
return v_res_2417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch(lean_object* v_00_u03b1_2418_, lean_object* v_00_u03b2_2419_, lean_object* v_d_2420_, lean_object* v_m_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_){
_start:
{
lean_object* v___x_2427_; 
v___x_2427_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_d_2420_, v_m_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_);
return v___x_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___boxed(lean_object* v_00_u03b1_2428_, lean_object* v_00_u03b2_2429_, lean_object* v_d_2430_, lean_object* v_m_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_){
_start:
{
lean_object* v_res_2437_; 
v_res_2437_ = l_Lean_Meta_LazyDiscrTree_runMatch(v_00_u03b1_2428_, v_00_u03b2_2429_, v_d_2430_, v_m_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_);
lean_dec(v_a_2435_);
lean_dec_ref(v_a_2434_);
lean_dec(v_a_2433_);
lean_dec_ref(v_a_2432_);
return v_res_2437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie___redArg(lean_object* v_i_2438_, lean_object* v_v_2439_, lean_object* v_a_2440_){
_start:
{
lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; 
v___x_2442_ = lean_st_ref_take(v_a_2440_);
v___x_2443_ = lean_box(0);
v___x_2444_ = lean_array_set(v___x_2442_, v_i_2438_, v_v_2439_);
v___x_2445_ = lean_st_ref_put(v_a_2440_, v___x_2444_);
v___x_2446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2446_, 0, v___x_2443_);
return v___x_2446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie___redArg___boxed(lean_object* v_i_2447_, lean_object* v_v_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_){
_start:
{
lean_object* v_res_2451_; 
v_res_2451_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_i_2447_, v_v_2448_, v_a_2449_);
lean_dec(v_a_2449_);
lean_dec(v_i_2447_);
return v_res_2451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie(lean_object* v_00_u03b1_2452_, lean_object* v_i_2453_, lean_object* v_v_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_){
_start:
{
lean_object* v___x_2461_; 
v___x_2461_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_i_2453_, v_v_2454_, v_a_2455_);
return v___x_2461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie___boxed(lean_object* v_00_u03b1_2462_, lean_object* v_i_2463_, lean_object* v_v_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_){
_start:
{
lean_object* v_res_2471_; 
v_res_2471_ = l_Lean_Meta_LazyDiscrTree_setTrie(v_00_u03b1_2462_, v_i_2463_, v_v_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_);
lean_dec(v_a_2469_);
lean_dec_ref(v_a_2468_);
lean_dec(v_a_2467_);
lean_dec_ref(v_a_2466_);
lean_dec(v_a_2465_);
lean_dec(v_i_2463_);
return v_res_2471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___redArg___lam__0(lean_object* v_e_2472_, lean_object* v_a_2473_){
_start:
{
lean_object* v_sz_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; 
v_sz_2474_ = lean_array_get_size(v_a_2473_);
v___x_2475_ = lean_unsigned_to_nat(0u);
v___x_2476_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___x_2477_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2);
v___x_2478_ = lean_unsigned_to_nat(1u);
v___x_2479_ = lean_mk_empty_array_with_capacity(v___x_2478_);
v___x_2480_ = lean_array_push(v___x_2479_, v_e_2472_);
v___x_2481_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2481_, 0, v___x_2476_);
lean_ctor_set(v___x_2481_, 1, v___x_2475_);
lean_ctor_set(v___x_2481_, 2, v___x_2477_);
lean_ctor_set(v___x_2481_, 3, v___x_2480_);
v___x_2482_ = lean_array_push(v_a_2473_, v___x_2481_);
v___x_2483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2483_, 0, v_sz_2474_);
lean_ctor_set(v___x_2483_, 1, v___x_2482_);
return v___x_2483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___redArg(lean_object* v_inst_2484_, lean_object* v_e_2485_){
_start:
{
lean_object* v_modifyGet_2486_; lean_object* v___f_2487_; lean_object* v___x_2488_; 
v_modifyGet_2486_ = lean_ctor_get(v_inst_2484_, 2);
lean_inc(v_modifyGet_2486_);
lean_dec_ref(v_inst_2484_);
v___f_2487_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_newTrie___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2487_, 0, v_e_2485_);
v___x_2488_ = lean_apply_2(v_modifyGet_2486_, lean_box(0), v___f_2487_);
return v___x_2488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie(lean_object* v_m_2489_, lean_object* v_00_u03b1_2490_, lean_object* v_inst_2491_, lean_object* v_inst_2492_, lean_object* v_e_2493_){
_start:
{
lean_object* v___x_2494_; 
v___x_2494_ = l_Lean_Meta_LazyDiscrTree_newTrie___redArg(v_inst_2492_, v_e_2493_);
return v___x_2494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___boxed(lean_object* v_m_2495_, lean_object* v_00_u03b1_2496_, lean_object* v_inst_2497_, lean_object* v_inst_2498_, lean_object* v_e_2499_){
_start:
{
lean_object* v_res_2500_; 
v_res_2500_ = l_Lean_Meta_LazyDiscrTree_newTrie(v_m_2495_, v_00_u03b1_2496_, v_inst_2497_, v_inst_2498_, v_e_2499_);
lean_dec_ref(v_inst_2497_);
return v_res_2500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(lean_object* v_i_2501_, lean_object* v_e_2502_, lean_object* v_a_2503_){
_start:
{
lean_object* v___x_2505_; lean_object* v_fst_2507_; lean_object* v_snd_2508_; lean_object* v___x_2511_; lean_object* v___x_2512_; uint8_t v___x_2513_; 
v___x_2505_ = lean_st_ref_take(v_a_2503_);
v___x_2511_ = lean_box(0);
v___x_2512_ = lean_array_get_size(v___x_2505_);
v___x_2513_ = lean_nat_dec_lt(v_i_2501_, v___x_2512_);
if (v___x_2513_ == 0)
{
lean_dec_ref(v_e_2502_);
v_fst_2507_ = v___x_2511_;
v_snd_2508_ = v___x_2505_;
goto v___jp_2506_;
}
else
{
lean_object* v_v_2514_; lean_object* v_xs_x27_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; 
v_v_2514_ = lean_array_fget(v___x_2505_, v_i_2501_);
v_xs_x27_2515_ = lean_array_fset(v___x_2505_, v_i_2501_, v___x_2511_);
v___x_2516_ = l_Lean_Meta_LazyDiscrTree_Trie_pushPending___redArg(v_v_2514_, v_e_2502_);
v___x_2517_ = lean_array_fset(v_xs_x27_2515_, v_i_2501_, v___x_2516_);
v_fst_2507_ = v___x_2511_;
v_snd_2508_ = v___x_2517_;
goto v___jp_2506_;
}
v___jp_2506_:
{
lean_object* v___x_2509_; lean_object* v___x_2510_; 
v___x_2509_ = lean_st_ref_put(v_a_2503_, v_snd_2508_);
v___x_2510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2510_, 0, v_fst_2507_);
return v___x_2510_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg___boxed(lean_object* v_i_2518_, lean_object* v_e_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_){
_start:
{
lean_object* v_res_2522_; 
v_res_2522_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_i_2518_, v_e_2519_, v_a_2520_);
lean_dec(v_a_2520_);
lean_dec(v_i_2518_);
return v_res_2522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie(lean_object* v_00_u03b1_2523_, lean_object* v_i_2524_, lean_object* v_e_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_){
_start:
{
lean_object* v___x_2532_; 
v___x_2532_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_i_2524_, v_e_2525_, v_a_2526_);
return v___x_2532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___boxed(lean_object* v_00_u03b1_2533_, lean_object* v_i_2534_, lean_object* v_e_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_){
_start:
{
lean_object* v_res_2542_; 
v_res_2542_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie(v_00_u03b1_2533_, v_i_2534_, v_e_2535_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_);
lean_dec(v_a_2540_);
lean_dec_ref(v_a_2539_);
lean_dec(v_a_2538_);
lean_dec_ref(v_a_2537_);
lean_dec(v_a_2536_);
lean_dec(v_i_2534_);
return v_res_2542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0(lean_object* v_x_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_){
_start:
{
lean_object* v___x_2550_; 
lean_inc(v___y_2544_);
v___x_2550_ = lean_apply_6(v_x_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, lean_box(0));
return v___x_2550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0___boxed(lean_object* v_x_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_){
_start:
{
lean_object* v_res_2558_; 
v_res_2558_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0(v_x_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_);
lean_dec(v___y_2552_);
return v_res_2558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(lean_object* v_lctx_2559_, lean_object* v_localInsts_2560_, lean_object* v_x_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_){
_start:
{
lean_object* v___f_2568_; lean_object* v___x_2569_; 
lean_inc(v___y_2562_);
v___f_2568_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2568_, 0, v_x_2561_);
lean_closure_set(v___f_2568_, 1, v___y_2562_);
v___x_2569_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_2559_, v_localInsts_2560_, v___f_2568_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_);
if (lean_obj_tag(v___x_2569_) == 0)
{
return v___x_2569_;
}
else
{
lean_object* v_a_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2577_; 
v_a_2570_ = lean_ctor_get(v___x_2569_, 0);
v_isSharedCheck_2577_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2577_ == 0)
{
v___x_2572_ = v___x_2569_;
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_a_2570_);
lean_dec(v___x_2569_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v___x_2575_; 
if (v_isShared_2573_ == 0)
{
v___x_2575_ = v___x_2572_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v_a_2570_);
v___x_2575_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
return v___x_2575_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___boxed(lean_object* v_lctx_2578_, lean_object* v_localInsts_2579_, lean_object* v_x_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_){
_start:
{
lean_object* v_res_2587_; 
v_res_2587_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(v_lctx_2578_, v_localInsts_2579_, v_x_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_);
lean_dec(v___y_2585_);
lean_dec_ref(v___y_2584_);
lean_dec(v___y_2583_);
lean_dec_ref(v___y_2582_);
lean_dec(v___y_2581_);
return v_res_2587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0(lean_object* v_00_u03b1_2588_, lean_object* v_00_u03b1_2589_, lean_object* v_lctx_2590_, lean_object* v_localInsts_2591_, lean_object* v_x_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_){
_start:
{
lean_object* v___x_2599_; 
v___x_2599_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(v_lctx_2590_, v_localInsts_2591_, v_x_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_);
return v___x_2599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___boxed(lean_object* v_00_u03b1_2600_, lean_object* v_00_u03b1_2601_, lean_object* v_lctx_2602_, lean_object* v_localInsts_2603_, lean_object* v_x_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_){
_start:
{
lean_object* v_res_2611_; 
v_res_2611_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0(v_00_u03b1_2600_, v_00_u03b1_2601_, v_lctx_2602_, v_localInsts_2603_, v_x_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_);
lean_dec(v___y_2609_);
lean_dec_ref(v___y_2608_);
lean_dec(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec(v___y_2605_);
return v_res_2611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(lean_object* v_e_2612_, lean_object* v___y_2613_){
_start:
{
lean_object* v___x_2615_; lean_object* v_sz_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; 
v___x_2615_ = lean_st_ref_take(v___y_2613_);
v_sz_2616_ = lean_array_get_size(v___x_2615_);
v___x_2617_ = lean_unsigned_to_nat(0u);
v___x_2618_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___x_2619_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2);
v___x_2620_ = lean_unsigned_to_nat(1u);
v___x_2621_ = lean_mk_empty_array_with_capacity(v___x_2620_);
v___x_2622_ = lean_array_push(v___x_2621_, v_e_2612_);
v___x_2623_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2623_, 0, v___x_2618_);
lean_ctor_set(v___x_2623_, 1, v___x_2617_);
lean_ctor_set(v___x_2623_, 2, v___x_2619_);
lean_ctor_set(v___x_2623_, 3, v___x_2622_);
v___x_2624_ = lean_array_push(v___x_2615_, v___x_2623_);
v___x_2625_ = lean_st_ref_put(v___y_2613_, v___x_2624_);
v___x_2626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2626_, 0, v_sz_2616_);
return v___x_2626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg___boxed(lean_object* v_e_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_){
_start:
{
lean_object* v_res_2630_; 
v_res_2630_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v_e_2627_, v___y_2628_);
lean_dec(v___y_2628_);
return v_res_2630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2(lean_object* v_00_u03b1_2631_, lean_object* v_e_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_){
_start:
{
lean_object* v___x_2639_; 
v___x_2639_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v_e_2632_, v___y_2633_);
return v___x_2639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___boxed(lean_object* v_00_u03b1_2640_, lean_object* v_e_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_){
_start:
{
lean_object* v_res_2648_; 
v_res_2648_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2(v_00_u03b1_2640_, v_e_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_);
lean_dec(v___y_2646_);
lean_dec_ref(v___y_2645_);
lean_dec(v___y_2644_);
lean_dec_ref(v___y_2643_);
lean_dec(v___y_2642_);
return v_res_2648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0(uint8_t v___x_2649_, lean_object* v_todo_2650_, lean_object* v_e_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_){
_start:
{
lean_object* v___x_2658_; 
v___x_2658_ = l_Lean_Meta_LazyDiscrTree_pushArgs(v___x_2649_, v_todo_2650_, v_e_2651_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_);
return v___x_2658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0___boxed(lean_object* v___x_2659_, lean_object* v_todo_2660_, lean_object* v_e_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_){
_start:
{
uint8_t v___x_3414__boxed_2668_; lean_object* v_res_2669_; 
v___x_3414__boxed_2668_ = lean_unbox(v___x_2659_);
v_res_2669_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0(v___x_3414__boxed_2668_, v_todo_2660_, v_e_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_);
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2665_);
lean_dec(v___y_2664_);
lean_dec_ref(v___y_2663_);
lean_dec(v___y_2662_);
return v_res_2669_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(lean_object* v_a_2670_, lean_object* v_b_2671_, lean_object* v_x_2672_){
_start:
{
if (lean_obj_tag(v_x_2672_) == 0)
{
lean_dec(v_b_2671_);
lean_dec(v_a_2670_);
return v_x_2672_;
}
else
{
lean_object* v_key_2673_; lean_object* v_value_2674_; lean_object* v_tail_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2687_; 
v_key_2673_ = lean_ctor_get(v_x_2672_, 0);
v_value_2674_ = lean_ctor_get(v_x_2672_, 1);
v_tail_2675_ = lean_ctor_get(v_x_2672_, 2);
v_isSharedCheck_2687_ = !lean_is_exclusive(v_x_2672_);
if (v_isSharedCheck_2687_ == 0)
{
v___x_2677_ = v_x_2672_;
v_isShared_2678_ = v_isSharedCheck_2687_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_tail_2675_);
lean_inc(v_value_2674_);
lean_inc(v_key_2673_);
lean_dec(v_x_2672_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2687_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
uint8_t v___x_2679_; 
v___x_2679_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_2673_, v_a_2670_);
if (v___x_2679_ == 0)
{
lean_object* v___x_2680_; lean_object* v___x_2682_; 
v___x_2680_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(v_a_2670_, v_b_2671_, v_tail_2675_);
if (v_isShared_2678_ == 0)
{
lean_ctor_set(v___x_2677_, 2, v___x_2680_);
v___x_2682_ = v___x_2677_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v_key_2673_);
lean_ctor_set(v_reuseFailAlloc_2683_, 1, v_value_2674_);
lean_ctor_set(v_reuseFailAlloc_2683_, 2, v___x_2680_);
v___x_2682_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
return v___x_2682_;
}
}
else
{
lean_object* v___x_2685_; 
lean_dec(v_value_2674_);
lean_dec(v_key_2673_);
if (v_isShared_2678_ == 0)
{
lean_ctor_set(v___x_2677_, 1, v_b_2671_);
lean_ctor_set(v___x_2677_, 0, v_a_2670_);
v___x_2685_ = v___x_2677_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v_a_2670_);
lean_ctor_set(v_reuseFailAlloc_2686_, 1, v_b_2671_);
lean_ctor_set(v_reuseFailAlloc_2686_, 2, v_tail_2675_);
v___x_2685_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
return v___x_2685_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(lean_object* v_a_2688_, lean_object* v_x_2689_){
_start:
{
if (lean_obj_tag(v_x_2689_) == 0)
{
uint8_t v___x_2690_; 
v___x_2690_ = 0;
return v___x_2690_;
}
else
{
lean_object* v_key_2691_; lean_object* v_tail_2692_; uint8_t v___x_2693_; 
v_key_2691_ = lean_ctor_get(v_x_2689_, 0);
v_tail_2692_ = lean_ctor_get(v_x_2689_, 2);
v___x_2693_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_2691_, v_a_2688_);
if (v___x_2693_ == 0)
{
v_x_2689_ = v_tail_2692_;
goto _start;
}
else
{
return v___x_2693_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg___boxed(lean_object* v_a_2695_, lean_object* v_x_2696_){
_start:
{
uint8_t v_res_2697_; lean_object* v_r_2698_; 
v_res_2697_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(v_a_2695_, v_x_2696_);
lean_dec(v_x_2696_);
lean_dec(v_a_2695_);
v_r_2698_ = lean_box(v_res_2697_);
return v_r_2698_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7___redArg(lean_object* v_x_2699_, lean_object* v_x_2700_){
_start:
{
if (lean_obj_tag(v_x_2700_) == 0)
{
return v_x_2699_;
}
else
{
lean_object* v_key_2701_; lean_object* v_value_2702_; lean_object* v_tail_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2726_; 
v_key_2701_ = lean_ctor_get(v_x_2700_, 0);
v_value_2702_ = lean_ctor_get(v_x_2700_, 1);
v_tail_2703_ = lean_ctor_get(v_x_2700_, 2);
v_isSharedCheck_2726_ = !lean_is_exclusive(v_x_2700_);
if (v_isSharedCheck_2726_ == 0)
{
v___x_2705_ = v_x_2700_;
v_isShared_2706_ = v_isSharedCheck_2726_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_tail_2703_);
lean_inc(v_value_2702_);
lean_inc(v_key_2701_);
lean_dec(v_x_2700_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2726_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v___x_2707_; uint64_t v___x_2708_; uint64_t v___x_2709_; uint64_t v___x_2710_; uint64_t v_fold_2711_; uint64_t v___x_2712_; uint64_t v___x_2713_; uint64_t v___x_2714_; size_t v___x_2715_; size_t v___x_2716_; size_t v___x_2717_; size_t v___x_2718_; size_t v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2722_; 
v___x_2707_ = lean_array_get_size(v_x_2699_);
v___x_2708_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_key_2701_);
v___x_2709_ = 32ULL;
v___x_2710_ = lean_uint64_shift_right(v___x_2708_, v___x_2709_);
v_fold_2711_ = lean_uint64_xor(v___x_2708_, v___x_2710_);
v___x_2712_ = 16ULL;
v___x_2713_ = lean_uint64_shift_right(v_fold_2711_, v___x_2712_);
v___x_2714_ = lean_uint64_xor(v_fold_2711_, v___x_2713_);
v___x_2715_ = lean_uint64_to_usize(v___x_2714_);
v___x_2716_ = lean_usize_of_nat(v___x_2707_);
v___x_2717_ = ((size_t)1ULL);
v___x_2718_ = lean_usize_sub(v___x_2716_, v___x_2717_);
v___x_2719_ = lean_usize_land(v___x_2715_, v___x_2718_);
v___x_2720_ = lean_array_uget_borrowed(v_x_2699_, v___x_2719_);
lean_inc(v___x_2720_);
if (v_isShared_2706_ == 0)
{
lean_ctor_set(v___x_2705_, 2, v___x_2720_);
v___x_2722_ = v___x_2705_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v_key_2701_);
lean_ctor_set(v_reuseFailAlloc_2725_, 1, v_value_2702_);
lean_ctor_set(v_reuseFailAlloc_2725_, 2, v___x_2720_);
v___x_2722_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
lean_object* v___x_2723_; 
v___x_2723_ = lean_array_uset(v_x_2699_, v___x_2719_, v___x_2722_);
v_x_2699_ = v___x_2723_;
v_x_2700_ = v_tail_2703_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6___redArg(lean_object* v_i_2727_, lean_object* v_source_2728_, lean_object* v_target_2729_){
_start:
{
lean_object* v___x_2730_; uint8_t v___x_2731_; 
v___x_2730_ = lean_array_get_size(v_source_2728_);
v___x_2731_ = lean_nat_dec_lt(v_i_2727_, v___x_2730_);
if (v___x_2731_ == 0)
{
lean_dec_ref(v_source_2728_);
lean_dec(v_i_2727_);
return v_target_2729_;
}
else
{
lean_object* v_es_2732_; lean_object* v___x_2733_; lean_object* v_source_2734_; lean_object* v_target_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; 
v_es_2732_ = lean_array_fget(v_source_2728_, v_i_2727_);
v___x_2733_ = lean_box(0);
v_source_2734_ = lean_array_fset(v_source_2728_, v_i_2727_, v___x_2733_);
v_target_2735_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7___redArg(v_target_2729_, v_es_2732_);
v___x_2736_ = lean_unsigned_to_nat(1u);
v___x_2737_ = lean_nat_add(v_i_2727_, v___x_2736_);
lean_dec(v_i_2727_);
v_i_2727_ = v___x_2737_;
v_source_2728_ = v_source_2734_;
v_target_2729_ = v_target_2735_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5___redArg(lean_object* v_data_2739_){
_start:
{
lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v_nbuckets_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; 
v___x_2740_ = lean_array_get_size(v_data_2739_);
v___x_2741_ = lean_unsigned_to_nat(2u);
v_nbuckets_2742_ = lean_nat_mul(v___x_2740_, v___x_2741_);
v___x_2743_ = lean_unsigned_to_nat(0u);
v___x_2744_ = lean_box(0);
v___x_2745_ = lean_mk_array(v_nbuckets_2742_, v___x_2744_);
v___x_2746_ = lean_array_propagate_mark(v_data_2739_, v___x_2745_);
v___x_2747_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6___redArg(v___x_2743_, v_data_2739_, v___x_2746_);
return v___x_2747_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(lean_object* v_m_2748_, lean_object* v_a_2749_, lean_object* v_b_2750_){
_start:
{
lean_object* v_size_2751_; lean_object* v_buckets_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2795_; 
v_size_2751_ = lean_ctor_get(v_m_2748_, 0);
v_buckets_2752_ = lean_ctor_get(v_m_2748_, 1);
v_isSharedCheck_2795_ = !lean_is_exclusive(v_m_2748_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2754_ = v_m_2748_;
v_isShared_2755_ = v_isSharedCheck_2795_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_buckets_2752_);
lean_inc(v_size_2751_);
lean_dec(v_m_2748_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2795_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v___x_2756_; uint64_t v___x_2757_; uint64_t v___x_2758_; uint64_t v___x_2759_; uint64_t v_fold_2760_; uint64_t v___x_2761_; uint64_t v___x_2762_; uint64_t v___x_2763_; size_t v___x_2764_; size_t v___x_2765_; size_t v___x_2766_; size_t v___x_2767_; size_t v___x_2768_; lean_object* v_bkt_2769_; uint8_t v___x_2770_; 
v___x_2756_ = lean_array_get_size(v_buckets_2752_);
v___x_2757_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_a_2749_);
v___x_2758_ = 32ULL;
v___x_2759_ = lean_uint64_shift_right(v___x_2757_, v___x_2758_);
v_fold_2760_ = lean_uint64_xor(v___x_2757_, v___x_2759_);
v___x_2761_ = 16ULL;
v___x_2762_ = lean_uint64_shift_right(v_fold_2760_, v___x_2761_);
v___x_2763_ = lean_uint64_xor(v_fold_2760_, v___x_2762_);
v___x_2764_ = lean_uint64_to_usize(v___x_2763_);
v___x_2765_ = lean_usize_of_nat(v___x_2756_);
v___x_2766_ = ((size_t)1ULL);
v___x_2767_ = lean_usize_sub(v___x_2765_, v___x_2766_);
v___x_2768_ = lean_usize_land(v___x_2764_, v___x_2767_);
v_bkt_2769_ = lean_array_uget_borrowed(v_buckets_2752_, v___x_2768_);
v___x_2770_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(v_a_2749_, v_bkt_2769_);
if (v___x_2770_ == 0)
{
lean_object* v___x_2771_; lean_object* v_size_x27_2772_; lean_object* v___x_2773_; lean_object* v_buckets_x27_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; uint8_t v___x_2780_; 
v___x_2771_ = lean_unsigned_to_nat(1u);
v_size_x27_2772_ = lean_nat_add(v_size_2751_, v___x_2771_);
lean_dec(v_size_2751_);
lean_inc(v_bkt_2769_);
v___x_2773_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2773_, 0, v_a_2749_);
lean_ctor_set(v___x_2773_, 1, v_b_2750_);
lean_ctor_set(v___x_2773_, 2, v_bkt_2769_);
v_buckets_x27_2774_ = lean_array_uset(v_buckets_2752_, v___x_2768_, v___x_2773_);
v___x_2775_ = lean_unsigned_to_nat(4u);
v___x_2776_ = lean_nat_mul(v_size_x27_2772_, v___x_2775_);
v___x_2777_ = lean_unsigned_to_nat(3u);
v___x_2778_ = lean_nat_div(v___x_2776_, v___x_2777_);
lean_dec(v___x_2776_);
v___x_2779_ = lean_array_get_size(v_buckets_x27_2774_);
v___x_2780_ = lean_nat_dec_le(v___x_2778_, v___x_2779_);
lean_dec(v___x_2778_);
if (v___x_2780_ == 0)
{
lean_object* v_val_2781_; lean_object* v___x_2783_; 
v_val_2781_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5___redArg(v_buckets_x27_2774_);
if (v_isShared_2755_ == 0)
{
lean_ctor_set(v___x_2754_, 1, v_val_2781_);
lean_ctor_set(v___x_2754_, 0, v_size_x27_2772_);
v___x_2783_ = v___x_2754_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v_size_x27_2772_);
lean_ctor_set(v_reuseFailAlloc_2784_, 1, v_val_2781_);
v___x_2783_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
return v___x_2783_;
}
}
else
{
lean_object* v___x_2786_; 
if (v_isShared_2755_ == 0)
{
lean_ctor_set(v___x_2754_, 1, v_buckets_x27_2774_);
lean_ctor_set(v___x_2754_, 0, v_size_x27_2772_);
v___x_2786_ = v___x_2754_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v_size_x27_2772_);
lean_ctor_set(v_reuseFailAlloc_2787_, 1, v_buckets_x27_2774_);
v___x_2786_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
return v___x_2786_;
}
}
}
else
{
lean_object* v___x_2788_; lean_object* v_buckets_x27_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2793_; 
lean_inc(v_bkt_2769_);
v___x_2788_ = lean_box(0);
v_buckets_x27_2789_ = lean_array_uset(v_buckets_2752_, v___x_2768_, v___x_2788_);
v___x_2790_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(v_a_2749_, v_b_2750_, v_bkt_2769_);
v___x_2791_ = lean_array_uset(v_buckets_x27_2789_, v___x_2768_, v___x_2790_);
if (v_isShared_2755_ == 0)
{
lean_ctor_set(v___x_2754_, 1, v___x_2791_);
v___x_2793_ = v___x_2754_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_size_2751_);
lean_ctor_set(v_reuseFailAlloc_2794_, 1, v___x_2791_);
v___x_2793_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
return v___x_2793_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(lean_object* v_a_2796_, lean_object* v_x_2797_){
_start:
{
if (lean_obj_tag(v_x_2797_) == 0)
{
lean_object* v___x_2798_; 
v___x_2798_ = lean_box(0);
return v___x_2798_;
}
else
{
lean_object* v_key_2799_; lean_object* v_value_2800_; lean_object* v_tail_2801_; uint8_t v___x_2802_; 
v_key_2799_ = lean_ctor_get(v_x_2797_, 0);
v_value_2800_ = lean_ctor_get(v_x_2797_, 1);
v_tail_2801_ = lean_ctor_get(v_x_2797_, 2);
v___x_2802_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_2799_, v_a_2796_);
if (v___x_2802_ == 0)
{
v_x_2797_ = v_tail_2801_;
goto _start;
}
else
{
lean_object* v___x_2804_; 
lean_inc(v_value_2800_);
v___x_2804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2804_, 0, v_value_2800_);
return v___x_2804_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg___boxed(lean_object* v_a_2805_, lean_object* v_x_2806_){
_start:
{
lean_object* v_res_2807_; 
v_res_2807_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(v_a_2805_, v_x_2806_);
lean_dec(v_x_2806_);
lean_dec(v_a_2805_);
return v_res_2807_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(lean_object* v_m_2808_, lean_object* v_a_2809_){
_start:
{
lean_object* v_buckets_2810_; lean_object* v___x_2811_; uint64_t v___x_2812_; uint64_t v___x_2813_; uint64_t v___x_2814_; uint64_t v_fold_2815_; uint64_t v___x_2816_; uint64_t v___x_2817_; uint64_t v___x_2818_; size_t v___x_2819_; size_t v___x_2820_; size_t v___x_2821_; size_t v___x_2822_; size_t v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; 
v_buckets_2810_ = lean_ctor_get(v_m_2808_, 1);
v___x_2811_ = lean_array_get_size(v_buckets_2810_);
v___x_2812_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_a_2809_);
v___x_2813_ = 32ULL;
v___x_2814_ = lean_uint64_shift_right(v___x_2812_, v___x_2813_);
v_fold_2815_ = lean_uint64_xor(v___x_2812_, v___x_2814_);
v___x_2816_ = 16ULL;
v___x_2817_ = lean_uint64_shift_right(v_fold_2815_, v___x_2816_);
v___x_2818_ = lean_uint64_xor(v_fold_2815_, v___x_2817_);
v___x_2819_ = lean_uint64_to_usize(v___x_2818_);
v___x_2820_ = lean_usize_of_nat(v___x_2811_);
v___x_2821_ = ((size_t)1ULL);
v___x_2822_ = lean_usize_sub(v___x_2820_, v___x_2821_);
v___x_2823_ = lean_usize_land(v___x_2819_, v___x_2822_);
v___x_2824_ = lean_array_uget_borrowed(v_buckets_2810_, v___x_2823_);
v___x_2825_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(v_a_2809_, v___x_2824_);
return v___x_2825_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg___boxed(lean_object* v_m_2826_, lean_object* v_a_2827_){
_start:
{
lean_object* v_res_2828_; 
v_res_2828_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_m_2826_, v_a_2827_);
lean_dec(v_a_2827_);
lean_dec_ref(v_m_2826_);
return v_res_2828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(lean_object* v_p_2829_, lean_object* v_entry_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_){
_start:
{
lean_object* v_snd_2837_; lean_object* v_snd_2838_; lean_object* v_fst_2839_; lean_object* v_fst_2840_; lean_object* v_snd_2841_; lean_object* v_fst_2842_; lean_object* v_fst_2843_; lean_object* v_snd_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; uint8_t v___x_2847_; 
v_snd_2837_ = lean_ctor_get(v_p_2829_, 1);
v_snd_2838_ = lean_ctor_get(v_entry_2830_, 1);
lean_inc(v_snd_2838_);
v_fst_2839_ = lean_ctor_get(v_p_2829_, 0);
v_fst_2840_ = lean_ctor_get(v_snd_2837_, 0);
v_snd_2841_ = lean_ctor_get(v_snd_2837_, 1);
v_fst_2842_ = lean_ctor_get(v_entry_2830_, 0);
lean_inc(v_fst_2842_);
lean_dec_ref(v_entry_2830_);
v_fst_2843_ = lean_ctor_get(v_snd_2838_, 0);
lean_inc(v_fst_2843_);
v_snd_2844_ = lean_ctor_get(v_snd_2838_, 1);
v___x_2845_ = lean_array_get_size(v_fst_2842_);
v___x_2846_ = lean_unsigned_to_nat(0u);
v___x_2847_ = lean_nat_dec_eq(v___x_2845_, v___x_2846_);
if (v___x_2847_ == 0)
{
lean_object* v_fst_2848_; lean_object* v_snd_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2954_; 
v_fst_2848_ = lean_ctor_get(v_fst_2843_, 0);
v_snd_2849_ = lean_ctor_get(v_fst_2843_, 1);
v_isSharedCheck_2954_ = !lean_is_exclusive(v_fst_2843_);
if (v_isSharedCheck_2954_ == 0)
{
v___x_2851_ = v_fst_2843_;
v_isShared_2852_ = v_isSharedCheck_2954_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_snd_2849_);
lean_inc(v_fst_2848_);
lean_dec(v_fst_2843_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2954_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v_e_2856_; lean_object* v_todo_2857_; lean_object* v___x_2858_; lean_object* v___f_2859_; lean_object* v___x_2860_; 
v___x_2853_ = l_Lean_instInhabitedExpr;
v___x_2854_ = lean_unsigned_to_nat(1u);
v___x_2855_ = lean_nat_sub(v___x_2845_, v___x_2854_);
v_e_2856_ = lean_array_get(v___x_2853_, v_fst_2842_, v___x_2855_);
lean_dec(v___x_2855_);
v_todo_2857_ = lean_array_pop(v_fst_2842_);
v___x_2858_ = lean_box(v___x_2847_);
v___f_2859_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2859_, 0, v___x_2858_);
lean_closure_set(v___f_2859_, 1, v_todo_2857_);
lean_closure_set(v___f_2859_, 2, v_e_2856_);
v___x_2860_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(v_fst_2848_, v_snd_2849_, v___f_2859_, v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_);
if (lean_obj_tag(v___x_2860_) == 0)
{
lean_object* v_a_2861_; lean_object* v_fst_2862_; lean_object* v_snd_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2945_; 
v_a_2861_ = lean_ctor_get(v___x_2860_, 0);
lean_inc(v_a_2861_);
lean_dec_ref_known(v___x_2860_, 1);
v_fst_2862_ = lean_ctor_get(v_a_2861_, 0);
v_snd_2863_ = lean_ctor_get(v_a_2861_, 1);
v_isSharedCheck_2945_ = !lean_is_exclusive(v_a_2861_);
if (v_isSharedCheck_2945_ == 0)
{
v___x_2865_ = v_a_2861_;
v_isShared_2866_ = v_isSharedCheck_2945_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_snd_2863_);
lean_inc(v_fst_2862_);
lean_dec(v_a_2861_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2945_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2867_; uint8_t v___x_2868_; 
v___x_2867_ = lean_box(3);
v___x_2868_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_fst_2862_, v___x_2867_);
if (v___x_2868_ == 0)
{
lean_object* v___x_2869_; 
v___x_2869_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_snd_2841_, v_fst_2862_);
if (lean_obj_tag(v___x_2869_) == 0)
{
lean_object* v___x_2871_; 
lean_inc(v_snd_2841_);
lean_inc(v_fst_2840_);
lean_inc(v_fst_2839_);
lean_dec_ref(v_p_2829_);
lean_inc(v_snd_2838_);
if (v_isShared_2866_ == 0)
{
lean_ctor_set(v___x_2865_, 1, v_snd_2838_);
lean_ctor_set(v___x_2865_, 0, v_snd_2863_);
v___x_2871_ = v___x_2865_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v_snd_2863_);
lean_ctor_set(v_reuseFailAlloc_2894_, 1, v_snd_2838_);
v___x_2871_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2891_; 
v_isSharedCheck_2891_ = !lean_is_exclusive(v_snd_2838_);
if (v_isSharedCheck_2891_ == 0)
{
lean_object* v_unused_2892_; lean_object* v_unused_2893_; 
v_unused_2892_ = lean_ctor_get(v_snd_2838_, 1);
lean_dec(v_unused_2892_);
v_unused_2893_ = lean_ctor_get(v_snd_2838_, 0);
lean_dec(v_unused_2893_);
v___x_2873_ = v_snd_2838_;
v_isShared_2874_ = v_isSharedCheck_2891_;
goto v_resetjp_2872_;
}
else
{
lean_dec(v_snd_2838_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2891_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
lean_object* v___x_2875_; lean_object* v_a_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2890_; 
v___x_2875_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v___x_2871_, v_a_2831_);
v_a_2876_ = lean_ctor_get(v___x_2875_, 0);
v_isSharedCheck_2890_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_2890_ == 0)
{
v___x_2878_ = v___x_2875_;
v_isShared_2879_ = v_isSharedCheck_2890_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_a_2876_);
lean_dec(v___x_2875_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2890_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v___x_2880_; lean_object* v___x_2882_; 
v___x_2880_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_snd_2841_, v_fst_2862_, v_a_2876_);
if (v_isShared_2852_ == 0)
{
lean_ctor_set(v___x_2851_, 1, v___x_2880_);
lean_ctor_set(v___x_2851_, 0, v_fst_2840_);
v___x_2882_ = v___x_2851_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v_fst_2840_);
lean_ctor_set(v_reuseFailAlloc_2889_, 1, v___x_2880_);
v___x_2882_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
lean_object* v___x_2884_; 
if (v_isShared_2874_ == 0)
{
lean_ctor_set(v___x_2873_, 1, v___x_2882_);
lean_ctor_set(v___x_2873_, 0, v_fst_2839_);
v___x_2884_ = v___x_2873_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v_fst_2839_);
lean_ctor_set(v_reuseFailAlloc_2888_, 1, v___x_2882_);
v___x_2884_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
lean_object* v___x_2886_; 
if (v_isShared_2879_ == 0)
{
lean_ctor_set(v___x_2878_, 0, v___x_2884_);
v___x_2886_ = v___x_2878_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v___x_2884_);
v___x_2886_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
return v___x_2886_;
}
}
}
}
}
}
}
else
{
lean_object* v_val_2895_; lean_object* v___x_2897_; 
lean_dec(v_fst_2862_);
lean_del_object(v___x_2851_);
v_val_2895_ = lean_ctor_get(v___x_2869_, 0);
lean_inc(v_val_2895_);
lean_dec_ref_known(v___x_2869_, 1);
if (v_isShared_2866_ == 0)
{
lean_ctor_set(v___x_2865_, 1, v_snd_2838_);
lean_ctor_set(v___x_2865_, 0, v_snd_2863_);
v___x_2897_ = v___x_2865_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v_snd_2863_);
lean_ctor_set(v_reuseFailAlloc_2907_, 1, v_snd_2838_);
v___x_2897_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
lean_object* v___x_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2905_; 
v___x_2898_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_val_2895_, v___x_2897_, v_a_2831_);
lean_dec(v_val_2895_);
v_isSharedCheck_2905_ = !lean_is_exclusive(v___x_2898_);
if (v_isSharedCheck_2905_ == 0)
{
lean_object* v_unused_2906_; 
v_unused_2906_ = lean_ctor_get(v___x_2898_, 0);
lean_dec(v_unused_2906_);
v___x_2900_ = v___x_2898_;
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
else
{
lean_dec(v___x_2898_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
lean_object* v___x_2903_; 
if (v_isShared_2901_ == 0)
{
lean_ctor_set(v___x_2900_, 0, v_p_2829_);
v___x_2903_ = v___x_2900_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v_p_2829_);
v___x_2903_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
return v___x_2903_;
}
}
}
}
}
else
{
uint8_t v___x_2908_; 
lean_dec(v_fst_2862_);
v___x_2908_ = lean_nat_dec_eq(v_fst_2840_, v___x_2846_);
if (v___x_2908_ == 0)
{
lean_object* v___x_2910_; 
lean_del_object(v___x_2851_);
if (v_isShared_2866_ == 0)
{
lean_ctor_set(v___x_2865_, 1, v_snd_2838_);
lean_ctor_set(v___x_2865_, 0, v_snd_2863_);
v___x_2910_ = v___x_2865_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v_snd_2863_);
lean_ctor_set(v_reuseFailAlloc_2920_, 1, v_snd_2838_);
v___x_2910_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
lean_object* v___x_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2918_; 
v___x_2911_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_fst_2840_, v___x_2910_, v_a_2831_);
v_isSharedCheck_2918_ = !lean_is_exclusive(v___x_2911_);
if (v_isSharedCheck_2918_ == 0)
{
lean_object* v_unused_2919_; 
v_unused_2919_ = lean_ctor_get(v___x_2911_, 0);
lean_dec(v_unused_2919_);
v___x_2913_ = v___x_2911_;
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
else
{
lean_dec(v___x_2911_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v___x_2916_; 
if (v_isShared_2914_ == 0)
{
lean_ctor_set(v___x_2913_, 0, v_p_2829_);
v___x_2916_ = v___x_2913_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v_p_2829_);
v___x_2916_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
return v___x_2916_;
}
}
}
}
else
{
lean_object* v___x_2922_; 
lean_inc(v_snd_2841_);
lean_inc(v_fst_2839_);
lean_dec_ref(v_p_2829_);
lean_inc(v_snd_2838_);
if (v_isShared_2866_ == 0)
{
lean_ctor_set(v___x_2865_, 1, v_snd_2838_);
lean_ctor_set(v___x_2865_, 0, v_snd_2863_);
v___x_2922_ = v___x_2865_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v_snd_2863_);
lean_ctor_set(v_reuseFailAlloc_2944_, 1, v_snd_2838_);
v___x_2922_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2941_; 
v_isSharedCheck_2941_ = !lean_is_exclusive(v_snd_2838_);
if (v_isSharedCheck_2941_ == 0)
{
lean_object* v_unused_2942_; lean_object* v_unused_2943_; 
v_unused_2942_ = lean_ctor_get(v_snd_2838_, 1);
lean_dec(v_unused_2942_);
v_unused_2943_ = lean_ctor_get(v_snd_2838_, 0);
lean_dec(v_unused_2943_);
v___x_2924_ = v_snd_2838_;
v_isShared_2925_ = v_isSharedCheck_2941_;
goto v_resetjp_2923_;
}
else
{
lean_dec(v_snd_2838_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2941_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v___x_2926_; lean_object* v_a_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2940_; 
v___x_2926_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v___x_2922_, v_a_2831_);
v_a_2927_ = lean_ctor_get(v___x_2926_, 0);
v_isSharedCheck_2940_ = !lean_is_exclusive(v___x_2926_);
if (v_isSharedCheck_2940_ == 0)
{
v___x_2929_ = v___x_2926_;
v_isShared_2930_ = v_isSharedCheck_2940_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_a_2927_);
lean_dec(v___x_2926_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2940_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v___x_2932_; 
if (v_isShared_2852_ == 0)
{
lean_ctor_set(v___x_2851_, 1, v_snd_2841_);
lean_ctor_set(v___x_2851_, 0, v_a_2927_);
v___x_2932_ = v___x_2851_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v_a_2927_);
lean_ctor_set(v_reuseFailAlloc_2939_, 1, v_snd_2841_);
v___x_2932_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
lean_object* v___x_2934_; 
if (v_isShared_2925_ == 0)
{
lean_ctor_set(v___x_2924_, 1, v___x_2932_);
lean_ctor_set(v___x_2924_, 0, v_fst_2839_);
v___x_2934_ = v___x_2924_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v_fst_2839_);
lean_ctor_set(v_reuseFailAlloc_2938_, 1, v___x_2932_);
v___x_2934_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
lean_object* v___x_2936_; 
if (v_isShared_2930_ == 0)
{
lean_ctor_set(v___x_2929_, 0, v___x_2934_);
v___x_2936_ = v___x_2929_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_2937_; 
v_reuseFailAlloc_2937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2937_, 0, v___x_2934_);
v___x_2936_ = v_reuseFailAlloc_2937_;
goto v_reusejp_2935_;
}
v_reusejp_2935_:
{
return v___x_2936_;
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
lean_object* v_a_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_2953_; 
lean_del_object(v___x_2851_);
lean_dec(v_snd_2838_);
lean_dec_ref(v_p_2829_);
v_a_2946_ = lean_ctor_get(v___x_2860_, 0);
v_isSharedCheck_2953_ = !lean_is_exclusive(v___x_2860_);
if (v_isSharedCheck_2953_ == 0)
{
v___x_2948_ = v___x_2860_;
v_isShared_2949_ = v_isSharedCheck_2953_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_a_2946_);
lean_dec(v___x_2860_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_2953_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
lean_object* v___x_2951_; 
if (v_isShared_2949_ == 0)
{
v___x_2951_ = v___x_2948_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_a_2946_);
v___x_2951_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
return v___x_2951_;
}
}
}
}
}
else
{
lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2963_; 
lean_inc(v_snd_2844_);
lean_inc(v_fst_2839_);
lean_inc(v_snd_2837_);
lean_dec(v_fst_2843_);
lean_dec(v_fst_2842_);
lean_dec_ref(v_p_2829_);
v_isSharedCheck_2963_ = !lean_is_exclusive(v_snd_2838_);
if (v_isSharedCheck_2963_ == 0)
{
lean_object* v_unused_2964_; lean_object* v_unused_2965_; 
v_unused_2964_ = lean_ctor_get(v_snd_2838_, 1);
lean_dec(v_unused_2964_);
v_unused_2965_ = lean_ctor_get(v_snd_2838_, 0);
lean_dec(v_unused_2965_);
v___x_2956_ = v_snd_2838_;
v_isShared_2957_ = v_isSharedCheck_2963_;
goto v_resetjp_2955_;
}
else
{
lean_dec(v_snd_2838_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_2963_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v_values_2958_; lean_object* v___x_2960_; 
v_values_2958_ = lean_array_push(v_fst_2839_, v_snd_2844_);
if (v_isShared_2957_ == 0)
{
lean_ctor_set(v___x_2956_, 1, v_snd_2837_);
lean_ctor_set(v___x_2956_, 0, v_values_2958_);
v___x_2960_ = v___x_2956_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2962_; 
v_reuseFailAlloc_2962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2962_, 0, v_values_2958_);
lean_ctor_set(v_reuseFailAlloc_2962_, 1, v_snd_2837_);
v___x_2960_ = v_reuseFailAlloc_2962_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
lean_object* v___x_2961_; 
v___x_2961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2961_, 0, v___x_2960_);
return v___x_2961_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___boxed(lean_object* v_p_2966_, lean_object* v_entry_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_){
_start:
{
lean_object* v_res_2974_; 
v_res_2974_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(v_p_2966_, v_entry_2967_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_);
lean_dec(v_a_2972_);
lean_dec_ref(v_a_2971_);
lean_dec(v_a_2970_);
lean_dec_ref(v_a_2969_);
lean_dec(v_a_2968_);
return v_res_2974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry(lean_object* v_00_u03b1_2975_, lean_object* v_p_2976_, lean_object* v_entry_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_){
_start:
{
lean_object* v___x_2984_; 
v___x_2984_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(v_p_2976_, v_entry_2977_, v_a_2978_, v_a_2979_, v_a_2980_, v_a_2981_, v_a_2982_);
return v___x_2984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___boxed(lean_object* v_00_u03b1_2985_, lean_object* v_p_2986_, lean_object* v_entry_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_){
_start:
{
lean_object* v_res_2994_; 
v_res_2994_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry(v_00_u03b1_2985_, v_p_2986_, v_entry_2987_, v_a_2988_, v_a_2989_, v_a_2990_, v_a_2991_, v_a_2992_);
lean_dec(v_a_2992_);
lean_dec_ref(v_a_2991_);
lean_dec(v_a_2990_);
lean_dec_ref(v_a_2989_);
lean_dec(v_a_2988_);
return v_res_2994_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1(lean_object* v_00_u03b2_2995_, lean_object* v_m_2996_, lean_object* v_a_2997_){
_start:
{
lean_object* v___x_2998_; 
v___x_2998_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_m_2996_, v_a_2997_);
return v___x_2998_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___boxed(lean_object* v_00_u03b2_2999_, lean_object* v_m_3000_, lean_object* v_a_3001_){
_start:
{
lean_object* v_res_3002_; 
v_res_3002_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1(v_00_u03b2_2999_, v_m_3000_, v_a_3001_);
lean_dec(v_a_3001_);
lean_dec_ref(v_m_3000_);
return v_res_3002_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3(lean_object* v_00_u03b2_3003_, lean_object* v_m_3004_, lean_object* v_a_3005_, lean_object* v_b_3006_){
_start:
{
lean_object* v___x_3007_; 
v___x_3007_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_m_3004_, v_a_3005_, v_b_3006_);
return v___x_3007_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1(lean_object* v_00_u03b2_3008_, lean_object* v_a_3009_, lean_object* v_x_3010_){
_start:
{
lean_object* v___x_3011_; 
v___x_3011_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(v_a_3009_, v_x_3010_);
return v___x_3011_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___boxed(lean_object* v_00_u03b2_3012_, lean_object* v_a_3013_, lean_object* v_x_3014_){
_start:
{
lean_object* v_res_3015_; 
v_res_3015_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1(v_00_u03b2_3012_, v_a_3013_, v_x_3014_);
lean_dec(v_x_3014_);
lean_dec(v_a_3013_);
return v_res_3015_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4(lean_object* v_00_u03b2_3016_, lean_object* v_a_3017_, lean_object* v_x_3018_){
_start:
{
uint8_t v___x_3019_; 
v___x_3019_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(v_a_3017_, v_x_3018_);
return v___x_3019_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___boxed(lean_object* v_00_u03b2_3020_, lean_object* v_a_3021_, lean_object* v_x_3022_){
_start:
{
uint8_t v_res_3023_; lean_object* v_r_3024_; 
v_res_3023_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4(v_00_u03b2_3020_, v_a_3021_, v_x_3022_);
lean_dec(v_x_3022_);
lean_dec(v_a_3021_);
v_r_3024_ = lean_box(v_res_3023_);
return v_r_3024_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5(lean_object* v_00_u03b2_3025_, lean_object* v_data_3026_){
_start:
{
lean_object* v___x_3027_; 
v___x_3027_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5___redArg(v_data_3026_);
return v___x_3027_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6(lean_object* v_00_u03b2_3028_, lean_object* v_a_3029_, lean_object* v_b_3030_, lean_object* v_x_3031_){
_start:
{
lean_object* v___x_3032_; 
v___x_3032_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(v_a_3029_, v_b_3030_, v_x_3031_);
return v___x_3032_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_3033_, lean_object* v_i_3034_, lean_object* v_source_3035_, lean_object* v_target_3036_){
_start:
{
lean_object* v___x_3037_; 
v___x_3037_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6___redArg(v_i_3034_, v_source_3035_, v_target_3036_);
return v___x_3037_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_3038_, lean_object* v_x_3039_, lean_object* v_x_3040_){
_start:
{
lean_object* v___x_3041_; 
v___x_3041_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7___redArg(v_x_3039_, v_x_3040_);
return v___x_3041_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(lean_object* v_as_3042_, size_t v_i_3043_, size_t v_stop_3044_, lean_object* v_b_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_){
_start:
{
uint8_t v___x_3052_; 
v___x_3052_ = lean_usize_dec_eq(v_i_3043_, v_stop_3044_);
if (v___x_3052_ == 0)
{
lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___x_3053_ = lean_array_uget_borrowed(v_as_3042_, v_i_3043_);
lean_inc(v___x_3053_);
v___x_3054_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(v_b_3045_, v___x_3053_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_);
if (lean_obj_tag(v___x_3054_) == 0)
{
lean_object* v_a_3055_; size_t v___x_3056_; size_t v___x_3057_; 
v_a_3055_ = lean_ctor_get(v___x_3054_, 0);
lean_inc(v_a_3055_);
lean_dec_ref_known(v___x_3054_, 1);
v___x_3056_ = ((size_t)1ULL);
v___x_3057_ = lean_usize_add(v_i_3043_, v___x_3056_);
v_i_3043_ = v___x_3057_;
v_b_3045_ = v_a_3055_;
goto _start;
}
else
{
return v___x_3054_;
}
}
else
{
lean_object* v___x_3059_; 
v___x_3059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3059_, 0, v_b_3045_);
return v___x_3059_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg___boxed(lean_object* v_as_3060_, lean_object* v_i_3061_, lean_object* v_stop_3062_, lean_object* v_b_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_){
_start:
{
size_t v_i_boxed_3070_; size_t v_stop_boxed_3071_; lean_object* v_res_3072_; 
v_i_boxed_3070_ = lean_unbox_usize(v_i_3061_);
lean_dec(v_i_3061_);
v_stop_boxed_3071_ = lean_unbox_usize(v_stop_3062_);
lean_dec(v_stop_3062_);
v_res_3072_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_as_3060_, v_i_boxed_3070_, v_stop_boxed_3071_, v_b_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_);
lean_dec(v___y_3068_);
lean_dec_ref(v___y_3067_);
lean_dec(v___y_3066_);
lean_dec_ref(v___y_3065_);
lean_dec(v___y_3064_);
lean_dec_ref(v_as_3060_);
return v_res_3072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(lean_object* v_values_3073_, lean_object* v_starIdx_3074_, lean_object* v_children_3075_, lean_object* v_entries_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_){
_start:
{
lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; uint8_t v___x_3087_; 
v___x_3083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3083_, 0, v_starIdx_3074_);
lean_ctor_set(v___x_3083_, 1, v_children_3075_);
v___x_3084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3084_, 0, v_values_3073_);
lean_ctor_set(v___x_3084_, 1, v___x_3083_);
v___x_3085_ = lean_unsigned_to_nat(0u);
v___x_3086_ = lean_array_get_size(v_entries_3076_);
v___x_3087_ = lean_nat_dec_lt(v___x_3085_, v___x_3086_);
if (v___x_3087_ == 0)
{
lean_object* v___x_3088_; 
v___x_3088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3088_, 0, v___x_3084_);
return v___x_3088_;
}
else
{
uint8_t v___x_3089_; 
v___x_3089_ = lean_nat_dec_le(v___x_3086_, v___x_3086_);
if (v___x_3089_ == 0)
{
if (v___x_3087_ == 0)
{
lean_object* v___x_3090_; 
v___x_3090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3090_, 0, v___x_3084_);
return v___x_3090_;
}
else
{
size_t v___x_3091_; size_t v___x_3092_; lean_object* v___x_3093_; 
v___x_3091_ = ((size_t)0ULL);
v___x_3092_ = lean_usize_of_nat(v___x_3086_);
v___x_3093_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_entries_3076_, v___x_3091_, v___x_3092_, v___x_3084_, v_a_3077_, v_a_3078_, v_a_3079_, v_a_3080_, v_a_3081_);
return v___x_3093_;
}
}
else
{
size_t v___x_3094_; size_t v___x_3095_; lean_object* v___x_3096_; 
v___x_3094_ = ((size_t)0ULL);
v___x_3095_ = lean_usize_of_nat(v___x_3086_);
v___x_3096_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_entries_3076_, v___x_3094_, v___x_3095_, v___x_3084_, v_a_3077_, v_a_3078_, v_a_3079_, v_a_3080_, v_a_3081_);
return v___x_3096_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg___boxed(lean_object* v_values_3097_, lean_object* v_starIdx_3098_, lean_object* v_children_3099_, lean_object* v_entries_3100_, lean_object* v_a_3101_, lean_object* v_a_3102_, lean_object* v_a_3103_, lean_object* v_a_3104_, lean_object* v_a_3105_, lean_object* v_a_3106_){
_start:
{
lean_object* v_res_3107_; 
v_res_3107_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(v_values_3097_, v_starIdx_3098_, v_children_3099_, v_entries_3100_, v_a_3101_, v_a_3102_, v_a_3103_, v_a_3104_, v_a_3105_);
lean_dec(v_a_3105_);
lean_dec_ref(v_a_3104_);
lean_dec(v_a_3103_);
lean_dec_ref(v_a_3102_);
lean_dec(v_a_3101_);
lean_dec_ref(v_entries_3100_);
return v_res_3107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries(lean_object* v_00_u03b1_3108_, lean_object* v_values_3109_, lean_object* v_starIdx_3110_, lean_object* v_children_3111_, lean_object* v_entries_3112_, lean_object* v_a_3113_, lean_object* v_a_3114_, lean_object* v_a_3115_, lean_object* v_a_3116_, lean_object* v_a_3117_){
_start:
{
lean_object* v___x_3119_; 
v___x_3119_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(v_values_3109_, v_starIdx_3110_, v_children_3111_, v_entries_3112_, v_a_3113_, v_a_3114_, v_a_3115_, v_a_3116_, v_a_3117_);
return v___x_3119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries___boxed(lean_object* v_00_u03b1_3120_, lean_object* v_values_3121_, lean_object* v_starIdx_3122_, lean_object* v_children_3123_, lean_object* v_entries_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_, lean_object* v_a_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_){
_start:
{
lean_object* v_res_3131_; 
v_res_3131_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries(v_00_u03b1_3120_, v_values_3121_, v_starIdx_3122_, v_children_3123_, v_entries_3124_, v_a_3125_, v_a_3126_, v_a_3127_, v_a_3128_, v_a_3129_);
lean_dec(v_a_3129_);
lean_dec_ref(v_a_3128_);
lean_dec(v_a_3127_);
lean_dec_ref(v_a_3126_);
lean_dec(v_a_3125_);
lean_dec_ref(v_entries_3124_);
return v_res_3131_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0(lean_object* v_00_u03b1_3132_, lean_object* v_as_3133_, size_t v_i_3134_, size_t v_stop_3135_, lean_object* v_b_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_){
_start:
{
lean_object* v___x_3143_; 
v___x_3143_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_as_3133_, v_i_3134_, v_stop_3135_, v_b_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_);
return v___x_3143_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___boxed(lean_object* v_00_u03b1_3144_, lean_object* v_as_3145_, lean_object* v_i_3146_, lean_object* v_stop_3147_, lean_object* v_b_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_){
_start:
{
size_t v_i_boxed_3155_; size_t v_stop_boxed_3156_; lean_object* v_res_3157_; 
v_i_boxed_3155_ = lean_unbox_usize(v_i_3146_);
lean_dec(v_i_3146_);
v_stop_boxed_3156_ = lean_unbox_usize(v_stop_3147_);
lean_dec(v_stop_3147_);
v_res_3157_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0(v_00_u03b1_3144_, v_as_3145_, v_i_boxed_3155_, v_stop_boxed_3156_, v_b_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_);
lean_dec(v___y_3153_);
lean_dec_ref(v___y_3152_);
lean_dec(v___y_3151_);
lean_dec_ref(v___y_3150_);
lean_dec(v___y_3149_);
lean_dec_ref(v_as_3145_);
return v_res_3157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode___redArg(lean_object* v_c_3158_, lean_object* v_a_3159_, lean_object* v_a_3160_, lean_object* v_a_3161_, lean_object* v_a_3162_, lean_object* v_a_3163_){
_start:
{
lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v_values_3168_; lean_object* v_star_3169_; lean_object* v_children_3170_; lean_object* v_pending_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3201_; 
v___x_3165_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0);
v___x_3166_ = lean_st_ref_get(v_a_3159_);
v___x_3167_ = lean_array_get(v___x_3165_, v___x_3166_, v_c_3158_);
lean_dec(v___x_3166_);
v_values_3168_ = lean_ctor_get(v___x_3167_, 0);
v_star_3169_ = lean_ctor_get(v___x_3167_, 1);
v_children_3170_ = lean_ctor_get(v___x_3167_, 2);
v_pending_3171_ = lean_ctor_get(v___x_3167_, 3);
v_isSharedCheck_3201_ = !lean_is_exclusive(v___x_3167_);
if (v_isSharedCheck_3201_ == 0)
{
v___x_3173_ = v___x_3167_;
v_isShared_3174_ = v_isSharedCheck_3201_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_pending_3171_);
lean_inc(v_children_3170_);
lean_inc(v_star_3169_);
lean_inc(v_values_3168_);
lean_dec(v___x_3167_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3201_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
lean_object* v___x_3175_; lean_object* v___x_3176_; uint8_t v___x_3177_; 
v___x_3175_ = lean_array_get_size(v_pending_3171_);
v___x_3176_ = lean_unsigned_to_nat(0u);
v___x_3177_ = lean_nat_dec_eq(v___x_3175_, v___x_3176_);
if (v___x_3177_ == 0)
{
lean_object* v___x_3178_; lean_object* v___x_3179_; 
v___x_3178_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_c_3158_, v___x_3165_, v_a_3159_);
lean_dec_ref(v___x_3178_);
v___x_3179_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(v_values_3168_, v_star_3169_, v_children_3170_, v_pending_3171_, v_a_3159_, v_a_3160_, v_a_3161_, v_a_3162_, v_a_3163_);
lean_dec_ref(v_pending_3171_);
if (lean_obj_tag(v___x_3179_) == 0)
{
lean_object* v_a_3180_; lean_object* v_snd_3181_; lean_object* v_fst_3182_; lean_object* v_fst_3183_; lean_object* v_snd_3184_; lean_object* v___x_3185_; lean_object* v___x_3187_; 
v_a_3180_ = lean_ctor_get(v___x_3179_, 0);
lean_inc(v_a_3180_);
lean_dec_ref_known(v___x_3179_, 1);
v_snd_3181_ = lean_ctor_get(v_a_3180_, 1);
v_fst_3182_ = lean_ctor_get(v_a_3180_, 0);
v_fst_3183_ = lean_ctor_get(v_snd_3181_, 0);
v_snd_3184_ = lean_ctor_get(v_snd_3181_, 1);
v___x_3185_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__3));
lean_inc(v_snd_3184_);
lean_inc(v_fst_3183_);
lean_inc(v_fst_3182_);
if (v_isShared_3174_ == 0)
{
lean_ctor_set(v___x_3173_, 3, v___x_3185_);
lean_ctor_set(v___x_3173_, 2, v_snd_3184_);
lean_ctor_set(v___x_3173_, 1, v_fst_3183_);
lean_ctor_set(v___x_3173_, 0, v_fst_3182_);
v___x_3187_ = v___x_3173_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v_fst_3182_);
lean_ctor_set(v_reuseFailAlloc_3197_, 1, v_fst_3183_);
lean_ctor_set(v_reuseFailAlloc_3197_, 2, v_snd_3184_);
lean_ctor_set(v_reuseFailAlloc_3197_, 3, v___x_3185_);
v___x_3187_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
lean_object* v___x_3188_; lean_object* v___x_3190_; uint8_t v_isShared_3191_; uint8_t v_isSharedCheck_3195_; 
v___x_3188_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_c_3158_, v___x_3187_, v_a_3159_);
v_isSharedCheck_3195_ = !lean_is_exclusive(v___x_3188_);
if (v_isSharedCheck_3195_ == 0)
{
lean_object* v_unused_3196_; 
v_unused_3196_ = lean_ctor_get(v___x_3188_, 0);
lean_dec(v_unused_3196_);
v___x_3190_ = v___x_3188_;
v_isShared_3191_ = v_isSharedCheck_3195_;
goto v_resetjp_3189_;
}
else
{
lean_dec(v___x_3188_);
v___x_3190_ = lean_box(0);
v_isShared_3191_ = v_isSharedCheck_3195_;
goto v_resetjp_3189_;
}
v_resetjp_3189_:
{
lean_object* v___x_3193_; 
if (v_isShared_3191_ == 0)
{
lean_ctor_set(v___x_3190_, 0, v_a_3180_);
v___x_3193_ = v___x_3190_;
goto v_reusejp_3192_;
}
else
{
lean_object* v_reuseFailAlloc_3194_; 
v_reuseFailAlloc_3194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3194_, 0, v_a_3180_);
v___x_3193_ = v_reuseFailAlloc_3194_;
goto v_reusejp_3192_;
}
v_reusejp_3192_:
{
return v___x_3193_;
}
}
}
}
else
{
lean_del_object(v___x_3173_);
return v___x_3179_;
}
}
else
{
lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; 
lean_del_object(v___x_3173_);
lean_dec_ref(v_pending_3171_);
v___x_3198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3198_, 0, v_star_3169_);
lean_ctor_set(v___x_3198_, 1, v_children_3170_);
v___x_3199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3199_, 0, v_values_3168_);
lean_ctor_set(v___x_3199_, 1, v___x_3198_);
v___x_3200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3200_, 0, v___x_3199_);
return v___x_3200_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode___redArg___boxed(lean_object* v_c_3202_, lean_object* v_a_3203_, lean_object* v_a_3204_, lean_object* v_a_3205_, lean_object* v_a_3206_, lean_object* v_a_3207_, lean_object* v_a_3208_){
_start:
{
lean_object* v_res_3209_; 
v_res_3209_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_c_3202_, v_a_3203_, v_a_3204_, v_a_3205_, v_a_3206_, v_a_3207_);
lean_dec(v_a_3207_);
lean_dec_ref(v_a_3206_);
lean_dec(v_a_3205_);
lean_dec_ref(v_a_3204_);
lean_dec(v_a_3203_);
lean_dec(v_c_3202_);
return v_res_3209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode(lean_object* v_00_u03b1_3210_, lean_object* v_c_3211_, lean_object* v_a_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_, lean_object* v_a_3215_, lean_object* v_a_3216_){
_start:
{
lean_object* v___x_3218_; 
v___x_3218_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_c_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_);
return v___x_3218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode___boxed(lean_object* v_00_u03b1_3219_, lean_object* v_c_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_){
_start:
{
lean_object* v_res_3227_; 
v_res_3227_ = l_Lean_Meta_LazyDiscrTree_evalNode(v_00_u03b1_3219_, v_c_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_);
lean_dec(v_a_3225_);
lean_dec_ref(v_a_3224_);
lean_dec(v_a_3223_);
lean_dec_ref(v_a_3222_);
lean_dec(v_a_3221_);
lean_dec(v_c_3220_);
return v_res_3227_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(lean_object* v_a_3228_, lean_object* v_fallback_3229_, lean_object* v_x_3230_){
_start:
{
if (lean_obj_tag(v_x_3230_) == 0)
{
lean_inc(v_fallback_3229_);
return v_fallback_3229_;
}
else
{
lean_object* v_key_3231_; lean_object* v_value_3232_; lean_object* v_tail_3233_; uint8_t v___x_3234_; 
v_key_3231_ = lean_ctor_get(v_x_3230_, 0);
v_value_3232_ = lean_ctor_get(v_x_3230_, 1);
v_tail_3233_ = lean_ctor_get(v_x_3230_, 2);
v___x_3234_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_3231_, v_a_3228_);
if (v___x_3234_ == 0)
{
v_x_3230_ = v_tail_3233_;
goto _start;
}
else
{
lean_inc(v_value_3232_);
return v_value_3232_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg___boxed(lean_object* v_a_3236_, lean_object* v_fallback_3237_, lean_object* v_x_3238_){
_start:
{
lean_object* v_res_3239_; 
v_res_3239_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(v_a_3236_, v_fallback_3237_, v_x_3238_);
lean_dec(v_x_3238_);
lean_dec(v_fallback_3237_);
lean_dec(v_a_3236_);
return v_res_3239_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(lean_object* v_m_3240_, lean_object* v_a_3241_, lean_object* v_fallback_3242_){
_start:
{
lean_object* v_buckets_3243_; lean_object* v___x_3244_; uint64_t v___x_3245_; uint64_t v___x_3246_; uint64_t v___x_3247_; uint64_t v_fold_3248_; uint64_t v___x_3249_; uint64_t v___x_3250_; uint64_t v___x_3251_; size_t v___x_3252_; size_t v___x_3253_; size_t v___x_3254_; size_t v___x_3255_; size_t v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; 
v_buckets_3243_ = lean_ctor_get(v_m_3240_, 1);
v___x_3244_ = lean_array_get_size(v_buckets_3243_);
v___x_3245_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_a_3241_);
v___x_3246_ = 32ULL;
v___x_3247_ = lean_uint64_shift_right(v___x_3245_, v___x_3246_);
v_fold_3248_ = lean_uint64_xor(v___x_3245_, v___x_3247_);
v___x_3249_ = 16ULL;
v___x_3250_ = lean_uint64_shift_right(v_fold_3248_, v___x_3249_);
v___x_3251_ = lean_uint64_xor(v_fold_3248_, v___x_3250_);
v___x_3252_ = lean_uint64_to_usize(v___x_3251_);
v___x_3253_ = lean_usize_of_nat(v___x_3244_);
v___x_3254_ = ((size_t)1ULL);
v___x_3255_ = lean_usize_sub(v___x_3253_, v___x_3254_);
v___x_3256_ = lean_usize_land(v___x_3252_, v___x_3255_);
v___x_3257_ = lean_array_uget_borrowed(v_buckets_3243_, v___x_3256_);
v___x_3258_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(v_a_3241_, v_fallback_3242_, v___x_3257_);
return v___x_3258_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg___boxed(lean_object* v_m_3259_, lean_object* v_a_3260_, lean_object* v_fallback_3261_){
_start:
{
lean_object* v_res_3262_; 
v_res_3262_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_m_3259_, v_a_3260_, v_fallback_3261_);
lean_dec(v_fallback_3261_);
lean_dec(v_a_3260_);
lean_dec_ref(v_m_3259_);
return v_res_3262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg(lean_object* v_next_3263_, lean_object* v_rest_3264_, lean_object* v_a_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_){
_start:
{
lean_object* v___x_3271_; uint8_t v___x_3272_; 
v___x_3271_ = lean_unsigned_to_nat(0u);
v___x_3272_ = lean_nat_dec_eq(v_next_3263_, v___x_3271_);
if (v___x_3272_ == 0)
{
lean_object* v___x_3273_; 
v___x_3273_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_next_3263_, v_a_3265_, v_a_3266_, v_a_3267_, v_a_3268_, v_a_3269_);
if (lean_obj_tag(v___x_3273_) == 0)
{
lean_object* v_a_3274_; lean_object* v___x_3276_; uint8_t v_isShared_3277_; uint8_t v_isSharedCheck_3299_; 
v_a_3274_ = lean_ctor_get(v___x_3273_, 0);
v_isSharedCheck_3299_ = !lean_is_exclusive(v___x_3273_);
if (v_isSharedCheck_3299_ == 0)
{
v___x_3276_ = v___x_3273_;
v_isShared_3277_ = v_isSharedCheck_3299_;
goto v_resetjp_3275_;
}
else
{
lean_inc(v_a_3274_);
lean_dec(v___x_3273_);
v___x_3276_ = lean_box(0);
v_isShared_3277_ = v_isSharedCheck_3299_;
goto v_resetjp_3275_;
}
v_resetjp_3275_:
{
lean_object* v_snd_3278_; 
v_snd_3278_ = lean_ctor_get(v_a_3274_, 1);
lean_inc(v_snd_3278_);
lean_dec(v_a_3274_);
if (lean_obj_tag(v_rest_3264_) == 0)
{
lean_object* v_fst_3279_; lean_object* v_snd_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3288_; 
v_fst_3279_ = lean_ctor_get(v_snd_3278_, 0);
lean_inc(v_fst_3279_);
v_snd_3280_ = lean_ctor_get(v_snd_3278_, 1);
lean_inc(v_snd_3280_);
lean_dec(v_snd_3278_);
v___x_3281_ = lean_st_ref_take(v_a_3265_);
v___x_3282_ = lean_box(0);
v___x_3283_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___x_3284_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3284_, 0, v___x_3283_);
lean_ctor_set(v___x_3284_, 1, v_fst_3279_);
lean_ctor_set(v___x_3284_, 2, v_snd_3280_);
lean_ctor_set(v___x_3284_, 3, v___x_3283_);
v___x_3285_ = lean_array_set(v___x_3281_, v_next_3263_, v___x_3284_);
lean_dec(v_next_3263_);
v___x_3286_ = lean_st_ref_put(v_a_3265_, v___x_3285_);
if (v_isShared_3277_ == 0)
{
lean_ctor_set(v___x_3276_, 0, v___x_3282_);
v___x_3288_ = v___x_3276_;
goto v_reusejp_3287_;
}
else
{
lean_object* v_reuseFailAlloc_3289_; 
v_reuseFailAlloc_3289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3289_, 0, v___x_3282_);
v___x_3288_ = v_reuseFailAlloc_3289_;
goto v_reusejp_3287_;
}
v_reusejp_3287_:
{
return v___x_3288_;
}
}
else
{
lean_object* v_fst_3290_; lean_object* v_snd_3291_; lean_object* v_head_3292_; lean_object* v_tail_3293_; lean_object* v___x_3294_; uint8_t v___x_3295_; 
lean_del_object(v___x_3276_);
lean_dec(v_next_3263_);
v_fst_3290_ = lean_ctor_get(v_snd_3278_, 0);
lean_inc(v_fst_3290_);
v_snd_3291_ = lean_ctor_get(v_snd_3278_, 1);
lean_inc(v_snd_3291_);
lean_dec(v_snd_3278_);
v_head_3292_ = lean_ctor_get(v_rest_3264_, 0);
v_tail_3293_ = lean_ctor_get(v_rest_3264_, 1);
v___x_3294_ = lean_box(3);
v___x_3295_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_head_3292_, v___x_3294_);
if (v___x_3295_ == 0)
{
lean_object* v___x_3296_; 
lean_dec(v_fst_3290_);
v___x_3296_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_snd_3291_, v_head_3292_, v___x_3271_);
lean_dec(v_snd_3291_);
v_next_3263_ = v___x_3296_;
v_rest_3264_ = v_tail_3293_;
goto _start;
}
else
{
lean_dec(v_snd_3291_);
v_next_3263_ = v_fst_3290_;
v_rest_3264_ = v_tail_3293_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3300_; lean_object* v___x_3302_; uint8_t v_isShared_3303_; uint8_t v_isSharedCheck_3307_; 
lean_dec(v_next_3263_);
v_a_3300_ = lean_ctor_get(v___x_3273_, 0);
v_isSharedCheck_3307_ = !lean_is_exclusive(v___x_3273_);
if (v_isSharedCheck_3307_ == 0)
{
v___x_3302_ = v___x_3273_;
v_isShared_3303_ = v_isSharedCheck_3307_;
goto v_resetjp_3301_;
}
else
{
lean_inc(v_a_3300_);
lean_dec(v___x_3273_);
v___x_3302_ = lean_box(0);
v_isShared_3303_ = v_isSharedCheck_3307_;
goto v_resetjp_3301_;
}
v_resetjp_3301_:
{
lean_object* v___x_3305_; 
if (v_isShared_3303_ == 0)
{
v___x_3305_ = v___x_3302_;
goto v_reusejp_3304_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v_a_3300_);
v___x_3305_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3304_;
}
v_reusejp_3304_:
{
return v___x_3305_;
}
}
}
}
else
{
lean_object* v___x_3308_; lean_object* v___x_3309_; 
lean_dec(v_next_3263_);
v___x_3308_ = lean_box(0);
v___x_3309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3309_, 0, v___x_3308_);
return v___x_3309_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg___boxed(lean_object* v_next_3310_, lean_object* v_rest_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_, lean_object* v_a_3314_, lean_object* v_a_3315_, lean_object* v_a_3316_, lean_object* v_a_3317_){
_start:
{
lean_object* v_res_3318_; 
v_res_3318_ = l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg(v_next_3310_, v_rest_3311_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_, v_a_3316_);
lean_dec(v_a_3316_);
lean_dec_ref(v_a_3315_);
lean_dec(v_a_3314_);
lean_dec_ref(v_a_3313_);
lean_dec(v_a_3312_);
lean_dec(v_rest_3311_);
return v_res_3318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux(lean_object* v_00_u03b1_3319_, lean_object* v_next_3320_, lean_object* v_rest_3321_, lean_object* v_a_3322_, lean_object* v_a_3323_, lean_object* v_a_3324_, lean_object* v_a_3325_, lean_object* v_a_3326_){
_start:
{
lean_object* v___x_3328_; 
v___x_3328_ = l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg(v_next_3320_, v_rest_3321_, v_a_3322_, v_a_3323_, v_a_3324_, v_a_3325_, v_a_3326_);
return v___x_3328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux___boxed(lean_object* v_00_u03b1_3329_, lean_object* v_next_3330_, lean_object* v_rest_3331_, lean_object* v_a_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_){
_start:
{
lean_object* v_res_3338_; 
v_res_3338_ = l_Lean_Meta_LazyDiscrTree_dropKeyAux(v_00_u03b1_3329_, v_next_3330_, v_rest_3331_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_);
lean_dec(v_a_3336_);
lean_dec_ref(v_a_3335_);
lean_dec(v_a_3334_);
lean_dec_ref(v_a_3333_);
lean_dec(v_a_3332_);
lean_dec(v_rest_3331_);
return v_res_3338_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0(lean_object* v_00_u03b2_3339_, lean_object* v_m_3340_, lean_object* v_a_3341_, lean_object* v_fallback_3342_){
_start:
{
lean_object* v___x_3343_; 
v___x_3343_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_m_3340_, v_a_3341_, v_fallback_3342_);
return v___x_3343_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___boxed(lean_object* v_00_u03b2_3344_, lean_object* v_m_3345_, lean_object* v_a_3346_, lean_object* v_fallback_3347_){
_start:
{
lean_object* v_res_3348_; 
v_res_3348_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0(v_00_u03b2_3344_, v_m_3345_, v_a_3346_, v_fallback_3347_);
lean_dec(v_fallback_3347_);
lean_dec(v_a_3346_);
lean_dec_ref(v_m_3345_);
return v_res_3348_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0(lean_object* v_00_u03b2_3349_, lean_object* v_a_3350_, lean_object* v_fallback_3351_, lean_object* v_x_3352_){
_start:
{
lean_object* v___x_3353_; 
v___x_3353_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(v_a_3350_, v_fallback_3351_, v_x_3352_);
return v___x_3353_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3354_, lean_object* v_a_3355_, lean_object* v_fallback_3356_, lean_object* v_x_3357_){
_start:
{
lean_object* v_res_3358_; 
v_res_3358_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0(v_00_u03b2_3354_, v_a_3355_, v_fallback_3356_, v_x_3357_);
lean_dec(v_x_3357_);
lean_dec(v_fallback_3356_);
lean_dec(v_a_3355_);
return v_res_3358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey___redArg(lean_object* v_t_3359_, lean_object* v_path_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_){
_start:
{
if (lean_obj_tag(v_path_3360_) == 0)
{
lean_object* v___x_3366_; 
v___x_3366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3366_, 0, v_t_3359_);
return v___x_3366_;
}
else
{
lean_object* v_head_3367_; lean_object* v_tail_3368_; lean_object* v_roots_3369_; lean_object* v___x_3370_; lean_object* v_idx_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; 
v_head_3367_ = lean_ctor_get(v_path_3360_, 0);
lean_inc(v_head_3367_);
v_tail_3368_ = lean_ctor_get(v_path_3360_, 1);
lean_inc(v_tail_3368_);
lean_dec_ref_known(v_path_3360_, 2);
v_roots_3369_ = lean_ctor_get(v_t_3359_, 1);
v___x_3370_ = lean_unsigned_to_nat(0u);
v_idx_3371_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_roots_3369_, v_head_3367_, v___x_3370_);
lean_dec(v_head_3367_);
v___x_3372_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_dropKeyAux___boxed), 9, 3);
lean_closure_set(v___x_3372_, 0, lean_box(0));
lean_closure_set(v___x_3372_, 1, v_idx_3371_);
lean_closure_set(v___x_3372_, 2, v_tail_3368_);
v___x_3373_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_t_3359_, v___x_3372_, v_a_3361_, v_a_3362_, v_a_3363_, v_a_3364_);
if (lean_obj_tag(v___x_3373_) == 0)
{
lean_object* v_a_3374_; lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3382_; 
v_a_3374_ = lean_ctor_get(v___x_3373_, 0);
v_isSharedCheck_3382_ = !lean_is_exclusive(v___x_3373_);
if (v_isSharedCheck_3382_ == 0)
{
v___x_3376_ = v___x_3373_;
v_isShared_3377_ = v_isSharedCheck_3382_;
goto v_resetjp_3375_;
}
else
{
lean_inc(v_a_3374_);
lean_dec(v___x_3373_);
v___x_3376_ = lean_box(0);
v_isShared_3377_ = v_isSharedCheck_3382_;
goto v_resetjp_3375_;
}
v_resetjp_3375_:
{
lean_object* v_snd_3378_; lean_object* v___x_3380_; 
v_snd_3378_ = lean_ctor_get(v_a_3374_, 1);
lean_inc(v_snd_3378_);
lean_dec(v_a_3374_);
if (v_isShared_3377_ == 0)
{
lean_ctor_set(v___x_3376_, 0, v_snd_3378_);
v___x_3380_ = v___x_3376_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v_snd_3378_);
v___x_3380_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
return v___x_3380_;
}
}
}
else
{
lean_object* v_a_3383_; lean_object* v___x_3385_; uint8_t v_isShared_3386_; uint8_t v_isSharedCheck_3390_; 
v_a_3383_ = lean_ctor_get(v___x_3373_, 0);
v_isSharedCheck_3390_ = !lean_is_exclusive(v___x_3373_);
if (v_isSharedCheck_3390_ == 0)
{
v___x_3385_ = v___x_3373_;
v_isShared_3386_ = v_isSharedCheck_3390_;
goto v_resetjp_3384_;
}
else
{
lean_inc(v_a_3383_);
lean_dec(v___x_3373_);
v___x_3385_ = lean_box(0);
v_isShared_3386_ = v_isSharedCheck_3390_;
goto v_resetjp_3384_;
}
v_resetjp_3384_:
{
lean_object* v___x_3388_; 
if (v_isShared_3386_ == 0)
{
v___x_3388_ = v___x_3385_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v_a_3383_);
v___x_3388_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
return v___x_3388_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey___redArg___boxed(lean_object* v_t_3391_, lean_object* v_path_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_){
_start:
{
lean_object* v_res_3398_; 
v_res_3398_ = l_Lean_Meta_LazyDiscrTree_dropKey___redArg(v_t_3391_, v_path_3392_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_);
lean_dec(v_a_3396_);
lean_dec_ref(v_a_3395_);
lean_dec(v_a_3394_);
lean_dec_ref(v_a_3393_);
return v_res_3398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey(lean_object* v_00_u03b1_3399_, lean_object* v_t_3400_, lean_object* v_path_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_){
_start:
{
lean_object* v___x_3407_; 
v___x_3407_ = l_Lean_Meta_LazyDiscrTree_dropKey___redArg(v_t_3400_, v_path_3401_, v_a_3402_, v_a_3403_, v_a_3404_, v_a_3405_);
return v___x_3407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey___boxed(lean_object* v_00_u03b1_3408_, lean_object* v_t_3409_, lean_object* v_path_3410_, lean_object* v_a_3411_, lean_object* v_a_3412_, lean_object* v_a_3413_, lean_object* v_a_3414_, lean_object* v_a_3415_){
_start:
{
lean_object* v_res_3416_; 
v_res_3416_ = l_Lean_Meta_LazyDiscrTree_dropKey(v_00_u03b1_3408_, v_t_3409_, v_path_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_);
lean_dec(v_a_3414_);
lean_dec_ref(v_a_3413_);
lean_dec(v_a_3412_);
lean_dec_ref(v_a_3411_);
return v_res_3416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(lean_object* v_score_3419_, lean_object* v_e_3420_, lean_object* v_a_3421_){
_start:
{
lean_object* v___x_3422_; uint8_t v___x_3423_; 
v___x_3422_ = lean_array_get_size(v_a_3421_);
v___x_3423_ = lean_nat_dec_lt(v___x_3422_, v_score_3419_);
if (v___x_3423_ == 0)
{
lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; 
v___x_3424_ = lean_unsigned_to_nat(1u);
v___x_3425_ = lean_mk_empty_array_with_capacity(v___x_3424_);
v___x_3426_ = lean_array_push(v___x_3425_, v_e_3420_);
v___x_3427_ = lean_array_push(v_a_3421_, v___x_3426_);
return v___x_3427_;
}
else
{
lean_object* v___x_3428_; lean_object* v___x_3429_; 
v___x_3428_ = ((lean_object*)(l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg___closed__0));
v___x_3429_ = lean_array_push(v_a_3421_, v___x_3428_);
v_a_3421_ = v___x_3429_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg___boxed(lean_object* v_score_3431_, lean_object* v_e_3432_, lean_object* v_a_3433_){
_start:
{
lean_object* v_res_3434_; 
v_res_3434_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(v_score_3431_, v_e_3432_, v_a_3433_);
lean_dec(v_score_3431_);
return v_res_3434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop(lean_object* v_00_u03b1_3435_, lean_object* v_score_3436_, lean_object* v_e_3437_, lean_object* v_a_3438_){
_start:
{
lean_object* v___x_3439_; 
v___x_3439_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(v_score_3436_, v_e_3437_, v_a_3438_);
return v___x_3439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___boxed(lean_object* v_00_u03b1_3440_, lean_object* v_score_3441_, lean_object* v_e_3442_, lean_object* v_a_3443_){
_start:
{
lean_object* v_res_3444_; 
v_res_3444_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop(v_00_u03b1_3440_, v_score_3441_, v_e_3442_, v_a_3443_);
lean_dec(v_score_3441_);
return v_res_3444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(lean_object* v_r_3445_, lean_object* v_score_3446_, lean_object* v_e_3447_){
_start:
{
lean_object* v___x_3448_; lean_object* v___x_3449_; uint8_t v___x_3450_; 
v___x_3448_ = lean_array_get_size(v_e_3447_);
v___x_3449_ = lean_unsigned_to_nat(0u);
v___x_3450_ = lean_nat_dec_eq(v___x_3448_, v___x_3449_);
if (v___x_3450_ == 0)
{
lean_object* v___x_3451_; uint8_t v___x_3452_; 
v___x_3451_ = lean_array_get_size(v_r_3445_);
v___x_3452_ = lean_nat_dec_lt(v_score_3446_, v___x_3451_);
if (v___x_3452_ == 0)
{
lean_object* v___x_3453_; 
v___x_3453_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(v_score_3446_, v_e_3447_, v_r_3445_);
return v___x_3453_;
}
else
{
if (v___x_3452_ == 0)
{
lean_dec_ref(v_e_3447_);
return v_r_3445_;
}
else
{
lean_object* v_v_3454_; lean_object* v___x_3455_; lean_object* v_xs_x27_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; 
v_v_3454_ = lean_array_fget(v_r_3445_, v_score_3446_);
v___x_3455_ = lean_box(0);
v_xs_x27_3456_ = lean_array_fset(v_r_3445_, v_score_3446_, v___x_3455_);
v___x_3457_ = lean_array_push(v_v_3454_, v_e_3447_);
v___x_3458_ = lean_array_fset(v_xs_x27_3456_, v_score_3446_, v___x_3457_);
return v___x_3458_;
}
}
}
else
{
lean_dec_ref(v_e_3447_);
return v_r_3445_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg___boxed(lean_object* v_r_3459_, lean_object* v_score_3460_, lean_object* v_e_3461_){
_start:
{
lean_object* v_res_3462_; 
v_res_3462_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v_r_3459_, v_score_3460_, v_e_3461_);
lean_dec(v_score_3460_);
return v_res_3462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push(lean_object* v_00_u03b1_3463_, lean_object* v_r_3464_, lean_object* v_score_3465_, lean_object* v_e_3466_){
_start:
{
lean_object* v___x_3467_; 
v___x_3467_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v_r_3464_, v_score_3465_, v_e_3466_);
return v___x_3467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push___boxed(lean_object* v_00_u03b1_3468_, lean_object* v_r_3469_, lean_object* v_score_3470_, lean_object* v_e_3471_){
_start:
{
lean_object* v_res_3472_; 
v_res_3472_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push(v_00_u03b1_3468_, v_r_3469_, v_score_3470_, v_e_3471_);
lean_dec(v_score_3470_);
return v_res_3472_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(lean_object* v_as_3473_, size_t v_i_3474_, size_t v_stop_3475_, lean_object* v_b_3476_){
_start:
{
uint8_t v___x_3477_; 
v___x_3477_ = lean_usize_dec_eq(v_i_3474_, v_stop_3475_);
if (v___x_3477_ == 0)
{
lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; size_t v___x_3481_; size_t v___x_3482_; 
v___x_3478_ = lean_array_uget_borrowed(v_as_3473_, v_i_3474_);
v___x_3479_ = lean_array_get_size(v___x_3478_);
v___x_3480_ = lean_nat_add(v_b_3476_, v___x_3479_);
lean_dec(v_b_3476_);
v___x_3481_ = ((size_t)1ULL);
v___x_3482_ = lean_usize_add(v_i_3474_, v___x_3481_);
v_i_3474_ = v___x_3482_;
v_b_3476_ = v___x_3480_;
goto _start;
}
else
{
return v_b_3476_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg___boxed(lean_object* v_as_3484_, lean_object* v_i_3485_, lean_object* v_stop_3486_, lean_object* v_b_3487_){
_start:
{
size_t v_i_boxed_3488_; size_t v_stop_boxed_3489_; lean_object* v_res_3490_; 
v_i_boxed_3488_ = lean_unbox_usize(v_i_3485_);
lean_dec(v_i_3485_);
v_stop_boxed_3489_ = lean_unbox_usize(v_stop_3486_);
lean_dec(v_stop_3486_);
v_res_3490_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v_as_3484_, v_i_boxed_3488_, v_stop_boxed_3489_, v_b_3487_);
lean_dec_ref(v_as_3484_);
return v_res_3490_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(lean_object* v_as_3491_, size_t v_i_3492_, size_t v_stop_3493_, lean_object* v_b_3494_){
_start:
{
lean_object* v___y_3496_; uint8_t v___x_3500_; 
v___x_3500_ = lean_usize_dec_eq(v_i_3492_, v_stop_3493_);
if (v___x_3500_ == 0)
{
lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; uint8_t v___x_3504_; 
v___x_3501_ = lean_array_uget_borrowed(v_as_3491_, v_i_3492_);
v___x_3502_ = lean_unsigned_to_nat(0u);
v___x_3503_ = lean_array_get_size(v___x_3501_);
v___x_3504_ = lean_nat_dec_lt(v___x_3502_, v___x_3503_);
if (v___x_3504_ == 0)
{
v___y_3496_ = v_b_3494_;
goto v___jp_3495_;
}
else
{
uint8_t v___x_3505_; 
v___x_3505_ = lean_nat_dec_le(v___x_3503_, v___x_3503_);
if (v___x_3505_ == 0)
{
if (v___x_3504_ == 0)
{
v___y_3496_ = v_b_3494_;
goto v___jp_3495_;
}
else
{
size_t v___x_3506_; size_t v___x_3507_; lean_object* v___x_3508_; 
v___x_3506_ = ((size_t)0ULL);
v___x_3507_ = lean_usize_of_nat(v___x_3503_);
v___x_3508_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v___x_3501_, v___x_3506_, v___x_3507_, v_b_3494_);
v___y_3496_ = v___x_3508_;
goto v___jp_3495_;
}
}
else
{
size_t v___x_3509_; size_t v___x_3510_; lean_object* v___x_3511_; 
v___x_3509_ = ((size_t)0ULL);
v___x_3510_ = lean_usize_of_nat(v___x_3503_);
v___x_3511_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v___x_3501_, v___x_3509_, v___x_3510_, v_b_3494_);
v___y_3496_ = v___x_3511_;
goto v___jp_3495_;
}
}
}
else
{
return v_b_3494_;
}
v___jp_3495_:
{
size_t v___x_3497_; size_t v___x_3498_; 
v___x_3497_ = ((size_t)1ULL);
v___x_3498_ = lean_usize_add(v_i_3492_, v___x_3497_);
v_i_3492_ = v___x_3498_;
v_b_3494_ = v___y_3496_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg___boxed(lean_object* v_as_3512_, lean_object* v_i_3513_, lean_object* v_stop_3514_, lean_object* v_b_3515_){
_start:
{
size_t v_i_boxed_3516_; size_t v_stop_boxed_3517_; lean_object* v_res_3518_; 
v_i_boxed_3516_ = lean_unbox_usize(v_i_3513_);
lean_dec(v_i_3513_);
v_stop_boxed_3517_ = lean_unbox_usize(v_stop_3514_);
lean_dec(v_stop_3514_);
v_res_3518_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_as_3512_, v_i_boxed_3516_, v_stop_boxed_3517_, v_b_3515_);
lean_dec_ref(v_as_3512_);
return v_res_3518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(lean_object* v_mr_3519_){
_start:
{
lean_object* v___x_3520_; lean_object* v___x_3521_; uint8_t v___x_3522_; 
v___x_3520_ = lean_unsigned_to_nat(0u);
v___x_3521_ = lean_array_get_size(v_mr_3519_);
v___x_3522_ = lean_nat_dec_lt(v___x_3520_, v___x_3521_);
if (v___x_3522_ == 0)
{
return v___x_3520_;
}
else
{
uint8_t v___x_3523_; 
v___x_3523_ = lean_nat_dec_le(v___x_3521_, v___x_3521_);
if (v___x_3523_ == 0)
{
if (v___x_3522_ == 0)
{
return v___x_3520_;
}
else
{
size_t v___x_3524_; size_t v___x_3525_; lean_object* v___x_3526_; 
v___x_3524_ = ((size_t)0ULL);
v___x_3525_ = lean_usize_of_nat(v___x_3521_);
v___x_3526_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_mr_3519_, v___x_3524_, v___x_3525_, v___x_3520_);
return v___x_3526_;
}
}
else
{
size_t v___x_3527_; size_t v___x_3528_; lean_object* v___x_3529_; 
v___x_3527_ = ((size_t)0ULL);
v___x_3528_ = lean_usize_of_nat(v___x_3521_);
v___x_3529_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_mr_3519_, v___x_3527_, v___x_3528_, v___x_3520_);
return v___x_3529_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg___boxed(lean_object* v_mr_3530_){
_start:
{
lean_object* v_res_3531_; 
v_res_3531_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_mr_3530_);
lean_dec_ref(v_mr_3530_);
return v_res_3531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size(lean_object* v_00_u03b1_3532_, lean_object* v_mr_3533_){
_start:
{
lean_object* v___x_3534_; 
v___x_3534_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_mr_3533_);
return v___x_3534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size___boxed(lean_object* v_00_u03b1_3535_, lean_object* v_mr_3536_){
_start:
{
lean_object* v_res_3537_; 
v_res_3537_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size(v_00_u03b1_3535_, v_mr_3536_);
lean_dec_ref(v_mr_3536_);
return v_res_3537_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0(lean_object* v_00_u03b1_3538_, lean_object* v_as_3539_, size_t v_i_3540_, size_t v_stop_3541_, lean_object* v_b_3542_){
_start:
{
lean_object* v___x_3543_; 
v___x_3543_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v_as_3539_, v_i_3540_, v_stop_3541_, v_b_3542_);
return v___x_3543_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___boxed(lean_object* v_00_u03b1_3544_, lean_object* v_as_3545_, lean_object* v_i_3546_, lean_object* v_stop_3547_, lean_object* v_b_3548_){
_start:
{
size_t v_i_boxed_3549_; size_t v_stop_boxed_3550_; lean_object* v_res_3551_; 
v_i_boxed_3549_ = lean_unbox_usize(v_i_3546_);
lean_dec(v_i_3546_);
v_stop_boxed_3550_ = lean_unbox_usize(v_stop_3547_);
lean_dec(v_stop_3547_);
v_res_3551_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0(v_00_u03b1_3544_, v_as_3545_, v_i_boxed_3549_, v_stop_boxed_3550_, v_b_3548_);
lean_dec_ref(v_as_3545_);
return v_res_3551_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1(lean_object* v_00_u03b1_3552_, lean_object* v_as_3553_, size_t v_i_3554_, size_t v_stop_3555_, lean_object* v_b_3556_){
_start:
{
lean_object* v___x_3557_; 
v___x_3557_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_as_3553_, v_i_3554_, v_stop_3555_, v_b_3556_);
return v___x_3557_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___boxed(lean_object* v_00_u03b1_3558_, lean_object* v_as_3559_, lean_object* v_i_3560_, lean_object* v_stop_3561_, lean_object* v_b_3562_){
_start:
{
size_t v_i_boxed_3563_; size_t v_stop_boxed_3564_; lean_object* v_res_3565_; 
v_i_boxed_3563_ = lean_unbox_usize(v_i_3560_);
lean_dec(v_i_3560_);
v_stop_boxed_3564_ = lean_unbox_usize(v_stop_3561_);
lean_dec(v_stop_3561_);
v_res_3565_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1(v_00_u03b1_3558_, v_as_3559_, v_i_boxed_3563_, v_stop_boxed_3564_, v_b_3562_);
lean_dec_ref(v_as_3559_);
return v_res_3565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__0(lean_object* v_f_3566_, lean_object* v_j_3567_, lean_object* v_x_3568_){
_start:
{
lean_object* v___x_3569_; 
v___x_3569_ = lean_apply_2(v_f_3566_, v_j_3567_, v_x_3568_);
return v___x_3569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1(lean_object* v___f_3589_, lean_object* v_x1_3590_, lean_object* v_x2_3591_){
_start:
{
lean_object* v___x_3592_; size_t v_sz_3593_; size_t v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; 
v___x_3592_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__9));
v_sz_3593_ = lean_array_size(v_x2_3591_);
v___x_3594_ = ((size_t)0ULL);
v___x_3595_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3592_, v___f_3589_, v_sz_3593_, v___x_3594_, v_x2_3591_);
v___x_3596_ = l_Array_append___redArg(v_x1_3590_, v___x_3595_);
lean_dec(v___x_3595_);
return v___x_3596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2(lean_object* v_n_3597_, lean_object* v_mr_3598_, lean_object* v_f_3599_, lean_object* v_i_3600_, lean_object* v_x_3601_, lean_object* v_r_3602_){
_start:
{
lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v_j_3605_; lean_object* v_b_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; uint8_t v___x_3610_; 
v___x_3603_ = lean_unsigned_to_nat(1u);
v___x_3604_ = lean_nat_sub(v_n_3597_, v___x_3603_);
v_j_3605_ = lean_nat_sub(v___x_3604_, v_i_3600_);
lean_dec(v___x_3604_);
v_b_3606_ = lean_array_fget_borrowed(v_mr_3598_, v_j_3605_);
v___x_3607_ = lean_unsigned_to_nat(0u);
v___x_3608_ = lean_array_get_size(v_b_3606_);
v___x_3609_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__9));
v___x_3610_ = lean_nat_dec_lt(v___x_3607_, v___x_3608_);
if (v___x_3610_ == 0)
{
lean_dec(v_j_3605_);
lean_dec(v_f_3599_);
return v_r_3602_;
}
else
{
lean_object* v___f_3611_; lean_object* v___f_3612_; uint8_t v___x_3613_; 
v___f_3611_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3611_, 0, v_f_3599_);
lean_closure_set(v___f_3611_, 1, v_j_3605_);
v___f_3612_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1), 3, 1);
lean_closure_set(v___f_3612_, 0, v___f_3611_);
v___x_3613_ = lean_nat_dec_le(v___x_3608_, v___x_3608_);
if (v___x_3613_ == 0)
{
if (v___x_3610_ == 0)
{
lean_dec_ref(v___f_3612_);
return v_r_3602_;
}
else
{
size_t v___x_3614_; size_t v___x_3615_; lean_object* v___x_3616_; 
v___x_3614_ = ((size_t)0ULL);
v___x_3615_ = lean_usize_of_nat(v___x_3608_);
lean_inc(v_b_3606_);
v___x_3616_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3609_, v___f_3612_, v_b_3606_, v___x_3614_, v___x_3615_, v_r_3602_);
return v___x_3616_;
}
}
else
{
size_t v___x_3617_; size_t v___x_3618_; lean_object* v___x_3619_; 
v___x_3617_ = ((size_t)0ULL);
v___x_3618_ = lean_usize_of_nat(v___x_3608_);
lean_inc(v_b_3606_);
v___x_3619_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3609_, v___f_3612_, v_b_3606_, v___x_3617_, v___x_3618_, v_r_3602_);
return v___x_3619_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2___boxed(lean_object* v_n_3620_, lean_object* v_mr_3621_, lean_object* v_f_3622_, lean_object* v_i_3623_, lean_object* v_x_3624_, lean_object* v_r_3625_){
_start:
{
lean_object* v_res_3626_; 
v_res_3626_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2(v_n_3620_, v_mr_3621_, v_f_3622_, v_i_3623_, v_x_3624_, v_r_3625_);
lean_dec(v_i_3623_);
lean_dec_ref(v_mr_3621_);
lean_dec(v_n_3620_);
return v_res_3626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg(lean_object* v_mr_3627_, lean_object* v_a_3628_, lean_object* v_f_3629_){
_start:
{
lean_object* v_n_3630_; lean_object* v___f_3631_; lean_object* v___x_3632_; 
v_n_3630_ = lean_array_get_size(v_mr_3627_);
v___f_3631_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_3631_, 0, v_n_3630_);
lean_closure_set(v___f_3631_, 1, v_mr_3627_);
lean_closure_set(v___f_3631_, 2, v_f_3629_);
v___x_3632_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop(lean_box(0), v_n_3630_, v___f_3631_, v_n_3630_, lean_box(0), v_a_3628_);
return v___x_3632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux(lean_object* v_00_u03b1_3633_, lean_object* v_00_u03b2_3634_, lean_object* v_mr_3635_, lean_object* v_a_3636_, lean_object* v_f_3637_){
_start:
{
lean_object* v___x_3638_; 
v___x_3638_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg(v_mr_3635_, v_a_3636_, v_f_3637_);
return v___x_3638_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(size_t v_sz_3639_, size_t v_i_3640_, lean_object* v_bs_3641_){
_start:
{
uint8_t v___x_3642_; 
v___x_3642_ = lean_usize_dec_lt(v_i_3640_, v_sz_3639_);
if (v___x_3642_ == 0)
{
return v_bs_3641_;
}
else
{
lean_object* v_v_3643_; lean_object* v___x_3644_; lean_object* v_bs_x27_3645_; size_t v___x_3646_; size_t v___x_3647_; lean_object* v___x_3648_; 
v_v_3643_ = lean_array_uget(v_bs_3641_, v_i_3640_);
v___x_3644_ = lean_unsigned_to_nat(0u);
v_bs_x27_3645_ = lean_array_uset(v_bs_3641_, v_i_3640_, v___x_3644_);
v___x_3646_ = ((size_t)1ULL);
v___x_3647_ = lean_usize_add(v_i_3640_, v___x_3646_);
v___x_3648_ = lean_array_uset(v_bs_x27_3645_, v_i_3640_, v_v_3643_);
v_i_3640_ = v___x_3647_;
v_bs_3641_ = v___x_3648_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg___boxed(lean_object* v_sz_3650_, lean_object* v_i_3651_, lean_object* v_bs_3652_){
_start:
{
size_t v_sz_boxed_3653_; size_t v_i_boxed_3654_; lean_object* v_res_3655_; 
v_sz_boxed_3653_ = lean_unbox_usize(v_sz_3650_);
lean_dec(v_sz_3650_);
v_i_boxed_3654_ = lean_unbox_usize(v_i_3651_);
lean_dec(v_i_3651_);
v_res_3655_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(v_sz_boxed_3653_, v_i_boxed_3654_, v_bs_3652_);
return v_res_3655_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(lean_object* v_as_3656_, size_t v_i_3657_, size_t v_stop_3658_, lean_object* v_b_3659_){
_start:
{
uint8_t v___x_3660_; 
v___x_3660_ = lean_usize_dec_eq(v_i_3657_, v_stop_3658_);
if (v___x_3660_ == 0)
{
lean_object* v___x_3661_; size_t v_sz_3662_; size_t v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; size_t v___x_3666_; size_t v___x_3667_; 
v___x_3661_ = lean_array_uget_borrowed(v_as_3656_, v_i_3657_);
v_sz_3662_ = lean_array_size(v___x_3661_);
v___x_3663_ = ((size_t)0ULL);
lean_inc(v___x_3661_);
v___x_3664_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(v_sz_3662_, v___x_3663_, v___x_3661_);
v___x_3665_ = l_Array_append___redArg(v_b_3659_, v___x_3664_);
lean_dec_ref(v___x_3664_);
v___x_3666_ = ((size_t)1ULL);
v___x_3667_ = lean_usize_add(v_i_3657_, v___x_3666_);
v_i_3657_ = v___x_3667_;
v_b_3659_ = v___x_3665_;
goto _start;
}
else
{
return v_b_3659_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg___boxed(lean_object* v_as_3669_, lean_object* v_i_3670_, lean_object* v_stop_3671_, lean_object* v_b_3672_){
_start:
{
size_t v_i_boxed_3673_; size_t v_stop_boxed_3674_; lean_object* v_res_3675_; 
v_i_boxed_3673_ = lean_unbox_usize(v_i_3670_);
lean_dec(v_i_3670_);
v_stop_boxed_3674_ = lean_unbox_usize(v_stop_3671_);
lean_dec(v_stop_3671_);
v_res_3675_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(v_as_3669_, v_i_boxed_3673_, v_stop_boxed_3674_, v_b_3672_);
lean_dec_ref(v_as_3669_);
return v_res_3675_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(lean_object* v_n_3676_, lean_object* v_aa_3677_, lean_object* v_n_3678_, lean_object* v_j_3679_, lean_object* v_a_3680_){
_start:
{
lean_object* v_zero_3681_; uint8_t v_isZero_3682_; 
v_zero_3681_ = lean_unsigned_to_nat(0u);
v_isZero_3682_ = lean_nat_dec_eq(v_j_3679_, v_zero_3681_);
if (v_isZero_3682_ == 1)
{
lean_dec(v_j_3679_);
return v_a_3680_;
}
else
{
lean_object* v_one_3683_; lean_object* v_n_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v_j_3687_; lean_object* v_b_3688_; lean_object* v___x_3689_; uint8_t v___x_3690_; 
v_one_3683_ = lean_unsigned_to_nat(1u);
v_n_3684_ = lean_nat_sub(v_j_3679_, v_one_3683_);
v___x_3685_ = lean_nat_sub(v_n_3678_, v_j_3679_);
lean_dec(v_j_3679_);
v___x_3686_ = lean_nat_sub(v_n_3676_, v_one_3683_);
v_j_3687_ = lean_nat_sub(v___x_3686_, v___x_3685_);
lean_dec(v___x_3685_);
lean_dec(v___x_3686_);
v_b_3688_ = lean_array_fget_borrowed(v_aa_3677_, v_j_3687_);
lean_dec(v_j_3687_);
v___x_3689_ = lean_array_get_size(v_b_3688_);
v___x_3690_ = lean_nat_dec_lt(v_zero_3681_, v___x_3689_);
if (v___x_3690_ == 0)
{
v_j_3679_ = v_n_3684_;
goto _start;
}
else
{
size_t v___x_3692_; size_t v___x_3693_; lean_object* v___x_3694_; 
v___x_3692_ = ((size_t)0ULL);
v___x_3693_ = lean_usize_of_nat(v___x_3689_);
v___x_3694_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(v_b_3688_, v___x_3692_, v___x_3693_, v_a_3680_);
v_j_3679_ = v_n_3684_;
v_a_3680_ = v___x_3694_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg___boxed(lean_object* v_n_3696_, lean_object* v_aa_3697_, lean_object* v_n_3698_, lean_object* v_j_3699_, lean_object* v_a_3700_){
_start:
{
lean_object* v_res_3701_; 
v_res_3701_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(v_n_3696_, v_aa_3697_, v_n_3698_, v_j_3699_, v_a_3700_);
lean_dec(v_n_3698_);
lean_dec_ref(v_aa_3697_);
lean_dec(v_n_3696_);
return v_res_3701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(lean_object* v_mr_3702_, lean_object* v_a_3703_){
_start:
{
lean_object* v_n_3704_; lean_object* v___x_3705_; 
v_n_3704_ = lean_array_get_size(v_mr_3702_);
v___x_3705_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(v_n_3704_, v_mr_3702_, v_n_3704_, v_n_3704_, v_a_3703_);
return v___x_3705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg___boxed(lean_object* v_mr_3706_, lean_object* v_a_3707_){
_start:
{
lean_object* v_res_3708_; 
v_res_3708_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3706_, v_a_3707_);
lean_dec_ref(v_mr_3706_);
return v_res_3708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___redArg(lean_object* v_mr_3709_, lean_object* v_a_3710_){
_start:
{
lean_object* v___x_3711_; 
v___x_3711_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3709_, v_a_3710_);
return v___x_3711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___redArg___boxed(lean_object* v_mr_3712_, lean_object* v_a_3713_){
_start:
{
lean_object* v_res_3714_; 
v_res_3714_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___redArg(v_mr_3712_, v_a_3713_);
lean_dec_ref(v_mr_3712_);
return v_res_3714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults(lean_object* v_00_u03b1_3715_, lean_object* v_mr_3716_, lean_object* v_a_3717_){
_start:
{
lean_object* v___x_3718_; 
v___x_3718_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3716_, v_a_3717_);
return v___x_3718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___boxed(lean_object* v_00_u03b1_3719_, lean_object* v_mr_3720_, lean_object* v_a_3721_){
_start:
{
lean_object* v_res_3722_; 
v_res_3722_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults(v_00_u03b1_3719_, v_mr_3720_, v_a_3721_);
lean_dec_ref(v_mr_3720_);
return v_res_3722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0(lean_object* v_00_u03b1_3723_, lean_object* v_mr_3724_, lean_object* v_a_3725_){
_start:
{
lean_object* v___x_3726_; 
v___x_3726_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3724_, v_a_3725_);
return v___x_3726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___boxed(lean_object* v_00_u03b1_3727_, lean_object* v_mr_3728_, lean_object* v_a_3729_){
_start:
{
lean_object* v_res_3730_; 
v_res_3730_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0(v_00_u03b1_3727_, v_mr_3728_, v_a_3729_);
lean_dec_ref(v_mr_3728_);
return v_res_3730_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0(lean_object* v_00_u03b1_3731_, size_t v_sz_3732_, size_t v_i_3733_, lean_object* v_bs_3734_){
_start:
{
lean_object* v___x_3735_; 
v___x_3735_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(v_sz_3732_, v_i_3733_, v_bs_3734_);
return v___x_3735_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3736_, lean_object* v_sz_3737_, lean_object* v_i_3738_, lean_object* v_bs_3739_){
_start:
{
size_t v_sz_boxed_3740_; size_t v_i_boxed_3741_; lean_object* v_res_3742_; 
v_sz_boxed_3740_ = lean_unbox_usize(v_sz_3737_);
lean_dec(v_sz_3737_);
v_i_boxed_3741_ = lean_unbox_usize(v_i_3738_);
lean_dec(v_i_3738_);
v_res_3742_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0(v_00_u03b1_3736_, v_sz_boxed_3740_, v_i_boxed_3741_, v_bs_3739_);
return v_res_3742_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1(lean_object* v_00_u03b1_3743_, lean_object* v_as_3744_, size_t v_i_3745_, size_t v_stop_3746_, lean_object* v_b_3747_){
_start:
{
lean_object* v___x_3748_; 
v___x_3748_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(v_as_3744_, v_i_3745_, v_stop_3746_, v_b_3747_);
return v___x_3748_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3749_, lean_object* v_as_3750_, lean_object* v_i_3751_, lean_object* v_stop_3752_, lean_object* v_b_3753_){
_start:
{
size_t v_i_boxed_3754_; size_t v_stop_boxed_3755_; lean_object* v_res_3756_; 
v_i_boxed_3754_ = lean_unbox_usize(v_i_3751_);
lean_dec(v_i_3751_);
v_stop_boxed_3755_ = lean_unbox_usize(v_stop_3752_);
lean_dec(v_stop_3752_);
v_res_3756_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1(v_00_u03b1_3749_, v_as_3750_, v_i_boxed_3754_, v_stop_boxed_3755_, v_b_3753_);
lean_dec_ref(v_as_3750_);
return v_res_3756_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2(lean_object* v_00_u03b1_3757_, lean_object* v_n_3758_, lean_object* v_aa_3759_, lean_object* v_n_3760_, lean_object* v_j_3761_, lean_object* v_a_3762_, lean_object* v_a_3763_){
_start:
{
lean_object* v___x_3764_; 
v___x_3764_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(v_n_3758_, v_aa_3759_, v_n_3760_, v_j_3761_, v_a_3763_);
return v___x_3764_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___boxed(lean_object* v_00_u03b1_3765_, lean_object* v_n_3766_, lean_object* v_aa_3767_, lean_object* v_n_3768_, lean_object* v_j_3769_, lean_object* v_a_3770_, lean_object* v_a_3771_){
_start:
{
lean_object* v_res_3772_; 
v_res_3772_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2(v_00_u03b1_3765_, v_n_3766_, v_aa_3767_, v_n_3768_, v_j_3769_, v_a_3770_, v_a_3771_);
lean_dec(v_n_3768_);
lean_dec_ref(v_aa_3767_);
lean_dec(v_n_3766_);
return v_res_3772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0(lean_object* v_snd_3780_, lean_object* v___x_3781_, lean_object* v_score_3782_, lean_object* v___x_3783_, lean_object* v_k_3784_, lean_object* v_args_3785_, lean_object* v_cases_3786_){
_start:
{
lean_object* v___x_3787_; 
v___x_3787_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_snd_3780_, v_k_3784_);
if (lean_obj_tag(v___x_3787_) == 0)
{
lean_dec_ref(v___x_3781_);
return v_cases_3786_;
}
else
{
lean_object* v_val_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; 
v_val_3788_ = lean_ctor_get(v___x_3787_, 0);
lean_inc(v_val_3788_);
lean_dec_ref_known(v___x_3787_, 1);
v___x_3789_ = l_Array_append___redArg(v___x_3781_, v_args_3785_);
v___x_3790_ = lean_nat_add(v_score_3782_, v___x_3783_);
v___x_3791_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3791_, 0, v___x_3789_);
lean_ctor_set(v___x_3791_, 1, v___x_3790_);
lean_ctor_set(v___x_3791_, 2, v_val_3788_);
v___x_3792_ = lean_array_push(v_cases_3786_, v___x_3791_);
return v___x_3792_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0___boxed(lean_object* v_snd_3793_, lean_object* v___x_3794_, lean_object* v_score_3795_, lean_object* v___x_3796_, lean_object* v_k_3797_, lean_object* v_args_3798_, lean_object* v_cases_3799_){
_start:
{
lean_object* v_res_3800_; 
v_res_3800_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0(v_snd_3793_, v___x_3794_, v_score_3795_, v___x_3796_, v_k_3797_, v_args_3798_, v_cases_3799_);
lean_dec_ref(v_args_3798_);
lean_dec(v_k_3797_);
lean_dec(v___x_3796_);
lean_dec(v_score_3795_);
lean_dec_ref(v_snd_3793_);
return v_res_3800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(lean_object* v_cases_3801_, lean_object* v_result_3802_, lean_object* v_a_3803_, lean_object* v_a_3804_, lean_object* v_a_3805_, lean_object* v_a_3806_, lean_object* v_a_3807_){
_start:
{
lean_object* v___x_3809_; lean_object* v___x_3810_; uint8_t v___x_3811_; 
v___x_3809_ = lean_array_get_size(v_cases_3801_);
v___x_3810_ = lean_unsigned_to_nat(0u);
v___x_3811_ = lean_nat_dec_eq(v___x_3809_, v___x_3810_);
if (v___x_3811_ == 0)
{
lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v_ca_3815_; lean_object* v_todo_3816_; lean_object* v_score_3817_; lean_object* v_c_3818_; lean_object* v___x_3820_; uint8_t v_isShared_3821_; uint8_t v_isSharedCheck_3884_; 
v___x_3812_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedPartialMatch_default));
v___x_3813_ = lean_unsigned_to_nat(1u);
v___x_3814_ = lean_nat_sub(v___x_3809_, v___x_3813_);
v_ca_3815_ = lean_array_get(v___x_3812_, v_cases_3801_, v___x_3814_);
lean_dec(v___x_3814_);
v_todo_3816_ = lean_ctor_get(v_ca_3815_, 0);
v_score_3817_ = lean_ctor_get(v_ca_3815_, 1);
v_c_3818_ = lean_ctor_get(v_ca_3815_, 2);
v_isSharedCheck_3884_ = !lean_is_exclusive(v_ca_3815_);
if (v_isSharedCheck_3884_ == 0)
{
v___x_3820_ = v_ca_3815_;
v_isShared_3821_ = v_isSharedCheck_3884_;
goto v_resetjp_3819_;
}
else
{
lean_inc(v_c_3818_);
lean_inc(v_score_3817_);
lean_inc(v_todo_3816_);
lean_dec(v_ca_3815_);
v___x_3820_ = lean_box(0);
v_isShared_3821_ = v_isSharedCheck_3884_;
goto v_resetjp_3819_;
}
v_resetjp_3819_:
{
lean_object* v___x_3822_; lean_object* v_cases_3823_; lean_object* v___x_3824_; 
v___x_3822_ = l_Lean_instInhabitedExpr;
v_cases_3823_ = lean_array_pop(v_cases_3801_);
v___x_3824_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_c_3818_, v_a_3803_, v_a_3804_, v_a_3805_, v_a_3806_, v_a_3807_);
lean_dec(v_c_3818_);
if (lean_obj_tag(v___x_3824_) == 0)
{
lean_object* v_a_3825_; lean_object* v___y_3827_; lean_object* v___y_3828_; uint8_t v___y_3829_; lean_object* v___y_3830_; lean_object* v_snd_3853_; lean_object* v_fst_3854_; lean_object* v_fst_3855_; lean_object* v_snd_3856_; lean_object* v___x_3857_; uint8_t v___y_3859_; uint8_t v___x_3869_; 
v_a_3825_ = lean_ctor_get(v___x_3824_, 0);
lean_inc(v_a_3825_);
lean_dec_ref_known(v___x_3824_, 1);
v_snd_3853_ = lean_ctor_get(v_a_3825_, 1);
lean_inc(v_snd_3853_);
v_fst_3854_ = lean_ctor_get(v_a_3825_, 0);
lean_inc(v_fst_3854_);
lean_dec(v_a_3825_);
v_fst_3855_ = lean_ctor_get(v_snd_3853_, 0);
lean_inc(v_fst_3855_);
v_snd_3856_ = lean_ctor_get(v_snd_3853_, 1);
lean_inc(v_snd_3856_);
lean_dec(v_snd_3853_);
v___x_3857_ = lean_array_get_size(v_todo_3816_);
v___x_3869_ = lean_nat_dec_eq(v___x_3857_, v___x_3810_);
if (v___x_3869_ == 0)
{
uint8_t v___x_3870_; 
lean_dec(v_fst_3854_);
v___x_3870_ = lean_nat_dec_eq(v_fst_3855_, v___x_3810_);
if (v___x_3870_ == 0)
{
v___y_3859_ = v___x_3869_;
goto v___jp_3858_;
}
else
{
lean_object* v_size_3871_; uint8_t v___x_3872_; 
v_size_3871_ = lean_ctor_get(v_snd_3856_, 0);
v___x_3872_ = lean_nat_dec_eq(v_size_3871_, v___x_3810_);
if (v___x_3872_ == 0)
{
v___y_3859_ = v___x_3872_;
goto v___jp_3858_;
}
else
{
lean_dec(v_snd_3856_);
lean_dec(v_fst_3855_);
lean_del_object(v___x_3820_);
lean_dec(v_score_3817_);
lean_dec_ref(v_todo_3816_);
v_cases_3801_ = v_cases_3823_;
goto _start;
}
}
}
else
{
lean_object* v___x_3874_; 
lean_dec(v_snd_3856_);
lean_dec(v_fst_3855_);
lean_del_object(v___x_3820_);
lean_dec_ref(v_todo_3816_);
v___x_3874_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v_result_3802_, v_score_3817_, v_fst_3854_);
lean_dec(v_score_3817_);
v_cases_3801_ = v_cases_3823_;
v_result_3802_ = v___x_3874_;
goto _start;
}
v___jp_3826_:
{
uint8_t v___x_3831_; lean_object* v___x_3832_; 
v___x_3831_ = 1;
v___x_3832_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v___y_3828_, v___x_3831_, v___y_3829_, v_a_3804_, v_a_3805_, v_a_3806_, v_a_3807_);
if (lean_obj_tag(v___x_3832_) == 0)
{
lean_object* v_a_3833_; lean_object* v_fst_3834_; 
v_a_3833_ = lean_ctor_get(v___x_3832_, 0);
lean_inc(v_a_3833_);
lean_dec_ref_known(v___x_3832_, 1);
v_fst_3834_ = lean_ctor_get(v_a_3833_, 0);
lean_inc(v_fst_3834_);
switch(lean_obj_tag(v_fst_3834_))
{
case 3:
{
lean_dec(v_a_3833_);
lean_dec_ref(v___y_3827_);
v_cases_3801_ = v___y_3830_;
goto _start;
}
case 5:
{
lean_object* v_snd_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; 
v_snd_3836_ = lean_ctor_get(v_a_3833_, 1);
lean_inc(v_snd_3836_);
lean_dec(v_a_3833_);
v___x_3837_ = lean_box(4);
v___x_3838_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
lean_inc_ref(v___y_3827_);
v___x_3839_ = lean_apply_3(v___y_3827_, v___x_3837_, v___x_3838_, v___y_3830_);
v___x_3840_ = lean_apply_3(v___y_3827_, v_fst_3834_, v_snd_3836_, v___x_3839_);
v_cases_3801_ = v___x_3840_;
goto _start;
}
default: 
{
lean_object* v_snd_3842_; lean_object* v___x_3843_; 
v_snd_3842_ = lean_ctor_get(v_a_3833_, 1);
lean_inc(v_snd_3842_);
lean_dec(v_a_3833_);
v___x_3843_ = lean_apply_3(v___y_3827_, v_fst_3834_, v_snd_3842_, v___y_3830_);
v_cases_3801_ = v___x_3843_;
goto _start;
}
}
}
else
{
lean_object* v_a_3845_; lean_object* v___x_3847_; uint8_t v_isShared_3848_; uint8_t v_isSharedCheck_3852_; 
lean_dec_ref(v___y_3830_);
lean_dec_ref(v___y_3827_);
lean_dec_ref(v_result_3802_);
v_a_3845_ = lean_ctor_get(v___x_3832_, 0);
v_isSharedCheck_3852_ = !lean_is_exclusive(v___x_3832_);
if (v_isSharedCheck_3852_ == 0)
{
v___x_3847_ = v___x_3832_;
v_isShared_3848_ = v_isSharedCheck_3852_;
goto v_resetjp_3846_;
}
else
{
lean_inc(v_a_3845_);
lean_dec(v___x_3832_);
v___x_3847_ = lean_box(0);
v_isShared_3848_ = v_isSharedCheck_3852_;
goto v_resetjp_3846_;
}
v_resetjp_3846_:
{
lean_object* v___x_3850_; 
if (v_isShared_3848_ == 0)
{
v___x_3850_ = v___x_3847_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v_a_3845_);
v___x_3850_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3849_;
}
v_reusejp_3849_:
{
return v___x_3850_;
}
}
}
}
v___jp_3858_:
{
lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___f_3863_; uint8_t v___x_3864_; 
v___x_3860_ = lean_nat_sub(v___x_3857_, v___x_3813_);
v___x_3861_ = lean_array_get(v___x_3822_, v_todo_3816_, v___x_3860_);
lean_dec(v___x_3860_);
v___x_3862_ = lean_array_pop(v_todo_3816_);
lean_inc(v_score_3817_);
lean_inc_ref(v___x_3862_);
v___f_3863_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0___boxed), 7, 4);
lean_closure_set(v___f_3863_, 0, v_snd_3856_);
lean_closure_set(v___f_3863_, 1, v___x_3862_);
lean_closure_set(v___f_3863_, 2, v_score_3817_);
lean_closure_set(v___f_3863_, 3, v___x_3813_);
v___x_3864_ = lean_nat_dec_eq(v_fst_3855_, v___x_3810_);
if (v___x_3864_ == 0)
{
lean_object* v___x_3866_; 
if (v_isShared_3821_ == 0)
{
lean_ctor_set(v___x_3820_, 2, v_fst_3855_);
lean_ctor_set(v___x_3820_, 0, v___x_3862_);
v___x_3866_ = v___x_3820_;
goto v_reusejp_3865_;
}
else
{
lean_object* v_reuseFailAlloc_3868_; 
v_reuseFailAlloc_3868_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3868_, 0, v___x_3862_);
lean_ctor_set(v_reuseFailAlloc_3868_, 1, v_score_3817_);
lean_ctor_set(v_reuseFailAlloc_3868_, 2, v_fst_3855_);
v___x_3866_ = v_reuseFailAlloc_3868_;
goto v_reusejp_3865_;
}
v_reusejp_3865_:
{
lean_object* v___x_3867_; 
v___x_3867_ = lean_array_push(v_cases_3823_, v___x_3866_);
v___y_3827_ = v___f_3863_;
v___y_3828_ = v___x_3861_;
v___y_3829_ = v___y_3859_;
v___y_3830_ = v___x_3867_;
goto v___jp_3826_;
}
}
else
{
lean_dec_ref(v___x_3862_);
lean_dec(v_fst_3855_);
lean_del_object(v___x_3820_);
lean_dec(v_score_3817_);
v___y_3827_ = v___f_3863_;
v___y_3828_ = v___x_3861_;
v___y_3829_ = v___y_3859_;
v___y_3830_ = v_cases_3823_;
goto v___jp_3826_;
}
}
}
else
{
lean_object* v_a_3876_; lean_object* v___x_3878_; uint8_t v_isShared_3879_; uint8_t v_isSharedCheck_3883_; 
lean_dec_ref(v_cases_3823_);
lean_del_object(v___x_3820_);
lean_dec(v_score_3817_);
lean_dec_ref(v_todo_3816_);
lean_dec_ref(v_result_3802_);
v_a_3876_ = lean_ctor_get(v___x_3824_, 0);
v_isSharedCheck_3883_ = !lean_is_exclusive(v___x_3824_);
if (v_isSharedCheck_3883_ == 0)
{
v___x_3878_ = v___x_3824_;
v_isShared_3879_ = v_isSharedCheck_3883_;
goto v_resetjp_3877_;
}
else
{
lean_inc(v_a_3876_);
lean_dec(v___x_3824_);
v___x_3878_ = lean_box(0);
v_isShared_3879_ = v_isSharedCheck_3883_;
goto v_resetjp_3877_;
}
v_resetjp_3877_:
{
lean_object* v___x_3881_; 
if (v_isShared_3879_ == 0)
{
v___x_3881_ = v___x_3878_;
goto v_reusejp_3880_;
}
else
{
lean_object* v_reuseFailAlloc_3882_; 
v_reuseFailAlloc_3882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3882_, 0, v_a_3876_);
v___x_3881_ = v_reuseFailAlloc_3882_;
goto v_reusejp_3880_;
}
v_reusejp_3880_:
{
return v___x_3881_;
}
}
}
}
}
else
{
lean_object* v___x_3885_; 
lean_dec_ref(v_cases_3801_);
v___x_3885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3885_, 0, v_result_3802_);
return v___x_3885_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___boxed(lean_object* v_cases_3886_, lean_object* v_result_3887_, lean_object* v_a_3888_, lean_object* v_a_3889_, lean_object* v_a_3890_, lean_object* v_a_3891_, lean_object* v_a_3892_, lean_object* v_a_3893_){
_start:
{
lean_object* v_res_3894_; 
v_res_3894_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v_cases_3886_, v_result_3887_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_, v_a_3892_);
lean_dec(v_a_3892_);
lean_dec_ref(v_a_3891_);
lean_dec(v_a_3890_);
lean_dec_ref(v_a_3889_);
lean_dec(v_a_3888_);
return v_res_3894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop(lean_object* v_00_u03b1_3895_, lean_object* v_cases_3896_, lean_object* v_result_3897_, lean_object* v_a_3898_, lean_object* v_a_3899_, lean_object* v_a_3900_, lean_object* v_a_3901_, lean_object* v_a_3902_){
_start:
{
lean_object* v___x_3904_; 
v___x_3904_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v_cases_3896_, v_result_3897_, v_a_3898_, v_a_3899_, v_a_3900_, v_a_3901_, v_a_3902_);
return v___x_3904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___boxed(lean_object* v_00_u03b1_3905_, lean_object* v_cases_3906_, lean_object* v_result_3907_, lean_object* v_a_3908_, lean_object* v_a_3909_, lean_object* v_a_3910_, lean_object* v_a_3911_, lean_object* v_a_3912_, lean_object* v_a_3913_){
_start:
{
lean_object* v_res_3914_; 
v_res_3914_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop(v_00_u03b1_3905_, v_cases_3906_, v_result_3907_, v_a_3908_, v_a_3909_, v_a_3910_, v_a_3911_, v_a_3912_);
lean_dec(v_a_3912_);
lean_dec_ref(v_a_3911_);
lean_dec(v_a_3910_);
lean_dec_ref(v_a_3909_);
lean_dec(v_a_3908_);
return v_res_3914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult___redArg(lean_object* v_root_3917_, lean_object* v_a_3918_, lean_object* v_a_3919_, lean_object* v_a_3920_, lean_object* v_a_3921_, lean_object* v_a_3922_){
_start:
{
lean_object* v___x_3924_; lean_object* v___x_3925_; 
v___x_3924_ = lean_box(3);
v___x_3925_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_root_3917_, v___x_3924_);
if (lean_obj_tag(v___x_3925_) == 0)
{
lean_object* v___x_3926_; lean_object* v___x_3927_; 
v___x_3926_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_getStarResult___redArg___closed__0));
v___x_3927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3927_, 0, v___x_3926_);
return v___x_3927_;
}
else
{
lean_object* v_val_3928_; lean_object* v___x_3929_; 
v_val_3928_ = lean_ctor_get(v___x_3925_, 0);
lean_inc(v_val_3928_);
lean_dec_ref_known(v___x_3925_, 1);
v___x_3929_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_val_3928_, v_a_3918_, v_a_3919_, v_a_3920_, v_a_3921_, v_a_3922_);
lean_dec(v_val_3928_);
if (lean_obj_tag(v___x_3929_) == 0)
{
lean_object* v_a_3930_; lean_object* v___x_3932_; uint8_t v_isShared_3933_; uint8_t v_isSharedCheck_3941_; 
v_a_3930_ = lean_ctor_get(v___x_3929_, 0);
v_isSharedCheck_3941_ = !lean_is_exclusive(v___x_3929_);
if (v_isSharedCheck_3941_ == 0)
{
v___x_3932_ = v___x_3929_;
v_isShared_3933_ = v_isSharedCheck_3941_;
goto v_resetjp_3931_;
}
else
{
lean_inc(v_a_3930_);
lean_dec(v___x_3929_);
v___x_3932_ = lean_box(0);
v_isShared_3933_ = v_isSharedCheck_3941_;
goto v_resetjp_3931_;
}
v_resetjp_3931_:
{
lean_object* v_fst_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3939_; 
v_fst_3934_ = lean_ctor_get(v_a_3930_, 0);
lean_inc(v_fst_3934_);
lean_dec(v_a_3930_);
v___x_3935_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_getStarResult___redArg___closed__0));
v___x_3936_ = lean_unsigned_to_nat(1u);
v___x_3937_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v___x_3935_, v___x_3936_, v_fst_3934_);
if (v_isShared_3933_ == 0)
{
lean_ctor_set(v___x_3932_, 0, v___x_3937_);
v___x_3939_ = v___x_3932_;
goto v_reusejp_3938_;
}
else
{
lean_object* v_reuseFailAlloc_3940_; 
v_reuseFailAlloc_3940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3940_, 0, v___x_3937_);
v___x_3939_ = v_reuseFailAlloc_3940_;
goto v_reusejp_3938_;
}
v_reusejp_3938_:
{
return v___x_3939_;
}
}
}
else
{
lean_object* v_a_3942_; lean_object* v___x_3944_; uint8_t v_isShared_3945_; uint8_t v_isSharedCheck_3949_; 
v_a_3942_ = lean_ctor_get(v___x_3929_, 0);
v_isSharedCheck_3949_ = !lean_is_exclusive(v___x_3929_);
if (v_isSharedCheck_3949_ == 0)
{
v___x_3944_ = v___x_3929_;
v_isShared_3945_ = v_isSharedCheck_3949_;
goto v_resetjp_3943_;
}
else
{
lean_inc(v_a_3942_);
lean_dec(v___x_3929_);
v___x_3944_ = lean_box(0);
v_isShared_3945_ = v_isSharedCheck_3949_;
goto v_resetjp_3943_;
}
v_resetjp_3943_:
{
lean_object* v___x_3947_; 
if (v_isShared_3945_ == 0)
{
v___x_3947_ = v___x_3944_;
goto v_reusejp_3946_;
}
else
{
lean_object* v_reuseFailAlloc_3948_; 
v_reuseFailAlloc_3948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3948_, 0, v_a_3942_);
v___x_3947_ = v_reuseFailAlloc_3948_;
goto v_reusejp_3946_;
}
v_reusejp_3946_:
{
return v___x_3947_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult___redArg___boxed(lean_object* v_root_3950_, lean_object* v_a_3951_, lean_object* v_a_3952_, lean_object* v_a_3953_, lean_object* v_a_3954_, lean_object* v_a_3955_, lean_object* v_a_3956_){
_start:
{
lean_object* v_res_3957_; 
v_res_3957_ = l_Lean_Meta_LazyDiscrTree_getStarResult___redArg(v_root_3950_, v_a_3951_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_);
lean_dec(v_a_3955_);
lean_dec_ref(v_a_3954_);
lean_dec(v_a_3953_);
lean_dec_ref(v_a_3952_);
lean_dec(v_a_3951_);
lean_dec_ref(v_root_3950_);
return v_res_3957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult(lean_object* v_00_u03b1_3958_, lean_object* v_root_3959_, lean_object* v_a_3960_, lean_object* v_a_3961_, lean_object* v_a_3962_, lean_object* v_a_3963_, lean_object* v_a_3964_){
_start:
{
lean_object* v___x_3966_; 
v___x_3966_ = l_Lean_Meta_LazyDiscrTree_getStarResult___redArg(v_root_3959_, v_a_3960_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_);
return v___x_3966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult___boxed(lean_object* v_00_u03b1_3967_, lean_object* v_root_3968_, lean_object* v_a_3969_, lean_object* v_a_3970_, lean_object* v_a_3971_, lean_object* v_a_3972_, lean_object* v_a_3973_, lean_object* v_a_3974_){
_start:
{
lean_object* v_res_3975_; 
v_res_3975_ = l_Lean_Meta_LazyDiscrTree_getStarResult(v_00_u03b1_3967_, v_root_3968_, v_a_3969_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_);
lean_dec(v_a_3973_);
lean_dec_ref(v_a_3972_);
lean_dec(v_a_3971_);
lean_dec_ref(v_a_3970_);
lean_dec(v_a_3969_);
lean_dec_ref(v_root_3968_);
return v_res_3975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushRootCase(lean_object* v_r_3976_, lean_object* v_k_3977_, lean_object* v_args_3978_, lean_object* v_cases_3979_){
_start:
{
lean_object* v___x_3980_; 
v___x_3980_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_r_3976_, v_k_3977_);
if (lean_obj_tag(v___x_3980_) == 0)
{
lean_dec_ref(v_args_3978_);
return v_cases_3979_;
}
else
{
lean_object* v_val_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; 
v_val_3981_ = lean_ctor_get(v___x_3980_, 0);
lean_inc(v_val_3981_);
lean_dec_ref_known(v___x_3980_, 1);
v___x_3982_ = lean_unsigned_to_nat(1u);
v___x_3983_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3983_, 0, v_args_3978_);
lean_ctor_set(v___x_3983_, 1, v___x_3982_);
lean_ctor_set(v___x_3983_, 2, v_val_3981_);
v___x_3984_ = lean_array_push(v_cases_3979_, v___x_3983_);
return v___x_3984_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushRootCase___boxed(lean_object* v_r_3985_, lean_object* v_k_3986_, lean_object* v_args_3987_, lean_object* v_cases_3988_){
_start:
{
lean_object* v_res_3989_; 
v_res_3989_ = l_Lean_Meta_LazyDiscrTree_pushRootCase(v_r_3985_, v_k_3986_, v_args_3987_, v_cases_3988_);
lean_dec(v_k_3986_);
lean_dec_ref(v_r_3985_);
return v_res_3989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg(lean_object* v_root_3992_, lean_object* v_e_3993_, lean_object* v_a_3994_, lean_object* v_a_3995_, lean_object* v_a_3996_, lean_object* v_a_3997_, lean_object* v_a_3998_){
_start:
{
lean_object* v___x_4000_; 
v___x_4000_ = l_Lean_Meta_LazyDiscrTree_getStarResult___redArg(v_root_3992_, v_a_3994_, v_a_3995_, v_a_3996_, v_a_3997_, v_a_3998_);
if (lean_obj_tag(v___x_4000_) == 0)
{
lean_object* v_a_4001_; uint8_t v___x_4002_; lean_object* v___x_4003_; 
v_a_4001_ = lean_ctor_get(v___x_4000_, 0);
lean_inc(v_a_4001_);
lean_dec_ref_known(v___x_4000_, 1);
v___x_4002_ = 1;
v___x_4003_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_3993_, v___x_4002_, v___x_4002_, v_a_3995_, v_a_3996_, v_a_3997_, v_a_3998_);
if (lean_obj_tag(v___x_4003_) == 0)
{
lean_object* v_a_4004_; lean_object* v_fst_4005_; 
v_a_4004_ = lean_ctor_get(v___x_4003_, 0);
lean_inc(v_a_4004_);
lean_dec_ref_known(v___x_4003_, 1);
v_fst_4005_ = lean_ctor_get(v_a_4004_, 0);
lean_inc(v_fst_4005_);
switch(lean_obj_tag(v_fst_4005_))
{
case 3:
{
lean_object* v___x_4006_; lean_object* v___x_4007_; 
lean_dec(v_a_4004_);
v___x_4006_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg___closed__0));
v___x_4007_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v___x_4006_, v_a_4001_, v_a_3994_, v_a_3995_, v_a_3996_, v_a_3997_, v_a_3998_);
return v___x_4007_;
}
case 5:
{
lean_object* v_snd_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; 
v_snd_4008_ = lean_ctor_get(v_a_4004_, 1);
lean_inc(v_snd_4008_);
lean_dec(v_a_4004_);
v___x_4009_ = lean_box(4);
v___x_4010_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
v___x_4011_ = l_Lean_Meta_LazyDiscrTree_pushRootCase(v_root_3992_, v___x_4009_, v___x_4010_, v___x_4010_);
v___x_4012_ = l_Lean_Meta_LazyDiscrTree_pushRootCase(v_root_3992_, v_fst_4005_, v_snd_4008_, v___x_4011_);
v___x_4013_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v___x_4012_, v_a_4001_, v_a_3994_, v_a_3995_, v_a_3996_, v_a_3997_, v_a_3998_);
return v___x_4013_;
}
default: 
{
lean_object* v_snd_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; 
v_snd_4014_ = lean_ctor_get(v_a_4004_, 1);
lean_inc(v_snd_4014_);
lean_dec(v_a_4004_);
v___x_4015_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg___closed__0));
v___x_4016_ = l_Lean_Meta_LazyDiscrTree_pushRootCase(v_root_3992_, v_fst_4005_, v_snd_4014_, v___x_4015_);
lean_dec(v_fst_4005_);
v___x_4017_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v___x_4016_, v_a_4001_, v_a_3994_, v_a_3995_, v_a_3996_, v_a_3997_, v_a_3998_);
return v___x_4017_;
}
}
}
else
{
lean_object* v_a_4018_; lean_object* v___x_4020_; uint8_t v_isShared_4021_; uint8_t v_isSharedCheck_4025_; 
lean_dec(v_a_4001_);
v_a_4018_ = lean_ctor_get(v___x_4003_, 0);
v_isSharedCheck_4025_ = !lean_is_exclusive(v___x_4003_);
if (v_isSharedCheck_4025_ == 0)
{
v___x_4020_ = v___x_4003_;
v_isShared_4021_ = v_isSharedCheck_4025_;
goto v_resetjp_4019_;
}
else
{
lean_inc(v_a_4018_);
lean_dec(v___x_4003_);
v___x_4020_ = lean_box(0);
v_isShared_4021_ = v_isSharedCheck_4025_;
goto v_resetjp_4019_;
}
v_resetjp_4019_:
{
lean_object* v___x_4023_; 
if (v_isShared_4021_ == 0)
{
v___x_4023_ = v___x_4020_;
goto v_reusejp_4022_;
}
else
{
lean_object* v_reuseFailAlloc_4024_; 
v_reuseFailAlloc_4024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4024_, 0, v_a_4018_);
v___x_4023_ = v_reuseFailAlloc_4024_;
goto v_reusejp_4022_;
}
v_reusejp_4022_:
{
return v___x_4023_;
}
}
}
}
else
{
lean_dec_ref(v_e_3993_);
return v___x_4000_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg___boxed(lean_object* v_root_4026_, lean_object* v_e_4027_, lean_object* v_a_4028_, lean_object* v_a_4029_, lean_object* v_a_4030_, lean_object* v_a_4031_, lean_object* v_a_4032_, lean_object* v_a_4033_){
_start:
{
lean_object* v_res_4034_; 
v_res_4034_ = l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg(v_root_4026_, v_e_4027_, v_a_4028_, v_a_4029_, v_a_4030_, v_a_4031_, v_a_4032_);
lean_dec(v_a_4032_);
lean_dec_ref(v_a_4031_);
lean_dec(v_a_4030_);
lean_dec_ref(v_a_4029_);
lean_dec(v_a_4028_);
lean_dec_ref(v_root_4026_);
return v_res_4034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore(lean_object* v_00_u03b1_4035_, lean_object* v_root_4036_, lean_object* v_e_4037_, lean_object* v_a_4038_, lean_object* v_a_4039_, lean_object* v_a_4040_, lean_object* v_a_4041_, lean_object* v_a_4042_){
_start:
{
lean_object* v___x_4044_; 
v___x_4044_ = l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg(v_root_4036_, v_e_4037_, v_a_4038_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_);
return v___x_4044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore___boxed(lean_object* v_00_u03b1_4045_, lean_object* v_root_4046_, lean_object* v_e_4047_, lean_object* v_a_4048_, lean_object* v_a_4049_, lean_object* v_a_4050_, lean_object* v_a_4051_, lean_object* v_a_4052_, lean_object* v_a_4053_){
_start:
{
lean_object* v_res_4054_; 
v_res_4054_ = l_Lean_Meta_LazyDiscrTree_getMatchCore(v_00_u03b1_4045_, v_root_4046_, v_e_4047_, v_a_4048_, v_a_4049_, v_a_4050_, v_a_4051_, v_a_4052_);
lean_dec(v_a_4052_);
lean_dec_ref(v_a_4051_);
lean_dec(v_a_4050_);
lean_dec_ref(v_a_4049_);
lean_dec(v_a_4048_);
lean_dec_ref(v_root_4046_);
return v_res_4054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch___redArg(lean_object* v_d_4055_, lean_object* v_e_4056_, lean_object* v_a_4057_, lean_object* v_a_4058_, lean_object* v_a_4059_, lean_object* v_a_4060_){
_start:
{
lean_object* v___y_4063_; lean_object* v_roots_4080_; lean_object* v___x_4081_; uint8_t v_transparency_4082_; lean_object* v___x_4083_; uint8_t v___x_4084_; uint8_t v___x_4085_; 
v_roots_4080_ = lean_ctor_get(v_d_4055_, 1);
v___x_4081_ = l_Lean_Meta_Context_config(v_a_4057_);
v_transparency_4082_ = lean_ctor_get_uint8(v___x_4081_, 9);
lean_dec_ref(v___x_4081_);
lean_inc_ref(v_roots_4080_);
v___x_4083_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getMatchCore___boxed), 9, 3);
lean_closure_set(v___x_4083_, 0, lean_box(0));
lean_closure_set(v___x_4083_, 1, v_roots_4080_);
lean_closure_set(v___x_4083_, 2, v_e_4056_);
v___x_4084_ = 2;
v___x_4085_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_4082_, v___x_4084_);
if (v___x_4085_ == 0)
{
lean_object* v_keyedConfig_4086_; uint8_t v_trackZetaDelta_4087_; lean_object* v_zetaDeltaSet_4088_; lean_object* v_lctx_4089_; lean_object* v_localInstances_4090_; lean_object* v_defEqCtx_x3f_4091_; lean_object* v_synthPendingDepth_4092_; lean_object* v_customCanUnfoldPredicate_x3f_4093_; uint8_t v_univApprox_4094_; uint8_t v_inTypeClassResolution_4095_; uint8_t v_cacheInferType_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; 
v_keyedConfig_4086_ = lean_ctor_get(v_a_4057_, 0);
v_trackZetaDelta_4087_ = lean_ctor_get_uint8(v_a_4057_, sizeof(void*)*7);
v_zetaDeltaSet_4088_ = lean_ctor_get(v_a_4057_, 1);
v_lctx_4089_ = lean_ctor_get(v_a_4057_, 2);
v_localInstances_4090_ = lean_ctor_get(v_a_4057_, 3);
v_defEqCtx_x3f_4091_ = lean_ctor_get(v_a_4057_, 4);
v_synthPendingDepth_4092_ = lean_ctor_get(v_a_4057_, 5);
v_customCanUnfoldPredicate_x3f_4093_ = lean_ctor_get(v_a_4057_, 6);
v_univApprox_4094_ = lean_ctor_get_uint8(v_a_4057_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4095_ = lean_ctor_get_uint8(v_a_4057_, sizeof(void*)*7 + 2);
v_cacheInferType_4096_ = lean_ctor_get_uint8(v_a_4057_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_4086_);
v___x_4097_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4084_, v_keyedConfig_4086_);
lean_inc(v_customCanUnfoldPredicate_x3f_4093_);
lean_inc(v_synthPendingDepth_4092_);
lean_inc(v_defEqCtx_x3f_4091_);
lean_inc_ref(v_localInstances_4090_);
lean_inc_ref(v_lctx_4089_);
lean_inc(v_zetaDeltaSet_4088_);
v___x_4098_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4098_, 0, v___x_4097_);
lean_ctor_set(v___x_4098_, 1, v_zetaDeltaSet_4088_);
lean_ctor_set(v___x_4098_, 2, v_lctx_4089_);
lean_ctor_set(v___x_4098_, 3, v_localInstances_4090_);
lean_ctor_set(v___x_4098_, 4, v_defEqCtx_x3f_4091_);
lean_ctor_set(v___x_4098_, 5, v_synthPendingDepth_4092_);
lean_ctor_set(v___x_4098_, 6, v_customCanUnfoldPredicate_x3f_4093_);
lean_ctor_set_uint8(v___x_4098_, sizeof(void*)*7, v_trackZetaDelta_4087_);
lean_ctor_set_uint8(v___x_4098_, sizeof(void*)*7 + 1, v_univApprox_4094_);
lean_ctor_set_uint8(v___x_4098_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4095_);
lean_ctor_set_uint8(v___x_4098_, sizeof(void*)*7 + 3, v_cacheInferType_4096_);
v___x_4099_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_d_4055_, v___x_4083_, v___x_4098_, v_a_4058_, v_a_4059_, v_a_4060_);
lean_dec_ref_known(v___x_4098_, 7);
v___y_4063_ = v___x_4099_;
goto v___jp_4062_;
}
else
{
lean_object* v___x_4100_; 
v___x_4100_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_d_4055_, v___x_4083_, v_a_4057_, v_a_4058_, v_a_4059_, v_a_4060_);
v___y_4063_ = v___x_4100_;
goto v___jp_4062_;
}
v___jp_4062_:
{
if (lean_obj_tag(v___y_4063_) == 0)
{
lean_object* v_a_4064_; lean_object* v___x_4066_; uint8_t v_isShared_4067_; uint8_t v_isSharedCheck_4071_; 
v_a_4064_ = lean_ctor_get(v___y_4063_, 0);
v_isSharedCheck_4071_ = !lean_is_exclusive(v___y_4063_);
if (v_isSharedCheck_4071_ == 0)
{
v___x_4066_ = v___y_4063_;
v_isShared_4067_ = v_isSharedCheck_4071_;
goto v_resetjp_4065_;
}
else
{
lean_inc(v_a_4064_);
lean_dec(v___y_4063_);
v___x_4066_ = lean_box(0);
v_isShared_4067_ = v_isSharedCheck_4071_;
goto v_resetjp_4065_;
}
v_resetjp_4065_:
{
lean_object* v___x_4069_; 
if (v_isShared_4067_ == 0)
{
v___x_4069_ = v___x_4066_;
goto v_reusejp_4068_;
}
else
{
lean_object* v_reuseFailAlloc_4070_; 
v_reuseFailAlloc_4070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4070_, 0, v_a_4064_);
v___x_4069_ = v_reuseFailAlloc_4070_;
goto v_reusejp_4068_;
}
v_reusejp_4068_:
{
return v___x_4069_;
}
}
}
else
{
lean_object* v_a_4072_; lean_object* v___x_4074_; uint8_t v_isShared_4075_; uint8_t v_isSharedCheck_4079_; 
v_a_4072_ = lean_ctor_get(v___y_4063_, 0);
v_isSharedCheck_4079_ = !lean_is_exclusive(v___y_4063_);
if (v_isSharedCheck_4079_ == 0)
{
v___x_4074_ = v___y_4063_;
v_isShared_4075_ = v_isSharedCheck_4079_;
goto v_resetjp_4073_;
}
else
{
lean_inc(v_a_4072_);
lean_dec(v___y_4063_);
v___x_4074_ = lean_box(0);
v_isShared_4075_ = v_isSharedCheck_4079_;
goto v_resetjp_4073_;
}
v_resetjp_4073_:
{
lean_object* v___x_4077_; 
if (v_isShared_4075_ == 0)
{
v___x_4077_ = v___x_4074_;
goto v_reusejp_4076_;
}
else
{
lean_object* v_reuseFailAlloc_4078_; 
v_reuseFailAlloc_4078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4078_, 0, v_a_4072_);
v___x_4077_ = v_reuseFailAlloc_4078_;
goto v_reusejp_4076_;
}
v_reusejp_4076_:
{
return v___x_4077_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch___redArg___boxed(lean_object* v_d_4101_, lean_object* v_e_4102_, lean_object* v_a_4103_, lean_object* v_a_4104_, lean_object* v_a_4105_, lean_object* v_a_4106_, lean_object* v_a_4107_){
_start:
{
lean_object* v_res_4108_; 
v_res_4108_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v_d_4101_, v_e_4102_, v_a_4103_, v_a_4104_, v_a_4105_, v_a_4106_);
lean_dec(v_a_4106_);
lean_dec_ref(v_a_4105_);
lean_dec(v_a_4104_);
lean_dec_ref(v_a_4103_);
return v_res_4108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch(lean_object* v_00_u03b1_4109_, lean_object* v_d_4110_, lean_object* v_e_4111_, lean_object* v_a_4112_, lean_object* v_a_4113_, lean_object* v_a_4114_, lean_object* v_a_4115_){
_start:
{
lean_object* v___x_4117_; 
v___x_4117_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v_d_4110_, v_e_4111_, v_a_4112_, v_a_4113_, v_a_4114_, v_a_4115_);
return v___x_4117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch___boxed(lean_object* v_00_u03b1_4118_, lean_object* v_d_4119_, lean_object* v_e_4120_, lean_object* v_a_4121_, lean_object* v_a_4122_, lean_object* v_a_4123_, lean_object* v_a_4124_, lean_object* v_a_4125_){
_start:
{
lean_object* v_res_4126_; 
v_res_4126_ = l_Lean_Meta_LazyDiscrTree_getMatch(v_00_u03b1_4118_, v_d_4119_, v_e_4120_, v_a_4121_, v_a_4122_, v_a_4123_, v_a_4124_);
lean_dec(v_a_4124_);
lean_dec_ref(v_a_4123_);
lean_dec(v_a_4122_);
lean_dec_ref(v_a_4121_);
return v_res_4126_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1(void){
_start:
{
lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; 
v___x_4129_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__0));
v___x_4130_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2);
v___x_4131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4131_, 0, v___x_4130_);
lean_ctor_set(v___x_4131_, 1, v___x_4129_);
return v___x_4131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg(){
_start:
{
lean_object* v___x_4133_; 
v___x_4133_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1);
return v___x_4133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___boxed(lean_object* v___dummy_4134_){
_start:
{
lean_object* v_res_4135_; 
v_res_4135_ = l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg();
return v_res_4135_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0(void){
_start:
{
lean_object* v___x_4136_; 
v___x_4136_ = l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg();
return v___x_4136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default(lean_object* v_00_u03b1_4137_){
_start:
{
lean_object* v___x_4138_; 
v___x_4138_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0);
return v___x_4138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___redArg(){
_start:
{
lean_object* v___x_4140_; 
v___x_4140_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0);
return v___x_4140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___redArg___boxed(lean_object* v___dummy_4141_){
_start:
{
lean_object* v_res_4142_; 
v_res_4142_ = l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___redArg();
return v_res_4142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree(lean_object* v_a_4143_){
_start:
{
lean_object* v___x_4144_; 
v___x_4144_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0);
return v___x_4144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(lean_object* v_d_4145_, lean_object* v_k_4146_, lean_object* v_f_4147_){
_start:
{
lean_object* v_roots_4148_; lean_object* v_tries_4149_; lean_object* v___x_4150_; 
v_roots_4148_ = lean_ctor_get(v_d_4145_, 0);
v_tries_4149_ = lean_ctor_get(v_d_4145_, 1);
v___x_4150_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_roots_4148_, v_k_4146_);
if (lean_obj_tag(v___x_4150_) == 0)
{
lean_object* v___x_4152_; uint8_t v_isShared_4153_; uint8_t v_isSharedCheck_4162_; 
lean_inc_ref(v_tries_4149_);
lean_inc_ref(v_roots_4148_);
v_isSharedCheck_4162_ = !lean_is_exclusive(v_d_4145_);
if (v_isSharedCheck_4162_ == 0)
{
lean_object* v_unused_4163_; lean_object* v_unused_4164_; 
v_unused_4163_ = lean_ctor_get(v_d_4145_, 1);
lean_dec(v_unused_4163_);
v_unused_4164_ = lean_ctor_get(v_d_4145_, 0);
lean_dec(v_unused_4164_);
v___x_4152_ = v_d_4145_;
v_isShared_4153_ = v_isSharedCheck_4162_;
goto v_resetjp_4151_;
}
else
{
lean_dec(v_d_4145_);
v___x_4152_ = lean_box(0);
v_isShared_4153_ = v_isSharedCheck_4162_;
goto v_resetjp_4151_;
}
v_resetjp_4151_:
{
lean_object* v___x_4154_; lean_object* v_roots_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4160_; 
v___x_4154_ = lean_array_get_size(v_tries_4149_);
v_roots_4155_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_roots_4148_, v_k_4146_, v___x_4154_);
v___x_4156_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__3));
v___x_4157_ = lean_apply_1(v_f_4147_, v___x_4156_);
v___x_4158_ = lean_array_push(v_tries_4149_, v___x_4157_);
if (v_isShared_4153_ == 0)
{
lean_ctor_set(v___x_4152_, 1, v___x_4158_);
lean_ctor_set(v___x_4152_, 0, v_roots_4155_);
v___x_4160_ = v___x_4152_;
goto v_reusejp_4159_;
}
else
{
lean_object* v_reuseFailAlloc_4161_; 
v_reuseFailAlloc_4161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4161_, 0, v_roots_4155_);
lean_ctor_set(v_reuseFailAlloc_4161_, 1, v___x_4158_);
v___x_4160_ = v_reuseFailAlloc_4161_;
goto v_reusejp_4159_;
}
v_reusejp_4159_:
{
return v___x_4160_;
}
}
}
else
{
lean_object* v_val_4165_; lean_object* v___x_4166_; uint8_t v___x_4167_; 
lean_dec(v_k_4146_);
v_val_4165_ = lean_ctor_get(v___x_4150_, 0);
lean_inc(v_val_4165_);
lean_dec_ref_known(v___x_4150_, 1);
v___x_4166_ = lean_array_get_size(v_tries_4149_);
v___x_4167_ = lean_nat_dec_lt(v_val_4165_, v___x_4166_);
if (v___x_4167_ == 0)
{
lean_dec(v_val_4165_);
lean_dec_ref(v_f_4147_);
return v_d_4145_;
}
else
{
lean_object* v___x_4169_; uint8_t v_isShared_4170_; uint8_t v_isSharedCheck_4179_; 
lean_inc_ref(v_tries_4149_);
lean_inc_ref(v_roots_4148_);
v_isSharedCheck_4179_ = !lean_is_exclusive(v_d_4145_);
if (v_isSharedCheck_4179_ == 0)
{
lean_object* v_unused_4180_; lean_object* v_unused_4181_; 
v_unused_4180_ = lean_ctor_get(v_d_4145_, 1);
lean_dec(v_unused_4180_);
v_unused_4181_ = lean_ctor_get(v_d_4145_, 0);
lean_dec(v_unused_4181_);
v___x_4169_ = v_d_4145_;
v_isShared_4170_ = v_isSharedCheck_4179_;
goto v_resetjp_4168_;
}
else
{
lean_dec(v_d_4145_);
v___x_4169_ = lean_box(0);
v_isShared_4170_ = v_isSharedCheck_4179_;
goto v_resetjp_4168_;
}
v_resetjp_4168_:
{
lean_object* v_v_4171_; lean_object* v___x_4172_; lean_object* v_xs_x27_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4177_; 
v_v_4171_ = lean_array_fget(v_tries_4149_, v_val_4165_);
v___x_4172_ = lean_box(0);
v_xs_x27_4173_ = lean_array_fset(v_tries_4149_, v_val_4165_, v___x_4172_);
v___x_4174_ = lean_apply_1(v_f_4147_, v_v_4171_);
v___x_4175_ = lean_array_fset(v_xs_x27_4173_, v_val_4165_, v___x_4174_);
lean_dec(v_val_4165_);
if (v_isShared_4170_ == 0)
{
lean_ctor_set(v___x_4169_, 1, v___x_4175_);
v___x_4177_ = v___x_4169_;
goto v_reusejp_4176_;
}
else
{
lean_object* v_reuseFailAlloc_4178_; 
v_reuseFailAlloc_4178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4178_, 0, v_roots_4148_);
lean_ctor_set(v_reuseFailAlloc_4178_, 1, v___x_4175_);
v___x_4177_ = v_reuseFailAlloc_4178_;
goto v_reusejp_4176_;
}
v_reusejp_4176_:
{
return v___x_4177_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt(lean_object* v_00_u03b1_4182_, lean_object* v_d_4183_, lean_object* v_k_4184_, lean_object* v_f_4185_){
_start:
{
lean_object* v___x_4186_; 
v___x_4186_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(v_d_4183_, v_k_4184_, v_f_4185_);
return v___x_4186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg___lam__0(lean_object* v_e_4187_, lean_object* v_x_4188_){
_start:
{
lean_object* v___x_4189_; 
v___x_4189_ = lean_array_push(v_x_4188_, v_e_4187_);
return v___x_4189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg(lean_object* v_d_4190_, lean_object* v_k_4191_, lean_object* v_e_4192_){
_start:
{
lean_object* v___f_4193_; lean_object* v___x_4194_; 
v___f_4193_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4193_, 0, v_e_4192_);
v___x_4194_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(v_d_4190_, v_k_4191_, v___f_4193_);
return v___x_4194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push(lean_object* v_00_u03b1_4195_, lean_object* v_d_4196_, lean_object* v_k_4197_, lean_object* v_e_4198_){
_start:
{
lean_object* v___x_4199_; 
v___x_4199_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg(v_d_4196_, v_k_4197_, v_e_4198_);
return v___x_4199_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(size_t v_sz_4200_, size_t v_i_4201_, lean_object* v_bs_4202_){
_start:
{
uint8_t v___x_4203_; 
v___x_4203_ = lean_usize_dec_lt(v_i_4201_, v_sz_4200_);
if (v___x_4203_ == 0)
{
return v_bs_4202_;
}
else
{
lean_object* v_v_4204_; lean_object* v___x_4205_; lean_object* v_bs_x27_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; size_t v___x_4210_; size_t v___x_4211_; lean_object* v___x_4212_; 
v_v_4204_ = lean_array_uget(v_bs_4202_, v_i_4201_);
v___x_4205_ = lean_unsigned_to_nat(0u);
v_bs_x27_4206_ = lean_array_uset(v_bs_4202_, v_i_4201_, v___x_4205_);
v___x_4207_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__0));
v___x_4208_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2);
v___x_4209_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4209_, 0, v___x_4207_);
lean_ctor_set(v___x_4209_, 1, v___x_4205_);
lean_ctor_set(v___x_4209_, 2, v___x_4208_);
lean_ctor_set(v___x_4209_, 3, v_v_4204_);
v___x_4210_ = ((size_t)1ULL);
v___x_4211_ = lean_usize_add(v_i_4201_, v___x_4210_);
v___x_4212_ = lean_array_uset(v_bs_x27_4206_, v_i_4201_, v___x_4209_);
v_i_4201_ = v___x_4211_;
v_bs_4202_ = v___x_4212_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg___boxed(lean_object* v_sz_4214_, lean_object* v_i_4215_, lean_object* v_bs_4216_){
_start:
{
size_t v_sz_boxed_4217_; size_t v_i_boxed_4218_; lean_object* v_res_4219_; 
v_sz_boxed_4217_ = lean_unbox_usize(v_sz_4214_);
lean_dec(v_sz_4214_);
v_i_boxed_4218_ = lean_unbox_usize(v_i_4215_);
lean_dec(v_i_4215_);
v_res_4219_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(v_sz_boxed_4217_, v_i_boxed_4218_, v_bs_4216_);
return v_res_4219_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__1(lean_object* v_x_4220_, lean_object* v_x_4221_){
_start:
{
if (lean_obj_tag(v_x_4221_) == 0)
{
return v_x_4220_;
}
else
{
lean_object* v_key_4222_; lean_object* v_value_4223_; lean_object* v_tail_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; 
v_key_4222_ = lean_ctor_get(v_x_4221_, 0);
lean_inc(v_key_4222_);
v_value_4223_ = lean_ctor_get(v_x_4221_, 1);
lean_inc(v_value_4223_);
v_tail_4224_ = lean_ctor_get(v_x_4221_, 2);
lean_inc(v_tail_4224_);
lean_dec_ref_known(v_x_4221_, 3);
v___x_4225_ = lean_unsigned_to_nat(1u);
v___x_4226_ = lean_nat_add(v_value_4223_, v___x_4225_);
lean_dec(v_value_4223_);
v___x_4227_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_x_4220_, v_key_4222_, v___x_4226_);
v_x_4220_ = v___x_4227_;
v_x_4221_ = v_tail_4224_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(lean_object* v_as_4229_, size_t v_i_4230_, size_t v_stop_4231_, lean_object* v_b_4232_){
_start:
{
uint8_t v___x_4233_; 
v___x_4233_ = lean_usize_dec_eq(v_i_4230_, v_stop_4231_);
if (v___x_4233_ == 0)
{
lean_object* v___x_4234_; lean_object* v___x_4235_; size_t v___x_4236_; size_t v___x_4237_; 
v___x_4234_ = lean_array_uget_borrowed(v_as_4229_, v_i_4230_);
lean_inc(v___x_4234_);
v___x_4235_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__1(v_b_4232_, v___x_4234_);
v___x_4236_ = ((size_t)1ULL);
v___x_4237_ = lean_usize_add(v_i_4230_, v___x_4236_);
v_i_4230_ = v___x_4237_;
v_b_4232_ = v___x_4235_;
goto _start;
}
else
{
return v_b_4232_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2___boxed(lean_object* v_as_4239_, lean_object* v_i_4240_, lean_object* v_stop_4241_, lean_object* v_b_4242_){
_start:
{
size_t v_i_boxed_4243_; size_t v_stop_boxed_4244_; lean_object* v_res_4245_; 
v_i_boxed_4243_ = lean_unbox_usize(v_i_4240_);
lean_dec(v_i_4240_);
v_stop_boxed_4244_ = lean_unbox_usize(v_stop_4241_);
lean_dec(v_stop_4241_);
v_res_4245_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(v_as_4239_, v_i_boxed_4243_, v_stop_boxed_4244_, v_b_4242_);
lean_dec_ref(v_as_4239_);
return v_res_4245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(lean_object* v_d_4246_){
_start:
{
lean_object* v_roots_4247_; lean_object* v_tries_4248_; lean_object* v___x_4250_; uint8_t v_isShared_4251_; uint8_t v_isSharedCheck_4271_; 
v_roots_4247_ = lean_ctor_get(v_d_4246_, 0);
v_tries_4248_ = lean_ctor_get(v_d_4246_, 1);
v_isSharedCheck_4271_ = !lean_is_exclusive(v_d_4246_);
if (v_isSharedCheck_4271_ == 0)
{
v___x_4250_ = v_d_4246_;
v_isShared_4251_ = v_isSharedCheck_4271_;
goto v_resetjp_4249_;
}
else
{
lean_inc(v_tries_4248_);
lean_inc(v_roots_4247_);
lean_dec(v_d_4246_);
v___x_4250_ = lean_box(0);
v_isShared_4251_ = v_isSharedCheck_4271_;
goto v_resetjp_4249_;
}
v_resetjp_4249_:
{
lean_object* v___y_4253_; lean_object* v_buckets_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; uint8_t v___x_4267_; 
v_buckets_4264_ = lean_ctor_get(v_roots_4247_, 1);
v___x_4265_ = lean_unsigned_to_nat(0u);
v___x_4266_ = lean_array_get_size(v_buckets_4264_);
v___x_4267_ = lean_nat_dec_lt(v___x_4265_, v___x_4266_);
if (v___x_4267_ == 0)
{
v___y_4253_ = v_roots_4247_;
goto v___jp_4252_;
}
else
{
size_t v___x_4268_; size_t v___x_4269_; lean_object* v___x_4270_; 
lean_inc_ref(v_buckets_4264_);
v___x_4268_ = ((size_t)0ULL);
v___x_4269_ = lean_usize_of_nat(v___x_4266_);
v___x_4270_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(v_buckets_4264_, v___x_4268_, v___x_4269_, v_roots_4247_);
lean_dec_ref(v_buckets_4264_);
v___y_4253_ = v___x_4270_;
goto v___jp_4252_;
}
v___jp_4252_:
{
lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; size_t v_sz_4257_; size_t v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4262_; 
v___x_4254_ = lean_unsigned_to_nat(1u);
v___x_4255_ = lean_mk_empty_array_with_capacity(v___x_4254_);
lean_dec_ref(v___x_4255_);
v___x_4256_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__0);
v_sz_4257_ = lean_array_size(v_tries_4248_);
v___x_4258_ = ((size_t)0ULL);
v___x_4259_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(v_sz_4257_, v___x_4258_, v_tries_4248_);
v___x_4260_ = l_Array_append___redArg(v___x_4256_, v___x_4259_);
lean_dec_ref(v___x_4259_);
if (v_isShared_4251_ == 0)
{
lean_ctor_set(v___x_4250_, 1, v___y_4253_);
lean_ctor_set(v___x_4250_, 0, v___x_4260_);
v___x_4262_ = v___x_4250_;
goto v_reusejp_4261_;
}
else
{
lean_object* v_reuseFailAlloc_4263_; 
v_reuseFailAlloc_4263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4263_, 0, v___x_4260_);
lean_ctor_set(v_reuseFailAlloc_4263_, 1, v___y_4253_);
v___x_4262_ = v_reuseFailAlloc_4263_;
goto v_reusejp_4261_;
}
v_reusejp_4261_:
{
return v___x_4262_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy(lean_object* v_00_u03b1_4272_, lean_object* v_d_4273_){
_start:
{
lean_object* v___x_4274_; 
v___x_4274_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_d_4273_);
return v___x_4274_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0(lean_object* v_00_u03b1_4275_, size_t v_sz_4276_, size_t v_i_4277_, lean_object* v_bs_4278_){
_start:
{
lean_object* v___x_4279_; 
v___x_4279_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(v_sz_4276_, v_i_4277_, v_bs_4278_);
return v___x_4279_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___boxed(lean_object* v_00_u03b1_4280_, lean_object* v_sz_4281_, lean_object* v_i_4282_, lean_object* v_bs_4283_){
_start:
{
size_t v_sz_boxed_4284_; size_t v_i_boxed_4285_; lean_object* v_res_4286_; 
v_sz_boxed_4284_ = lean_unbox_usize(v_sz_4281_);
lean_dec(v_sz_4281_);
v_i_boxed_4285_ = lean_unbox_usize(v_i_4282_);
lean_dec(v_i_4282_);
v_res_4286_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0(v_00_u03b1_4280_, v_sz_boxed_4284_, v_i_boxed_4285_, v_bs_4283_);
return v_res_4286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___lam__0(lean_object* v_y_4287_, lean_object* v_x_4288_){
_start:
{
lean_object* v___x_4289_; 
v___x_4289_ = l_Array_append___redArg(v_x_4288_, v_y_4287_);
return v___x_4289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___lam__0___boxed(lean_object* v_y_4290_, lean_object* v_x_4291_){
_start:
{
lean_object* v_res_4292_; 
v_res_4292_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___lam__0(v_y_4290_, v_x_4291_);
lean_dec_ref(v_y_4290_);
return v_res_4292_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4293_; 
v___x_4293_ = l_Array_instInhabited___redArg();
return v___x_4293_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(lean_object* v_tries_4294_, lean_object* v_snd_4295_, lean_object* v_x_4296_, lean_object* v_x_4297_){
_start:
{
if (lean_obj_tag(v_x_4297_) == 0)
{
lean_dec_ref(v_snd_4295_);
return v_x_4296_;
}
else
{
lean_object* v_key_4298_; lean_object* v_value_4299_; lean_object* v_tail_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; 
v_key_4298_ = lean_ctor_get(v_x_4297_, 0);
lean_inc(v_key_4298_);
v_value_4299_ = lean_ctor_get(v_x_4297_, 1);
lean_inc(v_value_4299_);
v_tail_4300_ = lean_ctor_get(v_x_4297_, 2);
lean_inc(v_tail_4300_);
lean_dec_ref_known(v_x_4297_, 3);
v___x_4301_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0);
v___x_4302_ = lean_array_get_borrowed(v___x_4301_, v_tries_4294_, v_value_4299_);
lean_dec(v_value_4299_);
lean_inc_ref(v_snd_4295_);
lean_inc(v___x_4302_);
v___x_4303_ = lean_apply_1(v_snd_4295_, v___x_4302_);
v___x_4304_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(v_x_4296_, v_key_4298_, v___x_4303_);
v_x_4296_ = v___x_4304_;
v_x_4297_ = v_tail_4300_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___boxed(lean_object* v_tries_4306_, lean_object* v_snd_4307_, lean_object* v_x_4308_, lean_object* v_x_4309_){
_start:
{
lean_object* v_res_4310_; 
v_res_4310_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(v_tries_4306_, v_snd_4307_, v_x_4308_, v_x_4309_);
lean_dec_ref(v_tries_4306_);
return v_res_4310_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(lean_object* v_tries_4311_, lean_object* v_snd_4312_, lean_object* v_as_4313_, size_t v_i_4314_, size_t v_stop_4315_, lean_object* v_b_4316_){
_start:
{
uint8_t v___x_4317_; 
v___x_4317_ = lean_usize_dec_eq(v_i_4314_, v_stop_4315_);
if (v___x_4317_ == 0)
{
lean_object* v___x_4318_; lean_object* v___x_4319_; size_t v___x_4320_; size_t v___x_4321_; 
v___x_4318_ = lean_array_uget_borrowed(v_as_4313_, v_i_4314_);
lean_inc(v___x_4318_);
lean_inc_ref(v_snd_4312_);
v___x_4319_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(v_tries_4311_, v_snd_4312_, v_b_4316_, v___x_4318_);
v___x_4320_ = ((size_t)1ULL);
v___x_4321_ = lean_usize_add(v_i_4314_, v___x_4320_);
v_i_4314_ = v___x_4321_;
v_b_4316_ = v___x_4319_;
goto _start;
}
else
{
lean_dec_ref(v_snd_4312_);
return v_b_4316_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg___boxed(lean_object* v_tries_4323_, lean_object* v_snd_4324_, lean_object* v_as_4325_, lean_object* v_i_4326_, lean_object* v_stop_4327_, lean_object* v_b_4328_){
_start:
{
size_t v_i_boxed_4329_; size_t v_stop_boxed_4330_; lean_object* v_res_4331_; 
v_i_boxed_4329_ = lean_unbox_usize(v_i_4326_);
lean_dec(v_i_4326_);
v_stop_boxed_4330_ = lean_unbox_usize(v_stop_4327_);
lean_dec(v_stop_4327_);
v_res_4331_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(v_tries_4323_, v_snd_4324_, v_as_4325_, v_i_boxed_4329_, v_stop_boxed_4330_, v_b_4328_);
lean_dec_ref(v_as_4325_);
lean_dec_ref(v_tries_4323_);
return v_res_4331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg(lean_object* v_x_4334_, lean_object* v_y_4335_){
_start:
{
lean_object* v_fst_4337_; lean_object* v_buckets_4338_; lean_object* v_tries_4339_; lean_object* v_snd_4340_; lean_object* v_roots_4347_; lean_object* v_roots_4348_; lean_object* v_tries_4349_; lean_object* v_size_4350_; lean_object* v_buckets_4351_; lean_object* v_tries_4352_; lean_object* v_size_4353_; lean_object* v_buckets_4354_; uint8_t v___x_4355_; 
v_roots_4347_ = lean_ctor_get(v_y_4335_, 0);
v_roots_4348_ = lean_ctor_get(v_x_4334_, 0);
v_tries_4349_ = lean_ctor_get(v_y_4335_, 1);
v_size_4350_ = lean_ctor_get(v_roots_4347_, 0);
v_buckets_4351_ = lean_ctor_get(v_roots_4347_, 1);
v_tries_4352_ = lean_ctor_get(v_x_4334_, 1);
v_size_4353_ = lean_ctor_get(v_roots_4348_, 0);
v_buckets_4354_ = lean_ctor_get(v_roots_4348_, 1);
v___x_4355_ = lean_nat_dec_le(v_size_4350_, v_size_4353_);
if (v___x_4355_ == 0)
{
lean_object* v___f_4356_; 
lean_inc_ref(v_buckets_4354_);
lean_inc_ref(v_tries_4352_);
lean_dec_ref(v_x_4334_);
v___f_4356_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___closed__0));
v_fst_4337_ = v_y_4335_;
v_buckets_4338_ = v_buckets_4354_;
v_tries_4339_ = v_tries_4352_;
v_snd_4340_ = v___f_4356_;
goto v___jp_4336_;
}
else
{
lean_object* v___f_4357_; 
lean_inc_ref(v_buckets_4351_);
lean_inc_ref(v_tries_4349_);
lean_dec_ref(v_y_4335_);
v___f_4357_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___closed__1));
v_fst_4337_ = v_x_4334_;
v_buckets_4338_ = v_buckets_4351_;
v_tries_4339_ = v_tries_4349_;
v_snd_4340_ = v___f_4357_;
goto v___jp_4336_;
}
v___jp_4336_:
{
lean_object* v___x_4341_; lean_object* v___x_4342_; uint8_t v___x_4343_; 
v___x_4341_ = lean_unsigned_to_nat(0u);
v___x_4342_ = lean_array_get_size(v_buckets_4338_);
v___x_4343_ = lean_nat_dec_lt(v___x_4341_, v___x_4342_);
if (v___x_4343_ == 0)
{
lean_dec_ref(v_tries_4339_);
lean_dec_ref(v_buckets_4338_);
return v_fst_4337_;
}
else
{
size_t v___x_4344_; size_t v___x_4345_; lean_object* v___x_4346_; 
v___x_4344_ = ((size_t)0ULL);
v___x_4345_ = lean_usize_of_nat(v___x_4342_);
lean_inc_ref(v_snd_4340_);
v___x_4346_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(v_tries_4339_, v_snd_4340_, v_buckets_4338_, v___x_4344_, v___x_4345_, v_fst_4337_);
lean_dec_ref(v_buckets_4338_);
lean_dec_ref(v_tries_4339_);
return v___x_4346_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append(lean_object* v_00_u03b1_4358_, lean_object* v_x_4359_, lean_object* v_y_4360_){
_start:
{
lean_object* v___x_4361_; 
v___x_4361_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg(v_x_4359_, v_y_4360_);
return v___x_4361_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0(lean_object* v_00_u03b1_4362_, lean_object* v_tries_4363_, lean_object* v_snd_4364_, lean_object* v_x_4365_, lean_object* v_x_4366_){
_start:
{
lean_object* v___x_4367_; 
v___x_4367_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(v_tries_4363_, v_snd_4364_, v_x_4365_, v_x_4366_);
return v___x_4367_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___boxed(lean_object* v_00_u03b1_4368_, lean_object* v_tries_4369_, lean_object* v_snd_4370_, lean_object* v_x_4371_, lean_object* v_x_4372_){
_start:
{
lean_object* v_res_4373_; 
v_res_4373_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0(v_00_u03b1_4368_, v_tries_4369_, v_snd_4370_, v_x_4371_, v_x_4372_);
lean_dec_ref(v_tries_4369_);
return v_res_4373_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1(lean_object* v_00_u03b1_4374_, lean_object* v_tries_4375_, lean_object* v_snd_4376_, lean_object* v_as_4377_, size_t v_i_4378_, size_t v_stop_4379_, lean_object* v_b_4380_){
_start:
{
lean_object* v___x_4381_; 
v___x_4381_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(v_tries_4375_, v_snd_4376_, v_as_4377_, v_i_4378_, v_stop_4379_, v_b_4380_);
return v___x_4381_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___boxed(lean_object* v_00_u03b1_4382_, lean_object* v_tries_4383_, lean_object* v_snd_4384_, lean_object* v_as_4385_, lean_object* v_i_4386_, lean_object* v_stop_4387_, lean_object* v_b_4388_){
_start:
{
size_t v_i_boxed_4389_; size_t v_stop_boxed_4390_; lean_object* v_res_4391_; 
v_i_boxed_4389_ = lean_unbox_usize(v_i_4386_);
lean_dec(v_i_4386_);
v_stop_boxed_4390_ = lean_unbox_usize(v_stop_4387_);
lean_dec(v_stop_4387_);
v_res_4391_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1(v_00_u03b1_4382_, v_tries_4383_, v_snd_4384_, v_as_4385_, v_i_boxed_4389_, v_stop_boxed_4390_, v_b_4388_);
lean_dec_ref(v_as_4385_);
lean_dec_ref(v_tries_4383_);
return v_res_4391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend___redArg(){
_start:
{
lean_object* v___x_4394_; 
v___x_4394_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend___redArg___closed__0));
return v___x_4394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend___redArg___boxed(lean_object* v___dummy_4395_){
_start:
{
lean_object* v_res_4396_; 
v_res_4396_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend___redArg();
return v_res_4396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend(lean_object* v_00_u03b1_4397_){
_start:
{
lean_object* v___x_4398_; 
v___x_4398_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend___redArg___closed__0));
return v___x_4398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(lean_object* v_expr_4399_, lean_object* v_value_4400_, lean_object* v_a_4401_, lean_object* v_a_4402_, lean_object* v_a_4403_, lean_object* v_a_4404_){
_start:
{
lean_object* v_lctx_4406_; lean_object* v_localInstances_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; 
v_lctx_4406_ = lean_ctor_get(v_a_4401_, 2);
v_localInstances_4407_ = lean_ctor_get(v_a_4401_, 3);
lean_inc_ref(v_localInstances_4407_);
lean_inc_ref(v_lctx_4406_);
v___x_4408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4408_, 0, v_lctx_4406_);
lean_ctor_set(v___x_4408_, 1, v_localInstances_4407_);
v___x_4409_ = l_Lean_Meta_LazyDiscrTree_rootKey(v_expr_4399_, v_a_4401_, v_a_4402_, v_a_4403_, v_a_4404_);
if (lean_obj_tag(v___x_4409_) == 0)
{
lean_object* v_a_4410_; lean_object* v___x_4412_; uint8_t v_isShared_4413_; uint8_t v_isSharedCheck_4428_; 
v_a_4410_ = lean_ctor_get(v___x_4409_, 0);
v_isSharedCheck_4428_ = !lean_is_exclusive(v___x_4409_);
if (v_isSharedCheck_4428_ == 0)
{
v___x_4412_ = v___x_4409_;
v_isShared_4413_ = v_isSharedCheck_4428_;
goto v_resetjp_4411_;
}
else
{
lean_inc(v_a_4410_);
lean_dec(v___x_4409_);
v___x_4412_ = lean_box(0);
v_isShared_4413_ = v_isSharedCheck_4428_;
goto v_resetjp_4411_;
}
v_resetjp_4411_:
{
lean_object* v_fst_4414_; lean_object* v_snd_4415_; lean_object* v___x_4417_; uint8_t v_isShared_4418_; uint8_t v_isSharedCheck_4427_; 
v_fst_4414_ = lean_ctor_get(v_a_4410_, 0);
v_snd_4415_ = lean_ctor_get(v_a_4410_, 1);
v_isSharedCheck_4427_ = !lean_is_exclusive(v_a_4410_);
if (v_isSharedCheck_4427_ == 0)
{
v___x_4417_ = v_a_4410_;
v_isShared_4418_ = v_isSharedCheck_4427_;
goto v_resetjp_4416_;
}
else
{
lean_inc(v_snd_4415_);
lean_inc(v_fst_4414_);
lean_dec(v_a_4410_);
v___x_4417_ = lean_box(0);
v_isShared_4418_ = v_isSharedCheck_4427_;
goto v_resetjp_4416_;
}
v_resetjp_4416_:
{
lean_object* v___x_4420_; 
if (v_isShared_4418_ == 0)
{
lean_ctor_set(v___x_4417_, 1, v_value_4400_);
lean_ctor_set(v___x_4417_, 0, v___x_4408_);
v___x_4420_ = v___x_4417_;
goto v_reusejp_4419_;
}
else
{
lean_object* v_reuseFailAlloc_4426_; 
v_reuseFailAlloc_4426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4426_, 0, v___x_4408_);
lean_ctor_set(v_reuseFailAlloc_4426_, 1, v_value_4400_);
v___x_4420_ = v_reuseFailAlloc_4426_;
goto v_reusejp_4419_;
}
v_reusejp_4419_:
{
lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4424_; 
v___x_4421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4421_, 0, v_snd_4415_);
lean_ctor_set(v___x_4421_, 1, v___x_4420_);
v___x_4422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4422_, 0, v_fst_4414_);
lean_ctor_set(v___x_4422_, 1, v___x_4421_);
if (v_isShared_4413_ == 0)
{
lean_ctor_set(v___x_4412_, 0, v___x_4422_);
v___x_4424_ = v___x_4412_;
goto v_reusejp_4423_;
}
else
{
lean_object* v_reuseFailAlloc_4425_; 
v_reuseFailAlloc_4425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4425_, 0, v___x_4422_);
v___x_4424_ = v_reuseFailAlloc_4425_;
goto v_reusejp_4423_;
}
v_reusejp_4423_:
{
return v___x_4424_;
}
}
}
}
}
else
{
lean_object* v_a_4429_; lean_object* v___x_4431_; uint8_t v_isShared_4432_; uint8_t v_isSharedCheck_4436_; 
lean_dec_ref_known(v___x_4408_, 2);
lean_dec(v_value_4400_);
v_a_4429_ = lean_ctor_get(v___x_4409_, 0);
v_isSharedCheck_4436_ = !lean_is_exclusive(v___x_4409_);
if (v_isSharedCheck_4436_ == 0)
{
v___x_4431_ = v___x_4409_;
v_isShared_4432_ = v_isSharedCheck_4436_;
goto v_resetjp_4430_;
}
else
{
lean_inc(v_a_4429_);
lean_dec(v___x_4409_);
v___x_4431_ = lean_box(0);
v_isShared_4432_ = v_isSharedCheck_4436_;
goto v_resetjp_4430_;
}
v_resetjp_4430_:
{
lean_object* v___x_4434_; 
if (v_isShared_4432_ == 0)
{
v___x_4434_ = v___x_4431_;
goto v_reusejp_4433_;
}
else
{
lean_object* v_reuseFailAlloc_4435_; 
v_reuseFailAlloc_4435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4435_, 0, v_a_4429_);
v___x_4434_ = v_reuseFailAlloc_4435_;
goto v_reusejp_4433_;
}
v_reusejp_4433_:
{
return v___x_4434_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg___boxed(lean_object* v_expr_4437_, lean_object* v_value_4438_, lean_object* v_a_4439_, lean_object* v_a_4440_, lean_object* v_a_4441_, lean_object* v_a_4442_, lean_object* v_a_4443_){
_start:
{
lean_object* v_res_4444_; 
v_res_4444_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(v_expr_4437_, v_value_4438_, v_a_4439_, v_a_4440_, v_a_4441_, v_a_4442_);
lean_dec(v_a_4442_);
lean_dec_ref(v_a_4441_);
lean_dec(v_a_4440_);
lean_dec_ref(v_a_4439_);
return v_res_4444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr(lean_object* v_00_u03b1_4445_, lean_object* v_expr_4446_, lean_object* v_value_4447_, lean_object* v_a_4448_, lean_object* v_a_4449_, lean_object* v_a_4450_, lean_object* v_a_4451_){
_start:
{
lean_object* v___x_4453_; 
v___x_4453_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(v_expr_4446_, v_value_4447_, v_a_4448_, v_a_4449_, v_a_4450_, v_a_4451_);
return v___x_4453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___boxed(lean_object* v_00_u03b1_4454_, lean_object* v_expr_4455_, lean_object* v_value_4456_, lean_object* v_a_4457_, lean_object* v_a_4458_, lean_object* v_a_4459_, lean_object* v_a_4460_, lean_object* v_a_4461_){
_start:
{
lean_object* v_res_4462_; 
v_res_4462_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr(v_00_u03b1_4454_, v_expr_4455_, v_value_4456_, v_a_4457_, v_a_4458_, v_a_4459_, v_a_4460_);
lean_dec(v_a_4460_);
lean_dec_ref(v_a_4459_);
lean_dec(v_a_4458_);
lean_dec_ref(v_a_4457_);
return v_res_4462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(lean_object* v_e_4463_, lean_object* v_idx_4464_, lean_object* v_value_4465_, lean_object* v_a_4466_, lean_object* v_a_4467_, lean_object* v_a_4468_, lean_object* v_a_4469_){
_start:
{
lean_object* v_entry_4471_; lean_object* v___x_4473_; uint8_t v_isShared_4474_; uint8_t v_isSharedCheck_4517_; 
v_entry_4471_ = lean_ctor_get(v_e_4463_, 1);
v_isSharedCheck_4517_ = !lean_is_exclusive(v_e_4463_);
if (v_isSharedCheck_4517_ == 0)
{
lean_object* v_unused_4518_; 
v_unused_4518_ = lean_ctor_get(v_e_4463_, 0);
lean_dec(v_unused_4518_);
v___x_4473_ = v_e_4463_;
v_isShared_4474_ = v_isSharedCheck_4517_;
goto v_resetjp_4472_;
}
else
{
lean_inc(v_entry_4471_);
lean_dec(v_e_4463_);
v___x_4473_ = lean_box(0);
v_isShared_4474_ = v_isSharedCheck_4517_;
goto v_resetjp_4472_;
}
v_resetjp_4472_:
{
lean_object* v_snd_4475_; lean_object* v_fst_4476_; lean_object* v_fst_4477_; lean_object* v___x_4479_; uint8_t v_isShared_4480_; uint8_t v_isSharedCheck_4515_; 
v_snd_4475_ = lean_ctor_get(v_entry_4471_, 1);
lean_inc(v_snd_4475_);
v_fst_4476_ = lean_ctor_get(v_entry_4471_, 0);
lean_inc(v_fst_4476_);
lean_dec_ref(v_entry_4471_);
v_fst_4477_ = lean_ctor_get(v_snd_4475_, 0);
v_isSharedCheck_4515_ = !lean_is_exclusive(v_snd_4475_);
if (v_isSharedCheck_4515_ == 0)
{
lean_object* v_unused_4516_; 
v_unused_4516_ = lean_ctor_get(v_snd_4475_, 1);
lean_dec(v_unused_4516_);
v___x_4479_ = v_snd_4475_;
v_isShared_4480_ = v_isSharedCheck_4515_;
goto v_resetjp_4478_;
}
else
{
lean_inc(v_fst_4477_);
lean_dec(v_snd_4475_);
v___x_4479_ = lean_box(0);
v_isShared_4480_ = v_isSharedCheck_4515_;
goto v_resetjp_4478_;
}
v_resetjp_4478_:
{
lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; 
v___x_4481_ = l_Lean_instInhabitedExpr;
v___x_4482_ = lean_array_get(v___x_4481_, v_fst_4476_, v_idx_4464_);
lean_dec(v_fst_4476_);
v___x_4483_ = l_Lean_Meta_LazyDiscrTree_rootKey(v___x_4482_, v_a_4466_, v_a_4467_, v_a_4468_, v_a_4469_);
if (lean_obj_tag(v___x_4483_) == 0)
{
lean_object* v_a_4484_; lean_object* v___x_4486_; uint8_t v_isShared_4487_; uint8_t v_isSharedCheck_4506_; 
v_a_4484_ = lean_ctor_get(v___x_4483_, 0);
v_isSharedCheck_4506_ = !lean_is_exclusive(v___x_4483_);
if (v_isSharedCheck_4506_ == 0)
{
v___x_4486_ = v___x_4483_;
v_isShared_4487_ = v_isSharedCheck_4506_;
goto v_resetjp_4485_;
}
else
{
lean_inc(v_a_4484_);
lean_dec(v___x_4483_);
v___x_4486_ = lean_box(0);
v_isShared_4487_ = v_isSharedCheck_4506_;
goto v_resetjp_4485_;
}
v_resetjp_4485_:
{
lean_object* v_fst_4488_; lean_object* v_snd_4489_; lean_object* v___x_4491_; uint8_t v_isShared_4492_; uint8_t v_isSharedCheck_4505_; 
v_fst_4488_ = lean_ctor_get(v_a_4484_, 0);
v_snd_4489_ = lean_ctor_get(v_a_4484_, 1);
v_isSharedCheck_4505_ = !lean_is_exclusive(v_a_4484_);
if (v_isSharedCheck_4505_ == 0)
{
v___x_4491_ = v_a_4484_;
v_isShared_4492_ = v_isSharedCheck_4505_;
goto v_resetjp_4490_;
}
else
{
lean_inc(v_snd_4489_);
lean_inc(v_fst_4488_);
lean_dec(v_a_4484_);
v___x_4491_ = lean_box(0);
v_isShared_4492_ = v_isSharedCheck_4505_;
goto v_resetjp_4490_;
}
v_resetjp_4490_:
{
lean_object* v___x_4494_; 
if (v_isShared_4492_ == 0)
{
lean_ctor_set(v___x_4491_, 1, v_value_4465_);
lean_ctor_set(v___x_4491_, 0, v_fst_4477_);
v___x_4494_ = v___x_4491_;
goto v_reusejp_4493_;
}
else
{
lean_object* v_reuseFailAlloc_4504_; 
v_reuseFailAlloc_4504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4504_, 0, v_fst_4477_);
lean_ctor_set(v_reuseFailAlloc_4504_, 1, v_value_4465_);
v___x_4494_ = v_reuseFailAlloc_4504_;
goto v_reusejp_4493_;
}
v_reusejp_4493_:
{
lean_object* v___x_4496_; 
if (v_isShared_4480_ == 0)
{
lean_ctor_set(v___x_4479_, 1, v___x_4494_);
lean_ctor_set(v___x_4479_, 0, v_snd_4489_);
v___x_4496_ = v___x_4479_;
goto v_reusejp_4495_;
}
else
{
lean_object* v_reuseFailAlloc_4503_; 
v_reuseFailAlloc_4503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4503_, 0, v_snd_4489_);
lean_ctor_set(v_reuseFailAlloc_4503_, 1, v___x_4494_);
v___x_4496_ = v_reuseFailAlloc_4503_;
goto v_reusejp_4495_;
}
v_reusejp_4495_:
{
lean_object* v___x_4498_; 
if (v_isShared_4474_ == 0)
{
lean_ctor_set(v___x_4473_, 1, v___x_4496_);
lean_ctor_set(v___x_4473_, 0, v_fst_4488_);
v___x_4498_ = v___x_4473_;
goto v_reusejp_4497_;
}
else
{
lean_object* v_reuseFailAlloc_4502_; 
v_reuseFailAlloc_4502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4502_, 0, v_fst_4488_);
lean_ctor_set(v_reuseFailAlloc_4502_, 1, v___x_4496_);
v___x_4498_ = v_reuseFailAlloc_4502_;
goto v_reusejp_4497_;
}
v_reusejp_4497_:
{
lean_object* v___x_4500_; 
if (v_isShared_4487_ == 0)
{
lean_ctor_set(v___x_4486_, 0, v___x_4498_);
v___x_4500_ = v___x_4486_;
goto v_reusejp_4499_;
}
else
{
lean_object* v_reuseFailAlloc_4501_; 
v_reuseFailAlloc_4501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4501_, 0, v___x_4498_);
v___x_4500_ = v_reuseFailAlloc_4501_;
goto v_reusejp_4499_;
}
v_reusejp_4499_:
{
return v___x_4500_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4507_; lean_object* v___x_4509_; uint8_t v_isShared_4510_; uint8_t v_isSharedCheck_4514_; 
lean_del_object(v___x_4479_);
lean_dec(v_fst_4477_);
lean_del_object(v___x_4473_);
lean_dec(v_value_4465_);
v_a_4507_ = lean_ctor_get(v___x_4483_, 0);
v_isSharedCheck_4514_ = !lean_is_exclusive(v___x_4483_);
if (v_isSharedCheck_4514_ == 0)
{
v___x_4509_ = v___x_4483_;
v_isShared_4510_ = v_isSharedCheck_4514_;
goto v_resetjp_4508_;
}
else
{
lean_inc(v_a_4507_);
lean_dec(v___x_4483_);
v___x_4509_ = lean_box(0);
v_isShared_4510_ = v_isSharedCheck_4514_;
goto v_resetjp_4508_;
}
v_resetjp_4508_:
{
lean_object* v___x_4512_; 
if (v_isShared_4510_ == 0)
{
v___x_4512_ = v___x_4509_;
goto v_reusejp_4511_;
}
else
{
lean_object* v_reuseFailAlloc_4513_; 
v_reuseFailAlloc_4513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4513_, 0, v_a_4507_);
v___x_4512_ = v_reuseFailAlloc_4513_;
goto v_reusejp_4511_;
}
v_reusejp_4511_:
{
return v___x_4512_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg___boxed(lean_object* v_e_4519_, lean_object* v_idx_4520_, lean_object* v_value_4521_, lean_object* v_a_4522_, lean_object* v_a_4523_, lean_object* v_a_4524_, lean_object* v_a_4525_, lean_object* v_a_4526_){
_start:
{
lean_object* v_res_4527_; 
v_res_4527_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(v_e_4519_, v_idx_4520_, v_value_4521_, v_a_4522_, v_a_4523_, v_a_4524_, v_a_4525_);
lean_dec(v_a_4525_);
lean_dec_ref(v_a_4524_);
lean_dec(v_a_4523_);
lean_dec_ref(v_a_4522_);
lean_dec(v_idx_4520_);
return v_res_4527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry(lean_object* v_00_u03b1_4528_, lean_object* v_e_4529_, lean_object* v_idx_4530_, lean_object* v_value_4531_, lean_object* v_a_4532_, lean_object* v_a_4533_, lean_object* v_a_4534_, lean_object* v_a_4535_){
_start:
{
lean_object* v___x_4537_; 
v___x_4537_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(v_e_4529_, v_idx_4530_, v_value_4531_, v_a_4532_, v_a_4533_, v_a_4534_, v_a_4535_);
return v___x_4537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___boxed(lean_object* v_00_u03b1_4538_, lean_object* v_e_4539_, lean_object* v_idx_4540_, lean_object* v_value_4541_, lean_object* v_a_4542_, lean_object* v_a_4543_, lean_object* v_a_4544_, lean_object* v_a_4545_, lean_object* v_a_4546_){
_start:
{
lean_object* v_res_4547_; 
v_res_4547_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry(v_00_u03b1_4538_, v_e_4539_, v_idx_4540_, v_value_4541_, v_a_4542_, v_a_4543_, v_a_4544_, v_a_4545_);
lean_dec(v_a_4545_);
lean_dec_ref(v_a_4544_);
lean_dec(v_a_4543_);
lean_dec_ref(v_a_4542_);
lean_dec(v_idx_4540_);
return v_res_4547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_ImportData_new(){
_start:
{
lean_object* v___x_4551_; lean_object* v___x_4552_; 
v___x_4551_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_ImportData_new___closed__0));
v___x_4552_ = lean_st_mk_ref(v___x_4551_);
return v___x_4552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_ImportData_new___boxed(lean_object* v_a_4553_){
_start:
{
lean_object* v_res_4554_; 
v_res_4554_ = l_Lean_Meta_LazyDiscrTree_ImportData_new();
return v_res_4554_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0(void){
_start:
{
lean_object* v___x_4555_; 
v___x_4555_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_4555_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1(void){
_start:
{
lean_object* v___x_4556_; lean_object* v___x_4557_; 
v___x_4556_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0);
v___x_4557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4557_, 0, v___x_4556_);
return v___x_4557_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2(void){
_start:
{
lean_object* v___x_4558_; lean_object* v___x_4559_; 
v___x_4558_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1);
v___x_4559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4559_, 0, v___x_4558_);
lean_ctor_set(v___x_4559_, 1, v___x_4558_);
return v___x_4559_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3(void){
_start:
{
lean_object* v___x_4560_; lean_object* v___x_4561_; 
v___x_4560_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1);
v___x_4561_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4561_, 0, v___x_4560_);
lean_ctor_set(v___x_4561_, 1, v___x_4560_);
lean_ctor_set(v___x_4561_, 2, v___x_4560_);
lean_ctor_set(v___x_4561_, 3, v___x_4560_);
lean_ctor_set(v___x_4561_, 4, v___x_4560_);
lean_ctor_set(v___x_4561_, 5, v___x_4560_);
return v___x_4561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Cache_empty(lean_object* v_ngen_4562_){
_start:
{
lean_object* v___x_4563_; lean_object* v___x_4564_; lean_object* v___x_4565_; 
v___x_4563_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2);
v___x_4564_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3);
v___x_4565_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4565_, 0, v_ngen_4562_);
lean_ctor_set(v___x_4565_, 1, v___x_4563_);
lean_ctor_set(v___x_4565_, 2, v___x_4564_);
return v___x_4565_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName(lean_object* v_env_4566_, lean_object* v_declName_4567_){
_start:
{
uint8_t v___x_4568_; 
v___x_4568_ = l_Lean_isPrivateName(v_declName_4567_);
if (v___x_4568_ == 0)
{
return v___x_4568_;
}
else
{
lean_object* v___x_4569_; 
v___x_4569_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4566_, v_declName_4567_);
if (lean_obj_tag(v___x_4569_) == 0)
{
return v___x_4568_;
}
else
{
lean_object* v_val_4570_; lean_object* v___x_4571_; uint8_t v_isModule_4572_; lean_object* v_modules_4573_; uint8_t v___x_4574_; 
v_val_4570_ = lean_ctor_get(v___x_4569_, 0);
lean_inc(v_val_4570_);
lean_dec_ref_known(v___x_4569_, 1);
v___x_4571_ = l_Lean_Environment_header(v_env_4566_);
v_isModule_4572_ = lean_ctor_get_uint8(v___x_4571_, sizeof(void*)*7 + 4);
v_modules_4573_ = lean_ctor_get(v___x_4571_, 3);
lean_inc_ref(v_modules_4573_);
lean_dec_ref(v___x_4571_);
v___x_4574_ = 0;
if (v_isModule_4572_ == 0)
{
lean_dec_ref(v_modules_4573_);
lean_dec(v_val_4570_);
return v___x_4574_;
}
else
{
lean_object* v___x_4575_; uint8_t v___x_4576_; 
v___x_4575_ = lean_array_get_size(v_modules_4573_);
v___x_4576_ = lean_nat_dec_lt(v_val_4570_, v___x_4575_);
if (v___x_4576_ == 0)
{
lean_dec_ref(v_modules_4573_);
lean_dec(v_val_4570_);
return v___x_4574_;
}
else
{
lean_object* v___x_4577_; lean_object* v_toImport_4578_; uint8_t v_importAll_4579_; 
v___x_4577_ = lean_array_fget(v_modules_4573_, v_val_4570_);
lean_dec(v_val_4570_);
lean_dec_ref(v_modules_4573_);
v_toImport_4578_ = lean_ctor_get(v___x_4577_, 0);
lean_inc_ref(v_toImport_4578_);
lean_dec(v___x_4577_);
v_importAll_4579_ = lean_ctor_get_uint8(v_toImport_4578_, sizeof(void*)*1);
lean_dec_ref(v_toImport_4578_);
return v_importAll_4579_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName___boxed(lean_object* v_env_4580_, lean_object* v_declName_4581_){
_start:
{
uint8_t v_res_4582_; lean_object* v_r_4583_; 
v_res_4582_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName(v_env_4580_, v_declName_4581_);
lean_dec(v_declName_4581_);
lean_dec_ref(v_env_4580_);
v_r_4583_ = lean_box(v_res_4582_);
return v_r_4583_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_LazyDiscrTree_blacklistInsertion(lean_object* v_env_4589_, lean_object* v_declName_4590_){
_start:
{
uint8_t v___x_4591_; 
lean_inc(v_declName_4590_);
lean_inc_ref(v_env_4589_);
v___x_4591_ = l_Lean_Meta_allowCompletion(v_env_4589_, v_declName_4590_);
if (v___x_4591_ == 0)
{
uint8_t v___x_4592_; 
lean_dec(v_declName_4590_);
lean_dec_ref(v_env_4589_);
v___x_4592_ = 1;
return v___x_4592_;
}
else
{
lean_object* v___x_4593_; uint8_t v___x_4594_; uint8_t v___y_4604_; 
v___x_4593_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__1));
v___x_4594_ = lean_name_eq(v_declName_4590_, v___x_4593_);
if (v___x_4594_ == 0)
{
uint8_t v___x_4605_; 
lean_inc(v_declName_4590_);
v___x_4605_ = l_Lean_Name_isInternalDetail(v_declName_4590_);
if (v___x_4605_ == 0)
{
lean_dec_ref(v_env_4589_);
v___y_4604_ = v___x_4605_;
goto v___jp_4603_;
}
else
{
uint8_t v___x_4606_; 
v___x_4606_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName(v_env_4589_, v_declName_4590_);
lean_dec_ref(v_env_4589_);
if (v___x_4606_ == 0)
{
v___y_4604_ = v___x_4605_;
goto v___jp_4603_;
}
else
{
goto v___jp_4599_;
}
}
}
else
{
lean_dec(v_declName_4590_);
lean_dec_ref(v_env_4589_);
return v___x_4594_;
}
v___jp_4595_:
{
if (lean_obj_tag(v_declName_4590_) == 1)
{
lean_object* v_str_4596_; lean_object* v___x_4597_; uint8_t v___x_4598_; 
v_str_4596_ = lean_ctor_get(v_declName_4590_, 1);
lean_inc_ref(v_str_4596_);
lean_dec_ref_known(v_declName_4590_, 2);
v___x_4597_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__2));
v___x_4598_ = lean_string_dec_eq(v_str_4596_, v___x_4597_);
lean_dec_ref(v_str_4596_);
return v___x_4598_;
}
else
{
lean_dec(v_declName_4590_);
return v___x_4594_;
}
}
v___jp_4599_:
{
if (lean_obj_tag(v_declName_4590_) == 1)
{
lean_object* v_str_4600_; lean_object* v___x_4601_; uint8_t v___x_4602_; 
v_str_4600_ = lean_ctor_get(v_declName_4590_, 1);
v___x_4601_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__3));
v___x_4602_ = lean_string_dec_eq(v_str_4600_, v___x_4601_);
if (v___x_4602_ == 0)
{
goto v___jp_4595_;
}
else
{
lean_dec_ref_known(v_declName_4590_, 2);
return v___x_4602_;
}
}
else
{
goto v___jp_4595_;
}
}
v___jp_4603_:
{
if (v___y_4604_ == 0)
{
goto v___jp_4599_;
}
else
{
lean_dec(v_declName_4590_);
return v___y_4604_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_blacklistInsertion___boxed(lean_object* v_env_4607_, lean_object* v_declName_4608_){
_start:
{
uint8_t v_res_4609_; lean_object* v_r_4610_; 
v_res_4609_ = l_Lean_Meta_LazyDiscrTree_blacklistInsertion(v_env_4607_, v_declName_4608_);
v_r_4610_ = lean_box(v_res_4609_);
return v_r_4610_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(lean_object* v_opts_4611_, lean_object* v_opt_4612_){
_start:
{
lean_object* v_name_4613_; lean_object* v_defValue_4614_; lean_object* v_map_4615_; lean_object* v___x_4616_; 
v_name_4613_ = lean_ctor_get(v_opt_4612_, 0);
v_defValue_4614_ = lean_ctor_get(v_opt_4612_, 1);
v_map_4615_ = lean_ctor_get(v_opts_4611_, 0);
v___x_4616_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4615_, v_name_4613_);
if (lean_obj_tag(v___x_4616_) == 0)
{
uint8_t v___x_4617_; 
v___x_4617_ = lean_unbox(v_defValue_4614_);
return v___x_4617_;
}
else
{
lean_object* v_val_4618_; 
v_val_4618_ = lean_ctor_get(v___x_4616_, 0);
lean_inc(v_val_4618_);
lean_dec_ref_known(v___x_4616_, 1);
if (lean_obj_tag(v_val_4618_) == 1)
{
uint8_t v_v_4619_; 
v_v_4619_ = lean_ctor_get_uint8(v_val_4618_, 0);
lean_dec_ref_known(v_val_4618_, 0);
return v_v_4619_;
}
else
{
uint8_t v___x_4620_; 
lean_dec(v_val_4618_);
v___x_4620_ = lean_unbox(v_defValue_4614_);
return v___x_4620_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0___boxed(lean_object* v_opts_4621_, lean_object* v_opt_4622_){
_start:
{
uint8_t v_res_4623_; lean_object* v_r_4624_; 
v_res_4623_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(v_opts_4621_, v_opt_4622_);
lean_dec_ref(v_opt_4622_);
lean_dec_ref(v_opts_4621_);
v_r_4624_ = lean_box(v_res_4623_);
return v_r_4624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1(lean_object* v_opts_4625_, lean_object* v_opt_4626_){
_start:
{
lean_object* v_name_4627_; lean_object* v_defValue_4628_; lean_object* v_map_4629_; lean_object* v___x_4630_; 
v_name_4627_ = lean_ctor_get(v_opt_4626_, 0);
v_defValue_4628_ = lean_ctor_get(v_opt_4626_, 1);
v_map_4629_ = lean_ctor_get(v_opts_4625_, 0);
v___x_4630_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4629_, v_name_4627_);
if (lean_obj_tag(v___x_4630_) == 0)
{
lean_inc(v_defValue_4628_);
return v_defValue_4628_;
}
else
{
lean_object* v_val_4631_; 
v_val_4631_ = lean_ctor_get(v___x_4630_, 0);
lean_inc(v_val_4631_);
lean_dec_ref_known(v___x_4630_, 1);
if (lean_obj_tag(v_val_4631_) == 3)
{
lean_object* v_v_4632_; 
v_v_4632_ = lean_ctor_get(v_val_4631_, 0);
lean_inc(v_v_4632_);
lean_dec_ref_known(v_val_4631_, 1);
return v_v_4632_;
}
else
{
lean_dec(v_val_4631_);
lean_inc(v_defValue_4628_);
return v_defValue_4628_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1___boxed(lean_object* v_opts_4633_, lean_object* v_opt_4634_){
_start:
{
lean_object* v_res_4635_; 
v_res_4635_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1(v_opts_4633_, v_opt_4634_);
lean_dec_ref(v_opt_4634_);
lean_dec_ref(v_opts_4633_);
return v_res_4635_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg(lean_object* v_as_4636_, size_t v_i_4637_, size_t v_stop_4638_, lean_object* v_b_4639_){
_start:
{
uint8_t v___x_4640_; 
v___x_4640_ = lean_usize_dec_eq(v_i_4637_, v_stop_4638_);
if (v___x_4640_ == 0)
{
lean_object* v___x_4641_; lean_object* v_key_4642_; lean_object* v_entry_4643_; lean_object* v___x_4644_; size_t v___x_4645_; size_t v___x_4646_; 
v___x_4641_ = lean_array_uget_borrowed(v_as_4636_, v_i_4637_);
v_key_4642_ = lean_ctor_get(v___x_4641_, 0);
v_entry_4643_ = lean_ctor_get(v___x_4641_, 1);
lean_inc_ref(v_entry_4643_);
lean_inc(v_key_4642_);
v___x_4644_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg(v_b_4639_, v_key_4642_, v_entry_4643_);
v___x_4645_ = ((size_t)1ULL);
v___x_4646_ = lean_usize_add(v_i_4637_, v___x_4645_);
v_i_4637_ = v___x_4646_;
v_b_4639_ = v___x_4644_;
goto _start;
}
else
{
return v_b_4639_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg___boxed(lean_object* v_as_4648_, lean_object* v_i_4649_, lean_object* v_stop_4650_, lean_object* v_b_4651_){
_start:
{
size_t v_i_boxed_4652_; size_t v_stop_boxed_4653_; lean_object* v_res_4654_; 
v_i_boxed_4652_ = lean_unbox_usize(v_i_4649_);
lean_dec(v_i_4649_);
v_stop_boxed_4653_ = lean_unbox_usize(v_stop_4650_);
lean_dec(v_stop_4650_);
v_res_4654_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg(v_as_4648_, v_i_boxed_4652_, v_stop_boxed_4653_, v_b_4651_);
lean_dec_ref(v_as_4648_);
return v_res_4654_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0(void){
_start:
{
lean_object* v___x_4655_; lean_object* v___x_4656_; 
v___x_4655_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0);
v___x_4656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4656_, 0, v___x_4655_);
return v___x_4656_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1(void){
_start:
{
lean_object* v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; 
v___x_4657_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0);
v___x_4658_ = lean_unsigned_to_nat(0u);
v___x_4659_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_4659_, 0, v___x_4658_);
lean_ctor_set(v___x_4659_, 1, v___x_4658_);
lean_ctor_set(v___x_4659_, 2, v___x_4658_);
lean_ctor_set(v___x_4659_, 3, v___x_4658_);
lean_ctor_set(v___x_4659_, 4, v___x_4657_);
lean_ctor_set(v___x_4659_, 5, v___x_4657_);
lean_ctor_set(v___x_4659_, 6, v___x_4657_);
lean_ctor_set(v___x_4659_, 7, v___x_4657_);
lean_ctor_set(v___x_4659_, 8, v___x_4657_);
lean_ctor_set(v___x_4659_, 9, v___x_4657_);
lean_ctor_set(v___x_4659_, 10, v___x_4657_);
return v___x_4659_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2(void){
_start:
{
lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; 
v___x_4660_ = lean_unsigned_to_nat(32u);
v___x_4661_ = lean_mk_empty_array_with_capacity(v___x_4660_);
v___x_4662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4662_, 0, v___x_4661_);
return v___x_4662_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3(void){
_start:
{
size_t v___x_4663_; lean_object* v___x_4664_; lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; 
v___x_4663_ = ((size_t)5ULL);
v___x_4664_ = lean_unsigned_to_nat(0u);
v___x_4665_ = lean_unsigned_to_nat(32u);
v___x_4666_ = lean_mk_empty_array_with_capacity(v___x_4665_);
v___x_4667_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2);
v___x_4668_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4668_, 0, v___x_4667_);
lean_ctor_set(v___x_4668_, 1, v___x_4666_);
lean_ctor_set(v___x_4668_, 2, v___x_4664_);
lean_ctor_set(v___x_4668_, 3, v___x_4664_);
lean_ctor_set_usize(v___x_4668_, 4, v___x_4663_);
return v___x_4668_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4(void){
_start:
{
lean_object* v___x_4669_; lean_object* v___x_4670_; 
v___x_4669_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0);
v___x_4670_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4670_, 0, v___x_4669_);
lean_ctor_set(v___x_4670_, 1, v___x_4669_);
lean_ctor_set(v___x_4670_, 2, v___x_4669_);
lean_ctor_set(v___x_4670_, 3, v___x_4669_);
lean_ctor_set(v___x_4670_, 4, v___x_4669_);
return v___x_4670_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5(void){
_start:
{
lean_object* v___x_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; 
v___x_4671_ = lean_box(1);
v___x_4672_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3);
v___x_4673_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0);
v___x_4674_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4674_, 0, v___x_4673_);
lean_ctor_set(v___x_4674_, 1, v___x_4672_);
lean_ctor_set(v___x_4674_, 2, v___x_4671_);
return v___x_4674_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__7(void){
_start:
{
lean_object* v___x_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; 
v___x_4677_ = lean_unsigned_to_nat(1u);
v___x_4678_ = l_Lean_firstFrontendMacroScope;
v___x_4679_ = lean_nat_add(v___x_4678_, v___x_4677_);
return v___x_4679_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__9(void){
_start:
{
lean_object* v___x_4684_; uint64_t v___x_4685_; lean_object* v___x_4686_; 
v___x_4684_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3);
v___x_4685_ = 0ULL;
v___x_4686_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4686_, 0, v___x_4684_);
lean_ctor_set_uint64(v___x_4686_, sizeof(void*)*1, v___x_4685_);
return v___x_4686_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10(void){
_start:
{
lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; 
v___x_4687_ = l_Lean_NameSet_empty;
v___x_4688_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3);
v___x_4689_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4689_, 0, v___x_4688_);
lean_ctor_set(v___x_4689_, 1, v___x_4688_);
lean_ctor_set(v___x_4689_, 2, v___x_4687_);
return v___x_4689_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11(void){
_start:
{
lean_object* v___x_4690_; lean_object* v___x_4691_; uint8_t v___x_4692_; lean_object* v___x_4693_; 
v___x_4690_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3);
v___x_4691_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0);
v___x_4692_ = 1;
v___x_4693_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4693_, 0, v___x_4691_);
lean_ctor_set(v___x_4693_, 1, v___x_4691_);
lean_ctor_set(v___x_4693_, 2, v___x_4690_);
lean_ctor_set_uint8(v___x_4693_, sizeof(void*)*3, v___x_4692_);
return v___x_4693_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12(void){
_start:
{
lean_object* v___x_4694_; lean_object* v___x_4695_; 
v___x_4694_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0);
v___x_4695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4695_, 0, v___x_4694_);
lean_ctor_set(v___x_4695_, 1, v___x_4694_);
return v___x_4695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(lean_object* v_cctx_4696_, lean_object* v_env_4697_, lean_object* v_modName_4698_, lean_object* v_d_4699_, lean_object* v_cacheRef_4700_, lean_object* v_tree_4701_, lean_object* v_act_4702_, lean_object* v_c_4703_){
_start:
{
uint8_t v___x_4705_; 
lean_inc_ref(v_c_4703_);
v___x_4705_ = l_Lean_AsyncConstantInfo_isUnsafe(v_c_4703_);
if (v___x_4705_ == 0)
{
lean_object* v_name_4706_; uint8_t v___x_4707_; 
v_name_4706_ = lean_ctor_get(v_c_4703_, 0);
lean_inc_n(v_name_4706_, 2);
lean_inc_ref(v_env_4697_);
v___x_4707_ = l_Lean_Meta_LazyDiscrTree_blacklistInsertion(v_env_4697_, v_name_4706_);
if (v___x_4707_ == 0)
{
lean_object* v___x_4708_; uint8_t v___x_4709_; lean_object* v___x_4710_; lean_object* v_ngen_4711_; lean_object* v_core_4712_; lean_object* v_meta_4713_; lean_object* v___x_4715_; uint8_t v_isShared_4716_; uint8_t v_isSharedCheck_4829_; 
v___x_4708_ = lean_box(1);
v___x_4709_ = 1;
v___x_4710_ = lean_st_ref_get(v_cacheRef_4700_);
v_ngen_4711_ = lean_ctor_get(v___x_4710_, 0);
v_core_4712_ = lean_ctor_get(v___x_4710_, 1);
v_meta_4713_ = lean_ctor_get(v___x_4710_, 2);
v_isSharedCheck_4829_ = !lean_is_exclusive(v___x_4710_);
if (v_isSharedCheck_4829_ == 0)
{
v___x_4715_ = v___x_4710_;
v_isShared_4716_ = v_isSharedCheck_4829_;
goto v_resetjp_4714_;
}
else
{
lean_inc(v_meta_4713_);
lean_inc(v_core_4712_);
lean_inc(v_ngen_4711_);
lean_dec(v___x_4710_);
v___x_4715_ = lean_box(0);
v_isShared_4716_ = v_isSharedCheck_4829_;
goto v_resetjp_4714_;
}
v_resetjp_4714_:
{
lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; uint8_t v___x_4724_; uint8_t v___x_4725_; uint8_t v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; lean_object* v___x_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; lean_object* v_toCold_4742_; lean_object* v_currRecDepth_4743_; lean_object* v_ref_4744_; uint8_t v_suppressElabErrors_4745_; lean_object* v___x_4747_; uint8_t v_isShared_4748_; uint8_t v_isSharedCheck_4828_; 
v___x_4717_ = lean_unsigned_to_nat(0u);
v___x_4718_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4719_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3);
v___x_4720_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4721_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4721_, 0, v___x_4718_);
lean_ctor_set(v___x_4721_, 1, v_meta_4713_);
lean_ctor_set(v___x_4721_, 2, v___x_4708_);
lean_ctor_set(v___x_4721_, 3, v___x_4719_);
lean_ctor_set(v___x_4721_, 4, v___x_4720_);
lean_inc_ref(v_ngen_4711_);
v___x_4722_ = l_Lean_Meta_LazyDiscrTree_Cache_empty(v_ngen_4711_);
v___x_4723_ = lean_st_ref_swap(v_cacheRef_4700_, v___x_4722_);
lean_dec(v___x_4723_);
v___x_4724_ = 2;
v___x_4725_ = 0;
v___x_4726_ = 2;
v___x_4727_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_4727_, 0, v___x_4707_);
lean_ctor_set_uint8(v___x_4727_, 1, v___x_4707_);
lean_ctor_set_uint8(v___x_4727_, 2, v___x_4707_);
lean_ctor_set_uint8(v___x_4727_, 3, v___x_4707_);
lean_ctor_set_uint8(v___x_4727_, 4, v___x_4707_);
lean_ctor_set_uint8(v___x_4727_, 5, v___x_4709_);
lean_ctor_set_uint8(v___x_4727_, 6, v___x_4709_);
lean_ctor_set_uint8(v___x_4727_, 7, v___x_4707_);
lean_ctor_set_uint8(v___x_4727_, 8, v___x_4709_);
lean_ctor_set_uint8(v___x_4727_, 9, v___x_4724_);
lean_ctor_set_uint8(v___x_4727_, 10, v___x_4725_);
lean_ctor_set_uint8(v___x_4727_, 11, v___x_4709_);
lean_ctor_set_uint8(v___x_4727_, 12, v___x_4709_);
lean_ctor_set_uint8(v___x_4727_, 13, v___x_4709_);
lean_ctor_set_uint8(v___x_4727_, 14, v___x_4726_);
lean_ctor_set_uint8(v___x_4727_, 15, v___x_4709_);
lean_ctor_set_uint8(v___x_4727_, 16, v___x_4709_);
lean_ctor_set_uint8(v___x_4727_, 17, v___x_4709_);
lean_ctor_set_uint8(v___x_4727_, 18, v___x_4709_);
lean_ctor_set_uint8(v___x_4727_, 19, v___x_4707_);
v___x_4728_ = l_Lean_Meta_Config_toConfigWithKey(v___x_4727_);
v___x_4729_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5);
v___x_4730_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6));
v___x_4731_ = lean_box(0);
v___x_4732_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4732_, 0, v___x_4728_);
lean_ctor_set(v___x_4732_, 1, v___x_4708_);
lean_ctor_set(v___x_4732_, 2, v___x_4729_);
lean_ctor_set(v___x_4732_, 3, v___x_4730_);
lean_ctor_set(v___x_4732_, 4, v___x_4731_);
lean_ctor_set(v___x_4732_, 5, v___x_4717_);
lean_ctor_set(v___x_4732_, 6, v___x_4731_);
lean_ctor_set_uint8(v___x_4732_, sizeof(void*)*7, v___x_4707_);
lean_ctor_set_uint8(v___x_4732_, sizeof(void*)*7 + 1, v___x_4707_);
lean_ctor_set_uint8(v___x_4732_, sizeof(void*)*7 + 2, v___x_4707_);
lean_ctor_set_uint8(v___x_4732_, sizeof(void*)*7 + 3, v___x_4709_);
v___x_4733_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__7, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__7_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__7);
v___x_4734_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__8));
v___x_4735_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__9, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__9_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__9);
v___x_4736_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10);
v___x_4737_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11);
v___x_4738_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_4738_, 0, v_env_4697_);
lean_ctor_set(v___x_4738_, 1, v___x_4733_);
lean_ctor_set(v___x_4738_, 2, v_ngen_4711_);
lean_ctor_set(v___x_4738_, 3, v___x_4734_);
lean_ctor_set(v___x_4738_, 4, v___x_4735_);
lean_ctor_set(v___x_4738_, 5, v_core_4712_);
lean_ctor_set(v___x_4738_, 6, v___x_4736_);
lean_ctor_set(v___x_4738_, 7, v___x_4737_);
lean_ctor_set(v___x_4738_, 8, v___x_4730_);
v___x_4739_ = lean_st_mk_ref(v___x_4738_);
v___x_4740_ = l_Lean_inheritedTraceOptions;
v___x_4741_ = lean_st_ref_get(v___x_4740_);
v_toCold_4742_ = lean_ctor_get(v_cctx_4696_, 0);
v_currRecDepth_4743_ = lean_ctor_get(v_cctx_4696_, 1);
v_ref_4744_ = lean_ctor_get(v_cctx_4696_, 2);
v_suppressElabErrors_4745_ = lean_ctor_get_uint8(v_cctx_4696_, sizeof(void*)*3 + 1);
v_isSharedCheck_4828_ = !lean_is_exclusive(v_cctx_4696_);
if (v_isSharedCheck_4828_ == 0)
{
v___x_4747_ = v_cctx_4696_;
v_isShared_4748_ = v_isSharedCheck_4828_;
goto v_resetjp_4746_;
}
else
{
lean_inc(v_ref_4744_);
lean_inc(v_currRecDepth_4743_);
lean_inc(v_toCold_4742_);
lean_dec(v_cctx_4696_);
v___x_4747_ = lean_box(0);
v_isShared_4748_ = v_isSharedCheck_4828_;
goto v_resetjp_4746_;
}
v_resetjp_4746_:
{
lean_object* v_fileName_4749_; lean_object* v_fileMap_4750_; lean_object* v_options_4751_; lean_object* v_currNamespace_4752_; lean_object* v_openDecls_4753_; lean_object* v_initHeartbeats_4754_; lean_object* v_maxHeartbeats_4755_; lean_object* v_quotContext_4756_; lean_object* v_currMacroScope_4757_; lean_object* v_cancelTk_x3f_4758_; lean_object* v___x_4760_; uint8_t v_isShared_4761_; uint8_t v_isSharedCheck_4825_; 
v_fileName_4749_ = lean_ctor_get(v_toCold_4742_, 0);
v_fileMap_4750_ = lean_ctor_get(v_toCold_4742_, 1);
v_options_4751_ = lean_ctor_get(v_toCold_4742_, 2);
v_currNamespace_4752_ = lean_ctor_get(v_toCold_4742_, 4);
v_openDecls_4753_ = lean_ctor_get(v_toCold_4742_, 5);
v_initHeartbeats_4754_ = lean_ctor_get(v_toCold_4742_, 6);
v_maxHeartbeats_4755_ = lean_ctor_get(v_toCold_4742_, 7);
v_quotContext_4756_ = lean_ctor_get(v_toCold_4742_, 8);
v_currMacroScope_4757_ = lean_ctor_get(v_toCold_4742_, 9);
v_cancelTk_x3f_4758_ = lean_ctor_get(v_toCold_4742_, 10);
v_isSharedCheck_4825_ = !lean_is_exclusive(v_toCold_4742_);
if (v_isSharedCheck_4825_ == 0)
{
lean_object* v_unused_4826_; lean_object* v_unused_4827_; 
v_unused_4826_ = lean_ctor_get(v_toCold_4742_, 11);
lean_dec(v_unused_4826_);
v_unused_4827_ = lean_ctor_get(v_toCold_4742_, 3);
lean_dec(v_unused_4827_);
v___x_4760_ = v_toCold_4742_;
v_isShared_4761_ = v_isSharedCheck_4825_;
goto v_resetjp_4759_;
}
else
{
lean_inc(v_cancelTk_x3f_4758_);
lean_inc(v_currMacroScope_4757_);
lean_inc(v_quotContext_4756_);
lean_inc(v_maxHeartbeats_4755_);
lean_inc(v_initHeartbeats_4754_);
lean_inc(v_openDecls_4753_);
lean_inc(v_currNamespace_4752_);
lean_inc(v_options_4751_);
lean_inc(v_fileMap_4750_);
lean_inc(v_fileName_4749_);
lean_dec(v_toCold_4742_);
v___x_4760_ = lean_box(0);
v_isShared_4761_ = v_isSharedCheck_4825_;
goto v_resetjp_4759_;
}
v_resetjp_4759_:
{
lean_object* v___x_4762_; uint8_t v___x_4763_; lean_object* v___y_4765_; lean_object* v___x_4800_; uint8_t v___y_4802_; lean_object* v_env_4823_; uint8_t v___x_4824_; 
v___x_4762_ = l_Lean_diagnostics;
v___x_4763_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(v_options_4751_, v___x_4762_);
v___x_4800_ = lean_st_ref_get(v___x_4739_);
v_env_4823_ = lean_ctor_get(v___x_4800_, 0);
lean_inc_ref(v_env_4823_);
lean_dec(v___x_4800_);
v___x_4824_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4823_);
lean_dec_ref(v_env_4823_);
if (v___x_4763_ == 0)
{
if (v___x_4824_ == 0)
{
lean_inc(v___x_4739_);
v___y_4765_ = v___x_4739_;
goto v___jp_4764_;
}
else
{
v___y_4802_ = v___x_4763_;
goto v___jp_4801_;
}
}
else
{
v___y_4802_ = v___x_4824_;
goto v___jp_4801_;
}
v___jp_4764_:
{
lean_object* v___x_4766_; lean_object* v___x_4767_; lean_object* v___x_4769_; 
v___x_4766_ = l_Lean_maxRecDepth;
v___x_4767_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1(v_options_4751_, v___x_4766_);
if (v_isShared_4761_ == 0)
{
lean_ctor_set(v___x_4760_, 11, v___x_4741_);
lean_ctor_set(v___x_4760_, 3, v___x_4767_);
v___x_4769_ = v___x_4760_;
goto v_reusejp_4768_;
}
else
{
lean_object* v_reuseFailAlloc_4799_; 
v_reuseFailAlloc_4799_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_4799_, 0, v_fileName_4749_);
lean_ctor_set(v_reuseFailAlloc_4799_, 1, v_fileMap_4750_);
lean_ctor_set(v_reuseFailAlloc_4799_, 2, v_options_4751_);
lean_ctor_set(v_reuseFailAlloc_4799_, 3, v___x_4767_);
lean_ctor_set(v_reuseFailAlloc_4799_, 4, v_currNamespace_4752_);
lean_ctor_set(v_reuseFailAlloc_4799_, 5, v_openDecls_4753_);
lean_ctor_set(v_reuseFailAlloc_4799_, 6, v_initHeartbeats_4754_);
lean_ctor_set(v_reuseFailAlloc_4799_, 7, v_maxHeartbeats_4755_);
lean_ctor_set(v_reuseFailAlloc_4799_, 8, v_quotContext_4756_);
lean_ctor_set(v_reuseFailAlloc_4799_, 9, v_currMacroScope_4757_);
lean_ctor_set(v_reuseFailAlloc_4799_, 10, v_cancelTk_x3f_4758_);
lean_ctor_set(v_reuseFailAlloc_4799_, 11, v___x_4741_);
v___x_4769_ = v_reuseFailAlloc_4799_;
goto v_reusejp_4768_;
}
v_reusejp_4768_:
{
lean_object* v___x_4771_; 
if (v_isShared_4748_ == 0)
{
lean_ctor_set(v___x_4747_, 0, v___x_4769_);
v___x_4771_ = v___x_4747_;
goto v_reusejp_4770_;
}
else
{
lean_object* v_reuseFailAlloc_4798_; 
v_reuseFailAlloc_4798_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4798_, 0, v___x_4769_);
lean_ctor_set(v_reuseFailAlloc_4798_, 1, v_currRecDepth_4743_);
lean_ctor_set(v_reuseFailAlloc_4798_, 2, v_ref_4744_);
lean_ctor_set_uint8(v_reuseFailAlloc_4798_, sizeof(void*)*3 + 1, v_suppressElabErrors_4745_);
v___x_4771_ = v_reuseFailAlloc_4798_;
goto v_reusejp_4770_;
}
v_reusejp_4770_:
{
lean_object* v___x_4772_; lean_object* v___x_4773_; 
lean_ctor_set_uint8(v___x_4771_, sizeof(void*)*3, v___x_4763_);
v___x_4772_ = lean_st_mk_ref(v___x_4721_);
lean_inc(v___x_4772_);
lean_inc(v_name_4706_);
v___x_4773_ = lean_apply_7(v_act_4702_, v_name_4706_, v_c_4703_, v___x_4732_, v___x_4772_, v___x_4771_, v___y_4765_, lean_box(0));
if (lean_obj_tag(v___x_4773_) == 0)
{
lean_object* v_a_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v_ngen_4777_; lean_object* v_cache_4778_; lean_object* v_cache_4779_; lean_object* v___x_4781_; 
lean_dec(v_name_4706_);
lean_dec(v_modName_4698_);
v_a_4774_ = lean_ctor_get(v___x_4773_, 0);
lean_inc(v_a_4774_);
lean_dec_ref_known(v___x_4773_, 1);
v___x_4775_ = lean_st_ref_get(v___x_4772_);
lean_dec(v___x_4772_);
v___x_4776_ = lean_st_ref_get(v___x_4739_);
lean_dec(v___x_4739_);
v_ngen_4777_ = lean_ctor_get(v___x_4776_, 2);
lean_inc_ref(v_ngen_4777_);
v_cache_4778_ = lean_ctor_get(v___x_4776_, 5);
lean_inc_ref(v_cache_4778_);
lean_dec(v___x_4776_);
v_cache_4779_ = lean_ctor_get(v___x_4775_, 1);
lean_inc_ref(v_cache_4779_);
lean_dec(v___x_4775_);
if (v_isShared_4716_ == 0)
{
lean_ctor_set(v___x_4715_, 2, v_cache_4779_);
lean_ctor_set(v___x_4715_, 1, v_cache_4778_);
lean_ctor_set(v___x_4715_, 0, v_ngen_4777_);
v___x_4781_ = v___x_4715_;
goto v_reusejp_4780_;
}
else
{
lean_object* v_reuseFailAlloc_4792_; 
v_reuseFailAlloc_4792_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4792_, 0, v_ngen_4777_);
lean_ctor_set(v_reuseFailAlloc_4792_, 1, v_cache_4778_);
lean_ctor_set(v_reuseFailAlloc_4792_, 2, v_cache_4779_);
v___x_4781_ = v_reuseFailAlloc_4792_;
goto v_reusejp_4780_;
}
v_reusejp_4780_:
{
lean_object* v___x_4782_; lean_object* v___x_4783_; uint8_t v___x_4784_; 
v___x_4782_ = lean_st_ref_swap(v_cacheRef_4700_, v___x_4781_);
lean_dec(v___x_4782_);
v___x_4783_ = lean_array_get_size(v_a_4774_);
v___x_4784_ = lean_nat_dec_lt(v___x_4717_, v___x_4783_);
if (v___x_4784_ == 0)
{
lean_dec(v_a_4774_);
return v_tree_4701_;
}
else
{
uint8_t v___x_4785_; 
v___x_4785_ = lean_nat_dec_le(v___x_4783_, v___x_4783_);
if (v___x_4785_ == 0)
{
if (v___x_4784_ == 0)
{
lean_dec(v_a_4774_);
return v_tree_4701_;
}
else
{
size_t v___x_4786_; size_t v___x_4787_; lean_object* v___x_4788_; 
v___x_4786_ = ((size_t)0ULL);
v___x_4787_ = lean_usize_of_nat(v___x_4783_);
v___x_4788_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg(v_a_4774_, v___x_4786_, v___x_4787_, v_tree_4701_);
lean_dec(v_a_4774_);
return v___x_4788_;
}
}
else
{
size_t v___x_4789_; size_t v___x_4790_; lean_object* v___x_4791_; 
v___x_4789_ = ((size_t)0ULL);
v___x_4790_ = lean_usize_of_nat(v___x_4783_);
v___x_4791_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg(v_a_4774_, v___x_4789_, v___x_4790_, v_tree_4701_);
lean_dec(v_a_4774_);
return v___x_4791_;
}
}
}
}
else
{
lean_object* v_a_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; 
lean_dec(v___x_4772_);
lean_dec(v___x_4739_);
lean_del_object(v___x_4715_);
v_a_4793_ = lean_ctor_get(v___x_4773_, 0);
lean_inc(v_a_4793_);
lean_dec_ref_known(v___x_4773_, 1);
v___x_4794_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4794_, 0, v_modName_4698_);
lean_ctor_set(v___x_4794_, 1, v_name_4706_);
lean_ctor_set(v___x_4794_, 2, v_a_4793_);
v___x_4795_ = lean_st_ref_take(v_d_4699_);
v___x_4796_ = lean_array_push(v___x_4795_, v___x_4794_);
v___x_4797_ = lean_st_ref_put(v_d_4699_, v___x_4796_);
return v_tree_4701_;
}
}
}
}
v___jp_4801_:
{
if (v___y_4802_ == 0)
{
lean_object* v___x_4803_; lean_object* v_env_4804_; lean_object* v_nextMacroScope_4805_; lean_object* v_ngen_4806_; lean_object* v_auxDeclNGen_4807_; lean_object* v_traceState_4808_; lean_object* v_messages_4809_; lean_object* v_infoState_4810_; lean_object* v_snapshotTasks_4811_; lean_object* v___x_4813_; uint8_t v_isShared_4814_; uint8_t v_isSharedCheck_4821_; 
v___x_4803_ = lean_st_ref_take(v___x_4739_);
v_env_4804_ = lean_ctor_get(v___x_4803_, 0);
v_nextMacroScope_4805_ = lean_ctor_get(v___x_4803_, 1);
v_ngen_4806_ = lean_ctor_get(v___x_4803_, 2);
v_auxDeclNGen_4807_ = lean_ctor_get(v___x_4803_, 3);
v_traceState_4808_ = lean_ctor_get(v___x_4803_, 4);
v_messages_4809_ = lean_ctor_get(v___x_4803_, 6);
v_infoState_4810_ = lean_ctor_get(v___x_4803_, 7);
v_snapshotTasks_4811_ = lean_ctor_get(v___x_4803_, 8);
v_isSharedCheck_4821_ = !lean_is_exclusive(v___x_4803_);
if (v_isSharedCheck_4821_ == 0)
{
lean_object* v_unused_4822_; 
v_unused_4822_ = lean_ctor_get(v___x_4803_, 5);
lean_dec(v_unused_4822_);
v___x_4813_ = v___x_4803_;
v_isShared_4814_ = v_isSharedCheck_4821_;
goto v_resetjp_4812_;
}
else
{
lean_inc(v_snapshotTasks_4811_);
lean_inc(v_infoState_4810_);
lean_inc(v_messages_4809_);
lean_inc(v_traceState_4808_);
lean_inc(v_auxDeclNGen_4807_);
lean_inc(v_ngen_4806_);
lean_inc(v_nextMacroScope_4805_);
lean_inc(v_env_4804_);
lean_dec(v___x_4803_);
v___x_4813_ = lean_box(0);
v_isShared_4814_ = v_isSharedCheck_4821_;
goto v_resetjp_4812_;
}
v_resetjp_4812_:
{
lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4818_; 
v___x_4815_ = l_Lean_Kernel_enableDiag(v_env_4804_, v___x_4763_);
v___x_4816_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12);
if (v_isShared_4814_ == 0)
{
lean_ctor_set(v___x_4813_, 5, v___x_4816_);
lean_ctor_set(v___x_4813_, 0, v___x_4815_);
v___x_4818_ = v___x_4813_;
goto v_reusejp_4817_;
}
else
{
lean_object* v_reuseFailAlloc_4820_; 
v_reuseFailAlloc_4820_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4820_, 0, v___x_4815_);
lean_ctor_set(v_reuseFailAlloc_4820_, 1, v_nextMacroScope_4805_);
lean_ctor_set(v_reuseFailAlloc_4820_, 2, v_ngen_4806_);
lean_ctor_set(v_reuseFailAlloc_4820_, 3, v_auxDeclNGen_4807_);
lean_ctor_set(v_reuseFailAlloc_4820_, 4, v_traceState_4808_);
lean_ctor_set(v_reuseFailAlloc_4820_, 5, v___x_4816_);
lean_ctor_set(v_reuseFailAlloc_4820_, 6, v_messages_4809_);
lean_ctor_set(v_reuseFailAlloc_4820_, 7, v_infoState_4810_);
lean_ctor_set(v_reuseFailAlloc_4820_, 8, v_snapshotTasks_4811_);
v___x_4818_ = v_reuseFailAlloc_4820_;
goto v_reusejp_4817_;
}
v_reusejp_4817_:
{
lean_object* v___x_4819_; 
v___x_4819_ = lean_st_ref_put(v___x_4739_, v___x_4818_);
lean_inc(v___x_4739_);
v___y_4765_ = v___x_4739_;
goto v___jp_4764_;
}
}
}
else
{
lean_inc(v___x_4739_);
v___y_4765_ = v___x_4739_;
goto v___jp_4764_;
}
}
}
}
}
}
else
{
lean_dec(v_name_4706_);
lean_dec_ref(v_c_4703_);
lean_dec_ref(v_act_4702_);
lean_dec(v_modName_4698_);
lean_dec_ref(v_env_4697_);
lean_dec_ref(v_cctx_4696_);
return v_tree_4701_;
}
}
else
{
lean_dec_ref(v_c_4703_);
lean_dec_ref(v_act_4702_);
lean_dec(v_modName_4698_);
lean_dec_ref(v_env_4697_);
lean_dec_ref(v_cctx_4696_);
return v_tree_4701_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___boxed(lean_object* v_cctx_4830_, lean_object* v_env_4831_, lean_object* v_modName_4832_, lean_object* v_d_4833_, lean_object* v_cacheRef_4834_, lean_object* v_tree_4835_, lean_object* v_act_4836_, lean_object* v_c_4837_, lean_object* v_a_4838_){
_start:
{
lean_object* v_res_4839_; 
v_res_4839_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_4830_, v_env_4831_, v_modName_4832_, v_d_4833_, v_cacheRef_4834_, v_tree_4835_, v_act_4836_, v_c_4837_);
lean_dec(v_cacheRef_4834_);
lean_dec(v_d_4833_);
return v_res_4839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData(lean_object* v_00_u03b1_4840_, lean_object* v_cctx_4841_, lean_object* v_env_4842_, lean_object* v_modName_4843_, lean_object* v_d_4844_, lean_object* v_cacheRef_4845_, lean_object* v_tree_4846_, lean_object* v_act_4847_, lean_object* v_c_4848_){
_start:
{
lean_object* v___x_4850_; 
v___x_4850_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_4841_, v_env_4842_, v_modName_4843_, v_d_4844_, v_cacheRef_4845_, v_tree_4846_, v_act_4847_, v_c_4848_);
return v___x_4850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___boxed(lean_object* v_00_u03b1_4851_, lean_object* v_cctx_4852_, lean_object* v_env_4853_, lean_object* v_modName_4854_, lean_object* v_d_4855_, lean_object* v_cacheRef_4856_, lean_object* v_tree_4857_, lean_object* v_act_4858_, lean_object* v_c_4859_, lean_object* v_a_4860_){
_start:
{
lean_object* v_res_4861_; 
v_res_4861_ = l_Lean_Meta_LazyDiscrTree_addConstImportData(v_00_u03b1_4851_, v_cctx_4852_, v_env_4853_, v_modName_4854_, v_d_4855_, v_cacheRef_4856_, v_tree_4857_, v_act_4858_, v_c_4859_);
lean_dec(v_cacheRef_4856_);
lean_dec(v_d_4855_);
return v_res_4861_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2(lean_object* v_00_u03b1_4862_, lean_object* v_as_4863_, size_t v_i_4864_, size_t v_stop_4865_, lean_object* v_b_4866_){
_start:
{
lean_object* v___x_4867_; 
v___x_4867_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg(v_as_4863_, v_i_4864_, v_stop_4865_, v_b_4866_);
return v___x_4867_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___boxed(lean_object* v_00_u03b1_4868_, lean_object* v_as_4869_, lean_object* v_i_4870_, lean_object* v_stop_4871_, lean_object* v_b_4872_){
_start:
{
size_t v_i_boxed_4873_; size_t v_stop_boxed_4874_; lean_object* v_res_4875_; 
v_i_boxed_4873_ = lean_unbox_usize(v_i_4870_);
lean_dec(v_i_4870_);
v_stop_boxed_4874_ = lean_unbox_usize(v_stop_4871_);
lean_dec(v_stop_4871_);
v_res_4875_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2(v_00_u03b1_4868_, v_as_4869_, v_i_boxed_4873_, v_stop_boxed_4874_, v_b_4872_);
lean_dec_ref(v_as_4869_);
return v_res_4875_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___redArg___closed__0(void){
_start:
{
lean_object* v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; 
v___x_4876_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__0));
v___x_4877_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1);
v___x_4878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4878_, 0, v___x_4877_);
lean_ctor_set(v___x_4878_, 1, v___x_4876_);
return v___x_4878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___redArg(){
_start:
{
lean_object* v___x_4880_; 
v___x_4880_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___redArg___closed__0);
return v___x_4880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___redArg___boxed(lean_object* v___dummy_4881_){
_start:
{
lean_object* v_res_4882_; 
v_res_4882_ = l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___redArg();
return v_res_4882_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0(void){
_start:
{
lean_object* v___x_4883_; 
v___x_4883_ = l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___redArg();
return v___x_4883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults(lean_object* v_00_u03b1_4884_){
_start:
{
lean_object* v___x_4885_; 
v___x_4885_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0);
return v___x_4885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_append___redArg(lean_object* v_x_4886_, lean_object* v_y_4887_){
_start:
{
lean_object* v_tree_4888_; lean_object* v_errors_4889_; lean_object* v_tree_4890_; lean_object* v_errors_4891_; lean_object* v___x_4893_; uint8_t v_isShared_4894_; uint8_t v_isSharedCheck_4900_; 
v_tree_4888_ = lean_ctor_get(v_x_4886_, 0);
lean_inc_ref(v_tree_4888_);
v_errors_4889_ = lean_ctor_get(v_x_4886_, 1);
lean_inc_ref(v_errors_4889_);
lean_dec_ref(v_x_4886_);
v_tree_4890_ = lean_ctor_get(v_y_4887_, 0);
v_errors_4891_ = lean_ctor_get(v_y_4887_, 1);
v_isSharedCheck_4900_ = !lean_is_exclusive(v_y_4887_);
if (v_isSharedCheck_4900_ == 0)
{
v___x_4893_ = v_y_4887_;
v_isShared_4894_ = v_isSharedCheck_4900_;
goto v_resetjp_4892_;
}
else
{
lean_inc(v_errors_4891_);
lean_inc(v_tree_4890_);
lean_dec(v_y_4887_);
v___x_4893_ = lean_box(0);
v_isShared_4894_ = v_isSharedCheck_4900_;
goto v_resetjp_4892_;
}
v_resetjp_4892_:
{
lean_object* v___x_4895_; lean_object* v___x_4896_; lean_object* v___x_4898_; 
v___x_4895_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg(v_tree_4888_, v_tree_4890_);
v___x_4896_ = l_Array_append___redArg(v_errors_4889_, v_errors_4891_);
lean_dec_ref(v_errors_4891_);
if (v_isShared_4894_ == 0)
{
lean_ctor_set(v___x_4893_, 1, v___x_4896_);
lean_ctor_set(v___x_4893_, 0, v___x_4895_);
v___x_4898_ = v___x_4893_;
goto v_reusejp_4897_;
}
else
{
lean_object* v_reuseFailAlloc_4899_; 
v_reuseFailAlloc_4899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4899_, 0, v___x_4895_);
lean_ctor_set(v_reuseFailAlloc_4899_, 1, v___x_4896_);
v___x_4898_ = v_reuseFailAlloc_4899_;
goto v_reusejp_4897_;
}
v_reusejp_4897_:
{
return v___x_4898_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_append(lean_object* v_00_u03b1_4901_, lean_object* v_x_4902_, lean_object* v_y_4903_){
_start:
{
lean_object* v___x_4904_; 
v___x_4904_ = l_Lean_Meta_LazyDiscrTree_InitResults_append___redArg(v_x_4902_, v_y_4903_);
return v___x_4904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___redArg(){
_start:
{
lean_object* v___x_4907_; 
v___x_4907_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___redArg___closed__0));
return v___x_4907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___redArg___boxed(lean_object* v___dummy_4908_){
_start:
{
lean_object* v_res_4909_; 
v_res_4909_ = l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___redArg();
return v_res_4909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_instAppend(lean_object* v_00_u03b1_4910_){
_start:
{
lean_object* v___x_4911_; 
v___x_4911_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___redArg___closed__0));
return v___x_4911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat___redArg(lean_object* v_d_4912_, lean_object* v_tree_4913_){
_start:
{
lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; 
v___x_4915_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_ImportData_new___closed__0));
v___x_4916_ = lean_st_ref_swap(v_d_4912_, v___x_4915_);
v___x_4917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4917_, 0, v_tree_4913_);
lean_ctor_set(v___x_4917_, 1, v___x_4916_);
return v___x_4917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat___redArg___boxed(lean_object* v_d_4918_, lean_object* v_tree_4919_, lean_object* v_a_4920_){
_start:
{
lean_object* v_res_4921_; 
v_res_4921_ = l_Lean_Meta_LazyDiscrTree_toFlat___redArg(v_d_4918_, v_tree_4919_);
lean_dec(v_d_4918_);
return v_res_4921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat(lean_object* v_00_u03b1_4922_, lean_object* v_d_4923_, lean_object* v_tree_4924_){
_start:
{
lean_object* v___x_4926_; 
v___x_4926_ = l_Lean_Meta_LazyDiscrTree_toFlat___redArg(v_d_4923_, v_tree_4924_);
return v___x_4926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat___boxed(lean_object* v_00_u03b1_4927_, lean_object* v_d_4928_, lean_object* v_tree_4929_, lean_object* v_a_4930_){
_start:
{
lean_object* v_res_4931_; 
v_res_4931_ = l_Lean_Meta_LazyDiscrTree_toFlat(v_00_u03b1_4927_, v_d_4928_, v_tree_4929_);
lean_dec(v_d_4928_);
return v_res_4931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(lean_object* v_cctx_4932_, lean_object* v_env_4933_, lean_object* v_act_4934_, lean_object* v_d_4935_, lean_object* v_cacheRef_4936_, lean_object* v_tree_4937_, lean_object* v_mname_4938_, lean_object* v_mdata_4939_, lean_object* v_i_4940_){
_start:
{
lean_object* v_constants_4942_; lean_object* v___x_4943_; uint8_t v___x_4944_; 
v_constants_4942_ = lean_ctor_get(v_mdata_4939_, 2);
v___x_4943_ = lean_array_get_size(v_constants_4942_);
v___x_4944_ = lean_nat_dec_lt(v_i_4940_, v___x_4943_);
if (v___x_4944_ == 0)
{
lean_dec(v_i_4940_);
lean_dec(v_mname_4938_);
lean_dec_ref(v_act_4934_);
lean_dec_ref(v_env_4933_);
lean_dec_ref(v_cctx_4932_);
return v_tree_4937_;
}
else
{
lean_object* v___x_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; lean_object* v___x_4949_; 
v___x_4945_ = lean_array_fget_borrowed(v_constants_4942_, v_i_4940_);
lean_inc(v___x_4945_);
v___x_4946_ = l_Lean_AsyncConstantInfo_ofConstantInfo(v___x_4945_);
lean_inc_ref(v_act_4934_);
lean_inc(v_mname_4938_);
lean_inc_ref(v_env_4933_);
lean_inc_ref(v_cctx_4932_);
v___x_4947_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_4932_, v_env_4933_, v_mname_4938_, v_d_4935_, v_cacheRef_4936_, v_tree_4937_, v_act_4934_, v___x_4946_);
v___x_4948_ = lean_unsigned_to_nat(1u);
v___x_4949_ = lean_nat_add(v_i_4940_, v___x_4948_);
lean_dec(v_i_4940_);
v_tree_4937_ = v___x_4947_;
v_i_4940_ = v___x_4949_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg___boxed(lean_object* v_cctx_4951_, lean_object* v_env_4952_, lean_object* v_act_4953_, lean_object* v_d_4954_, lean_object* v_cacheRef_4955_, lean_object* v_tree_4956_, lean_object* v_mname_4957_, lean_object* v_mdata_4958_, lean_object* v_i_4959_, lean_object* v_a_4960_){
_start:
{
lean_object* v_res_4961_; 
v_res_4961_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(v_cctx_4951_, v_env_4952_, v_act_4953_, v_d_4954_, v_cacheRef_4955_, v_tree_4956_, v_mname_4957_, v_mdata_4958_, v_i_4959_);
lean_dec_ref(v_mdata_4958_);
lean_dec(v_cacheRef_4955_);
lean_dec(v_d_4954_);
return v_res_4961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule(lean_object* v_00_u03b1_4962_, lean_object* v_cctx_4963_, lean_object* v_env_4964_, lean_object* v_act_4965_, lean_object* v_d_4966_, lean_object* v_cacheRef_4967_, lean_object* v_tree_4968_, lean_object* v_mname_4969_, lean_object* v_mdata_4970_, lean_object* v_i_4971_){
_start:
{
lean_object* v___x_4973_; 
v___x_4973_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(v_cctx_4963_, v_env_4964_, v_act_4965_, v_d_4966_, v_cacheRef_4967_, v_tree_4968_, v_mname_4969_, v_mdata_4970_, v_i_4971_);
return v___x_4973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule___boxed(lean_object* v_00_u03b1_4974_, lean_object* v_cctx_4975_, lean_object* v_env_4976_, lean_object* v_act_4977_, lean_object* v_d_4978_, lean_object* v_cacheRef_4979_, lean_object* v_tree_4980_, lean_object* v_mname_4981_, lean_object* v_mdata_4982_, lean_object* v_i_4983_, lean_object* v_a_4984_){
_start:
{
lean_object* v_res_4985_; 
v_res_4985_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule(v_00_u03b1_4974_, v_cctx_4975_, v_env_4976_, v_act_4977_, v_d_4978_, v_cacheRef_4979_, v_tree_4980_, v_mname_4981_, v_mdata_4982_, v_i_4983_);
lean_dec_ref(v_mdata_4982_);
lean_dec(v_cacheRef_4979_);
lean_dec(v_d_4978_);
return v_res_4985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg(lean_object* v_cctx_4986_, lean_object* v_env_4987_, lean_object* v_act_4988_, lean_object* v_d_4989_, lean_object* v_cacheRef_4990_, lean_object* v_tree_4991_, lean_object* v_start_4992_, lean_object* v_stop_4993_){
_start:
{
uint8_t v___x_4995_; 
v___x_4995_ = lean_nat_dec_lt(v_start_4992_, v_stop_4993_);
if (v___x_4995_ == 0)
{
lean_object* v___x_4996_; 
lean_dec(v_start_4992_);
lean_dec_ref(v_act_4988_);
lean_dec_ref(v_env_4987_);
lean_dec_ref(v_cctx_4986_);
v___x_4996_ = l_Lean_Meta_LazyDiscrTree_toFlat___redArg(v_d_4989_, v_tree_4991_);
return v___x_4996_;
}
else
{
lean_object* v___x_4997_; lean_object* v_moduleData_4998_; lean_object* v___x_4999_; lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v_mname_5002_; lean_object* v_mdata_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; lean_object* v___x_5007_; 
v___x_4997_ = l_Lean_Environment_header(v_env_4987_);
v_moduleData_4998_ = lean_ctor_get(v___x_4997_, 6);
lean_inc_ref(v_moduleData_4998_);
v___x_4999_ = lean_box(0);
v___x_5000_ = l_Lean_instInhabitedModuleData_default;
v___x_5001_ = l_Lean_EnvironmentHeader_moduleNames(v___x_4997_);
v_mname_5002_ = lean_array_get(v___x_4999_, v___x_5001_, v_start_4992_);
lean_dec_ref(v___x_5001_);
v_mdata_5003_ = lean_array_get(v___x_5000_, v_moduleData_4998_, v_start_4992_);
lean_dec_ref(v_moduleData_4998_);
v___x_5004_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_act_4988_);
lean_inc_ref(v_env_4987_);
lean_inc_ref(v_cctx_4986_);
v___x_5005_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(v_cctx_4986_, v_env_4987_, v_act_4988_, v_d_4989_, v_cacheRef_4990_, v_tree_4991_, v_mname_5002_, v_mdata_5003_, v___x_5004_);
lean_dec(v_mdata_5003_);
v___x_5006_ = lean_unsigned_to_nat(1u);
v___x_5007_ = lean_nat_add(v_start_4992_, v___x_5006_);
lean_dec(v_start_4992_);
v_tree_4991_ = v___x_5005_;
v_start_4992_ = v___x_5007_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg___boxed(lean_object* v_cctx_5009_, lean_object* v_env_5010_, lean_object* v_act_5011_, lean_object* v_d_5012_, lean_object* v_cacheRef_5013_, lean_object* v_tree_5014_, lean_object* v_start_5015_, lean_object* v_stop_5016_, lean_object* v_a_5017_){
_start:
{
lean_object* v_res_5018_; 
v_res_5018_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg(v_cctx_5009_, v_env_5010_, v_act_5011_, v_d_5012_, v_cacheRef_5013_, v_tree_5014_, v_start_5015_, v_stop_5016_);
lean_dec(v_stop_5016_);
lean_dec(v_cacheRef_5013_);
lean_dec(v_d_5012_);
return v_res_5018_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go(lean_object* v_00_u03b1_5019_, lean_object* v_cctx_5020_, lean_object* v_env_5021_, lean_object* v_act_5022_, lean_object* v_d_5023_, lean_object* v_cacheRef_5024_, lean_object* v_tree_5025_, lean_object* v_start_5026_, lean_object* v_stop_5027_){
_start:
{
lean_object* v___x_5029_; 
v___x_5029_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg(v_cctx_5020_, v_env_5021_, v_act_5022_, v_d_5023_, v_cacheRef_5024_, v_tree_5025_, v_start_5026_, v_stop_5027_);
return v___x_5029_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___boxed(lean_object* v_00_u03b1_5030_, lean_object* v_cctx_5031_, lean_object* v_env_5032_, lean_object* v_act_5033_, lean_object* v_d_5034_, lean_object* v_cacheRef_5035_, lean_object* v_tree_5036_, lean_object* v_start_5037_, lean_object* v_stop_5038_, lean_object* v_a_5039_){
_start:
{
lean_object* v_res_5040_; 
v_res_5040_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go(v_00_u03b1_5030_, v_cctx_5031_, v_env_5032_, v_act_5033_, v_d_5034_, v_cacheRef_5035_, v_tree_5036_, v_start_5037_, v_stop_5038_);
lean_dec(v_stop_5038_);
lean_dec(v_cacheRef_5035_);
lean_dec(v_d_5034_);
return v_res_5040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___redArg(lean_object* v_cctx_5041_, lean_object* v_ngen_5042_, lean_object* v_env_5043_, lean_object* v_act_5044_, lean_object* v_start_5045_, lean_object* v_stop_5046_){
_start:
{
lean_object* v___x_5048_; lean_object* v___x_5049_; lean_object* v___x_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; 
v___x_5048_ = l_Lean_Meta_LazyDiscrTree_Cache_empty(v_ngen_5042_);
v___x_5049_ = lean_st_mk_ref(v___x_5048_);
v___x_5050_ = l_Lean_Meta_LazyDiscrTree_ImportData_new();
v___x_5051_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1);
v___x_5052_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg(v_cctx_5041_, v_env_5043_, v_act_5044_, v___x_5050_, v___x_5049_, v___x_5051_, v_start_5045_, v_stop_5046_);
lean_dec(v___x_5049_);
lean_dec(v___x_5050_);
return v___x_5052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___redArg___boxed(lean_object* v_cctx_5053_, lean_object* v_ngen_5054_, lean_object* v_env_5055_, lean_object* v_act_5056_, lean_object* v_start_5057_, lean_object* v_stop_5058_, lean_object* v_a_5059_){
_start:
{
lean_object* v_res_5060_; 
v_res_5060_ = l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___redArg(v_cctx_5053_, v_ngen_5054_, v_env_5055_, v_act_5056_, v_start_5057_, v_stop_5058_);
lean_dec(v_stop_5058_);
return v_res_5060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq(lean_object* v_00_u03b1_5061_, lean_object* v_cctx_5062_, lean_object* v_ngen_5063_, lean_object* v_env_5064_, lean_object* v_act_5065_, lean_object* v_start_5066_, lean_object* v_stop_5067_){
_start:
{
lean_object* v___x_5069_; 
v___x_5069_ = l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___redArg(v_cctx_5062_, v_ngen_5063_, v_env_5064_, v_act_5065_, v_start_5066_, v_stop_5067_);
return v___x_5069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed(lean_object* v_00_u03b1_5070_, lean_object* v_cctx_5071_, lean_object* v_ngen_5072_, lean_object* v_env_5073_, lean_object* v_act_5074_, lean_object* v_start_5075_, lean_object* v_stop_5076_, lean_object* v_a_5077_){
_start:
{
lean_object* v_res_5078_; 
v_res_5078_ = l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq(v_00_u03b1_5070_, v_cctx_5071_, v_ngen_5072_, v_env_5073_, v_act_5074_, v_start_5075_, v_stop_5076_);
lean_dec(v_stop_5076_);
return v_res_5078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___redArg___lam__0(lean_object* v_inst_5079_, lean_object* v_x1_5080_, lean_object* v_x2_5081_){
_start:
{
lean_object* v___x_5082_; lean_object* v___x_5083_; 
v___x_5082_ = lean_task_get_own(v_x2_5081_);
v___x_5083_ = lean_apply_2(v_inst_5079_, v_x1_5080_, v___x_5082_);
return v___x_5083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___redArg(lean_object* v_inst_5084_, lean_object* v_z_5085_, lean_object* v_tasks_5086_){
_start:
{
lean_object* v___x_5087_; lean_object* v___x_5088_; lean_object* v___x_5089_; uint8_t v___x_5090_; 
v___x_5087_ = lean_unsigned_to_nat(0u);
v___x_5088_ = lean_array_get_size(v_tasks_5086_);
v___x_5089_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__9));
v___x_5090_ = lean_nat_dec_lt(v___x_5087_, v___x_5088_);
if (v___x_5090_ == 0)
{
lean_dec_ref(v_tasks_5086_);
lean_dec(v_inst_5084_);
return v_z_5085_;
}
else
{
lean_object* v___f_5091_; uint8_t v___x_5092_; 
v___f_5091_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_combineGet___redArg___lam__0), 3, 1);
lean_closure_set(v___f_5091_, 0, v_inst_5084_);
v___x_5092_ = lean_nat_dec_le(v___x_5088_, v___x_5088_);
if (v___x_5092_ == 0)
{
if (v___x_5090_ == 0)
{
lean_dec_ref(v___f_5091_);
lean_dec_ref(v_tasks_5086_);
return v_z_5085_;
}
else
{
size_t v___x_5093_; size_t v___x_5094_; lean_object* v___x_5095_; 
v___x_5093_ = ((size_t)0ULL);
v___x_5094_ = lean_usize_of_nat(v___x_5088_);
v___x_5095_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_5089_, v___f_5091_, v_tasks_5086_, v___x_5093_, v___x_5094_, v_z_5085_);
return v___x_5095_;
}
}
else
{
size_t v___x_5096_; size_t v___x_5097_; lean_object* v___x_5098_; 
v___x_5096_ = ((size_t)0ULL);
v___x_5097_ = lean_usize_of_nat(v___x_5088_);
v___x_5098_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_5089_, v___f_5091_, v_tasks_5086_, v___x_5096_, v___x_5097_, v_z_5085_);
return v___x_5098_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet(lean_object* v_00_u03b1_5099_, lean_object* v_inst_5100_, lean_object* v_z_5101_, lean_object* v_tasks_5102_){
_start:
{
lean_object* v___x_5103_; 
v___x_5103_ = l_Lean_Meta_LazyDiscrTree_combineGet___redArg(v_inst_5100_, v_z_5101_, v_tasks_5102_);
return v___x_5103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg___lam__0(lean_object* v_toPure_5104_, lean_object* v___x_5105_, lean_object* v_____r_5106_){
_start:
{
lean_object* v___x_5107_; 
v___x_5107_ = lean_apply_2(v_toPure_5104_, lean_box(0), v___x_5105_);
return v___x_5107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg___lam__1(lean_object* v_toPure_5108_, lean_object* v_setNGen_5109_, lean_object* v_toBind_5110_, lean_object* v_ngen_5111_){
_start:
{
lean_object* v_namePrefix_5112_; lean_object* v_idx_5113_; lean_object* v___x_5115_; uint8_t v_isShared_5116_; uint8_t v_isSharedCheck_5127_; 
v_namePrefix_5112_ = lean_ctor_get(v_ngen_5111_, 0);
v_idx_5113_ = lean_ctor_get(v_ngen_5111_, 1);
v_isSharedCheck_5127_ = !lean_is_exclusive(v_ngen_5111_);
if (v_isSharedCheck_5127_ == 0)
{
v___x_5115_ = v_ngen_5111_;
v_isShared_5116_ = v_isSharedCheck_5127_;
goto v_resetjp_5114_;
}
else
{
lean_inc(v_idx_5113_);
lean_inc(v_namePrefix_5112_);
lean_dec(v_ngen_5111_);
v___x_5115_ = lean_box(0);
v_isShared_5116_ = v_isSharedCheck_5127_;
goto v_resetjp_5114_;
}
v_resetjp_5114_:
{
lean_object* v___x_5117_; lean_object* v___x_5118_; lean_object* v___x_5120_; 
lean_inc(v_idx_5113_);
lean_inc(v_namePrefix_5112_);
v___x_5117_ = l_Lean_Name_num___override(v_namePrefix_5112_, v_idx_5113_);
v___x_5118_ = lean_unsigned_to_nat(1u);
if (v_isShared_5116_ == 0)
{
lean_ctor_set(v___x_5115_, 1, v___x_5118_);
lean_ctor_set(v___x_5115_, 0, v___x_5117_);
v___x_5120_ = v___x_5115_;
goto v_reusejp_5119_;
}
else
{
lean_object* v_reuseFailAlloc_5126_; 
v_reuseFailAlloc_5126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5126_, 0, v___x_5117_);
lean_ctor_set(v_reuseFailAlloc_5126_, 1, v___x_5118_);
v___x_5120_ = v_reuseFailAlloc_5126_;
goto v_reusejp_5119_;
}
v_reusejp_5119_:
{
lean_object* v___f_5121_; lean_object* v___x_5122_; lean_object* v___x_5123_; lean_object* v___x_5124_; lean_object* v___x_5125_; 
v___f_5121_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5121_, 0, v_toPure_5108_);
lean_closure_set(v___f_5121_, 1, v___x_5120_);
v___x_5122_ = lean_nat_add(v_idx_5113_, v___x_5118_);
lean_dec(v_idx_5113_);
v___x_5123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5123_, 0, v_namePrefix_5112_);
lean_ctor_set(v___x_5123_, 1, v___x_5122_);
v___x_5124_ = lean_apply_1(v_setNGen_5109_, v___x_5123_);
v___x_5125_ = lean_apply_4(v_toBind_5110_, lean_box(0), lean_box(0), v___x_5124_, v___f_5121_);
return v___x_5125_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg(lean_object* v_inst_5128_, lean_object* v_inst_5129_){
_start:
{
lean_object* v_toApplicative_5130_; lean_object* v_toBind_5131_; lean_object* v_getNGen_5132_; lean_object* v_setNGen_5133_; lean_object* v_toPure_5134_; lean_object* v___f_5135_; lean_object* v___x_5136_; 
v_toApplicative_5130_ = lean_ctor_get(v_inst_5128_, 0);
lean_inc_ref(v_toApplicative_5130_);
v_toBind_5131_ = lean_ctor_get(v_inst_5128_, 1);
lean_inc_n(v_toBind_5131_, 2);
lean_dec_ref(v_inst_5128_);
v_getNGen_5132_ = lean_ctor_get(v_inst_5129_, 0);
lean_inc(v_getNGen_5132_);
v_setNGen_5133_ = lean_ctor_get(v_inst_5129_, 1);
lean_inc(v_setNGen_5133_);
lean_dec_ref(v_inst_5129_);
v_toPure_5134_ = lean_ctor_get(v_toApplicative_5130_, 1);
lean_inc(v_toPure_5134_);
lean_dec_ref(v_toApplicative_5130_);
v___f_5135_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg___lam__1), 4, 3);
lean_closure_set(v___f_5135_, 0, v_toPure_5134_);
lean_closure_set(v___f_5135_, 1, v_setNGen_5133_);
lean_closure_set(v___f_5135_, 2, v_toBind_5131_);
v___x_5136_ = lean_apply_4(v_toBind_5131_, lean_box(0), lean_box(0), v_getNGen_5132_, v___f_5135_);
return v___x_5136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen(lean_object* v_M_5137_, lean_object* v_inst_5138_, lean_object* v_inst_5139_){
_start:
{
lean_object* v___x_5140_; 
v___x_5140_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg(v_inst_5138_, v_inst_5139_);
return v___x_5140_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg(lean_object* v_cctx_5141_, lean_object* v_env_5142_, lean_object* v_modName_5143_, lean_object* v_d_5144_, lean_object* v_val_5145_, lean_object* v_act_5146_, lean_object* v_as_5147_, size_t v_sz_5148_, size_t v_i_5149_, lean_object* v_b_5150_){
_start:
{
uint8_t v___x_5152_; 
v___x_5152_ = lean_usize_dec_lt(v_i_5149_, v_sz_5148_);
if (v___x_5152_ == 0)
{
lean_dec_ref(v_act_5146_);
lean_dec(v_modName_5143_);
lean_dec_ref(v_env_5142_);
lean_dec_ref(v_cctx_5141_);
return v_b_5150_;
}
else
{
lean_object* v_a_5153_; lean_object* v___x_5154_; size_t v___x_5155_; size_t v___x_5156_; 
v_a_5153_ = lean_array_uget_borrowed(v_as_5147_, v_i_5149_);
lean_inc(v_a_5153_);
lean_inc_ref(v_act_5146_);
lean_inc(v_modName_5143_);
lean_inc_ref(v_env_5142_);
lean_inc_ref(v_cctx_5141_);
v___x_5154_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_5141_, v_env_5142_, v_modName_5143_, v_d_5144_, v_val_5145_, v_b_5150_, v_act_5146_, v_a_5153_);
v___x_5155_ = ((size_t)1ULL);
v___x_5156_ = lean_usize_add(v_i_5149_, v___x_5155_);
v_i_5149_ = v___x_5156_;
v_b_5150_ = v___x_5154_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg___boxed(lean_object* v_cctx_5158_, lean_object* v_env_5159_, lean_object* v_modName_5160_, lean_object* v_d_5161_, lean_object* v_val_5162_, lean_object* v_act_5163_, lean_object* v_as_5164_, lean_object* v_sz_5165_, lean_object* v_i_5166_, lean_object* v_b_5167_, lean_object* v___y_5168_){
_start:
{
size_t v_sz_boxed_5169_; size_t v_i_boxed_5170_; lean_object* v_res_5171_; 
v_sz_boxed_5169_ = lean_unbox_usize(v_sz_5165_);
lean_dec(v_sz_5165_);
v_i_boxed_5170_ = lean_unbox_usize(v_i_5166_);
lean_dec(v_i_5166_);
v_res_5171_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg(v_cctx_5158_, v_env_5159_, v_modName_5160_, v_d_5161_, v_val_5162_, v_act_5163_, v_as_5164_, v_sz_boxed_5169_, v_i_boxed_5170_, v_b_5167_);
lean_dec_ref(v_as_5164_);
lean_dec(v_val_5162_);
lean_dec(v_d_5161_);
return v_res_5171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(lean_object* v_cctx_5172_, lean_object* v_ngen_5173_, lean_object* v_env_5174_, lean_object* v_d_5175_, lean_object* v_act_5176_){
_start:
{
lean_object* v___x_5178_; lean_object* v_mainModule_5179_; lean_object* v___x_5180_; lean_object* v___x_5181_; lean_object* v___x_5182_; uint8_t v___x_5183_; lean_object* v___x_5184_; size_t v_sz_5185_; size_t v___x_5186_; lean_object* v___x_5187_; 
v___x_5178_ = l_Lean_Environment_header(v_env_5174_);
v_mainModule_5179_ = lean_ctor_get(v___x_5178_, 0);
lean_inc(v_mainModule_5179_);
lean_dec_ref(v___x_5178_);
v___x_5180_ = l_Lean_Meta_LazyDiscrTree_Cache_empty(v_ngen_5173_);
v___x_5181_ = lean_st_mk_ref(v___x_5180_);
v___x_5182_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1);
v___x_5183_ = 1;
v___x_5184_ = l_Lean_Environment_getLocalConstantInfos(v_env_5174_, v___x_5183_);
v_sz_5185_ = lean_array_size(v___x_5184_);
v___x_5186_ = ((size_t)0ULL);
v___x_5187_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg(v_cctx_5172_, v_env_5174_, v_mainModule_5179_, v_d_5175_, v___x_5181_, v_act_5176_, v___x_5184_, v_sz_5185_, v___x_5186_, v___x_5182_);
lean_dec_ref(v___x_5184_);
lean_dec(v___x_5181_);
return v___x_5187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg___boxed(lean_object* v_cctx_5188_, lean_object* v_ngen_5189_, lean_object* v_env_5190_, lean_object* v_d_5191_, lean_object* v_act_5192_, lean_object* v_a_5193_){
_start:
{
lean_object* v_res_5194_; 
v_res_5194_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(v_cctx_5188_, v_ngen_5189_, v_env_5190_, v_d_5191_, v_act_5192_);
lean_dec(v_d_5191_);
return v_res_5194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree(lean_object* v_00_u03b1_5195_, lean_object* v_cctx_5196_, lean_object* v_ngen_5197_, lean_object* v_env_5198_, lean_object* v_d_5199_, lean_object* v_act_5200_){
_start:
{
lean_object* v___x_5202_; 
v___x_5202_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(v_cctx_5196_, v_ngen_5197_, v_env_5198_, v_d_5199_, v_act_5200_);
return v___x_5202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___boxed(lean_object* v_00_u03b1_5203_, lean_object* v_cctx_5204_, lean_object* v_ngen_5205_, lean_object* v_env_5206_, lean_object* v_d_5207_, lean_object* v_act_5208_, lean_object* v_a_5209_){
_start:
{
lean_object* v_res_5210_; 
v_res_5210_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree(v_00_u03b1_5203_, v_cctx_5204_, v_ngen_5205_, v_env_5206_, v_d_5207_, v_act_5208_);
lean_dec(v_d_5207_);
return v_res_5210_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0(lean_object* v_00_u03b1_5211_, lean_object* v_cctx_5212_, lean_object* v_env_5213_, lean_object* v_modName_5214_, lean_object* v_d_5215_, lean_object* v_val_5216_, lean_object* v_act_5217_, lean_object* v_as_5218_, size_t v_sz_5219_, size_t v_i_5220_, lean_object* v_b_5221_){
_start:
{
lean_object* v___x_5223_; 
v___x_5223_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg(v_cctx_5212_, v_env_5213_, v_modName_5214_, v_d_5215_, v_val_5216_, v_act_5217_, v_as_5218_, v_sz_5219_, v_i_5220_, v_b_5221_);
return v___x_5223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___boxed(lean_object* v_00_u03b1_5224_, lean_object* v_cctx_5225_, lean_object* v_env_5226_, lean_object* v_modName_5227_, lean_object* v_d_5228_, lean_object* v_val_5229_, lean_object* v_act_5230_, lean_object* v_as_5231_, lean_object* v_sz_5232_, lean_object* v_i_5233_, lean_object* v_b_5234_, lean_object* v___y_5235_){
_start:
{
size_t v_sz_boxed_5236_; size_t v_i_boxed_5237_; lean_object* v_res_5238_; 
v_sz_boxed_5236_ = lean_unbox_usize(v_sz_5232_);
lean_dec(v_sz_5232_);
v_i_boxed_5237_ = lean_unbox_usize(v_i_5233_);
lean_dec(v_i_5233_);
v_res_5238_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0(v_00_u03b1_5224_, v_cctx_5225_, v_env_5226_, v_modName_5227_, v_d_5228_, v_val_5229_, v_act_5230_, v_as_5231_, v_sz_boxed_5236_, v_i_boxed_5237_, v_b_5234_);
lean_dec_ref(v_as_5231_);
lean_dec(v_val_5229_);
lean_dec(v_d_5228_);
return v_res_5238_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(lean_object* v_x_5239_, lean_object* v_x_5240_, lean_object* v___y_5241_, lean_object* v___y_5242_, lean_object* v___y_5243_, lean_object* v___y_5244_){
_start:
{
if (lean_obj_tag(v_x_5240_) == 0)
{
lean_object* v___x_5246_; 
v___x_5246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5246_, 0, v_x_5239_);
return v___x_5246_;
}
else
{
lean_object* v_head_5247_; lean_object* v_tail_5248_; lean_object* v___x_5249_; 
v_head_5247_ = lean_ctor_get(v_x_5240_, 0);
lean_inc(v_head_5247_);
v_tail_5248_ = lean_ctor_get(v_x_5240_, 1);
lean_inc(v_tail_5248_);
lean_dec_ref_known(v_x_5240_, 2);
v___x_5249_ = l_Lean_Meta_LazyDiscrTree_dropKey___redArg(v_x_5239_, v_head_5247_, v___y_5241_, v___y_5242_, v___y_5243_, v___y_5244_);
if (lean_obj_tag(v___x_5249_) == 0)
{
lean_object* v_a_5250_; 
v_a_5250_ = lean_ctor_get(v___x_5249_, 0);
lean_inc(v_a_5250_);
lean_dec_ref_known(v___x_5249_, 1);
v_x_5239_ = v_a_5250_;
v_x_5240_ = v_tail_5248_;
goto _start;
}
else
{
lean_dec(v_tail_5248_);
return v___x_5249_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg___boxed(lean_object* v_x_5252_, lean_object* v_x_5253_, lean_object* v___y_5254_, lean_object* v___y_5255_, lean_object* v___y_5256_, lean_object* v___y_5257_, lean_object* v___y_5258_){
_start:
{
lean_object* v_res_5259_; 
v_res_5259_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_x_5252_, v_x_5253_, v___y_5254_, v___y_5255_, v___y_5256_, v___y_5257_);
lean_dec(v___y_5257_);
lean_dec_ref(v___y_5256_);
lean_dec(v___y_5255_);
lean_dec_ref(v___y_5254_);
return v_res_5259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys___redArg(lean_object* v_t_5260_, lean_object* v_keys_5261_, lean_object* v_a_5262_, lean_object* v_a_5263_, lean_object* v_a_5264_, lean_object* v_a_5265_){
_start:
{
lean_object* v___x_5267_; 
v___x_5267_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_t_5260_, v_keys_5261_, v_a_5262_, v_a_5263_, v_a_5264_, v_a_5265_);
return v___x_5267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys___redArg___boxed(lean_object* v_t_5268_, lean_object* v_keys_5269_, lean_object* v_a_5270_, lean_object* v_a_5271_, lean_object* v_a_5272_, lean_object* v_a_5273_, lean_object* v_a_5274_){
_start:
{
lean_object* v_res_5275_; 
v_res_5275_ = l_Lean_Meta_LazyDiscrTree_dropKeys___redArg(v_t_5268_, v_keys_5269_, v_a_5270_, v_a_5271_, v_a_5272_, v_a_5273_);
lean_dec(v_a_5273_);
lean_dec_ref(v_a_5272_);
lean_dec(v_a_5271_);
lean_dec_ref(v_a_5270_);
return v_res_5275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys(lean_object* v_00_u03b1_5276_, lean_object* v_t_5277_, lean_object* v_keys_5278_, lean_object* v_a_5279_, lean_object* v_a_5280_, lean_object* v_a_5281_, lean_object* v_a_5282_){
_start:
{
lean_object* v___x_5284_; 
v___x_5284_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_t_5277_, v_keys_5278_, v_a_5279_, v_a_5280_, v_a_5281_, v_a_5282_);
return v___x_5284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys___boxed(lean_object* v_00_u03b1_5285_, lean_object* v_t_5286_, lean_object* v_keys_5287_, lean_object* v_a_5288_, lean_object* v_a_5289_, lean_object* v_a_5290_, lean_object* v_a_5291_, lean_object* v_a_5292_){
_start:
{
lean_object* v_res_5293_; 
v_res_5293_ = l_Lean_Meta_LazyDiscrTree_dropKeys(v_00_u03b1_5285_, v_t_5286_, v_keys_5287_, v_a_5288_, v_a_5289_, v_a_5290_, v_a_5291_);
lean_dec(v_a_5291_);
lean_dec_ref(v_a_5290_);
lean_dec(v_a_5289_);
lean_dec_ref(v_a_5288_);
return v_res_5293_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0(lean_object* v_00_u03b1_5294_, lean_object* v_x_5295_, lean_object* v_x_5296_, lean_object* v___y_5297_, lean_object* v___y_5298_, lean_object* v___y_5299_, lean_object* v___y_5300_){
_start:
{
lean_object* v___x_5302_; 
v___x_5302_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_x_5295_, v_x_5296_, v___y_5297_, v___y_5298_, v___y_5299_, v___y_5300_);
return v___x_5302_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___boxed(lean_object* v_00_u03b1_5303_, lean_object* v_x_5304_, lean_object* v_x_5305_, lean_object* v___y_5306_, lean_object* v___y_5307_, lean_object* v___y_5308_, lean_object* v___y_5309_, lean_object* v___y_5310_){
_start:
{
lean_object* v_res_5311_; 
v_res_5311_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0(v_00_u03b1_5303_, v_x_5304_, v_x_5305_, v___y_5306_, v___y_5307_, v___y_5308_, v___y_5309_);
lean_dec(v___y_5309_);
lean_dec_ref(v___y_5308_);
lean_dec(v___y_5307_);
lean_dec_ref(v___y_5306_);
return v_res_5311_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(lean_object* v_as_5312_, size_t v_sz_5313_, size_t v_i_5314_, lean_object* v_b_5315_, lean_object* v___y_5316_, lean_object* v___y_5317_, lean_object* v___y_5318_, lean_object* v___y_5319_, lean_object* v___y_5320_){
_start:
{
uint8_t v___x_5322_; 
v___x_5322_ = lean_usize_dec_lt(v_i_5314_, v_sz_5313_);
if (v___x_5322_ == 0)
{
lean_object* v___x_5323_; 
v___x_5323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5323_, 0, v_b_5315_);
return v___x_5323_;
}
else
{
lean_object* v_a_5324_; lean_object* v___x_5325_; 
v_a_5324_ = lean_array_uget_borrowed(v_as_5312_, v_i_5314_);
v___x_5325_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(v_a_5324_, v_b_5315_, v___y_5316_, v___y_5317_, v___y_5318_, v___y_5319_, v___y_5320_);
if (lean_obj_tag(v___x_5325_) == 0)
{
lean_object* v_a_5326_; lean_object* v___x_5328_; uint8_t v_isShared_5329_; uint8_t v_isSharedCheck_5338_; 
v_a_5326_ = lean_ctor_get(v___x_5325_, 0);
v_isSharedCheck_5338_ = !lean_is_exclusive(v___x_5325_);
if (v_isSharedCheck_5338_ == 0)
{
v___x_5328_ = v___x_5325_;
v_isShared_5329_ = v_isSharedCheck_5338_;
goto v_resetjp_5327_;
}
else
{
lean_inc(v_a_5326_);
lean_dec(v___x_5325_);
v___x_5328_ = lean_box(0);
v_isShared_5329_ = v_isSharedCheck_5338_;
goto v_resetjp_5327_;
}
v_resetjp_5327_:
{
if (lean_obj_tag(v_a_5326_) == 0)
{
lean_object* v_a_5330_; lean_object* v___x_5332_; 
v_a_5330_ = lean_ctor_get(v_a_5326_, 0);
lean_inc(v_a_5330_);
lean_dec_ref_known(v_a_5326_, 1);
if (v_isShared_5329_ == 0)
{
lean_ctor_set(v___x_5328_, 0, v_a_5330_);
v___x_5332_ = v___x_5328_;
goto v_reusejp_5331_;
}
else
{
lean_object* v_reuseFailAlloc_5333_; 
v_reuseFailAlloc_5333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5333_, 0, v_a_5330_);
v___x_5332_ = v_reuseFailAlloc_5333_;
goto v_reusejp_5331_;
}
v_reusejp_5331_:
{
return v___x_5332_;
}
}
else
{
lean_object* v_a_5334_; size_t v___x_5335_; size_t v___x_5336_; 
lean_del_object(v___x_5328_);
v_a_5334_ = lean_ctor_get(v_a_5326_, 0);
lean_inc(v_a_5334_);
lean_dec_ref_known(v_a_5326_, 1);
v___x_5335_ = ((size_t)1ULL);
v___x_5336_ = lean_usize_add(v_i_5314_, v___x_5335_);
v_i_5314_ = v___x_5336_;
v_b_5315_ = v_a_5334_;
goto _start;
}
}
}
else
{
lean_object* v_a_5339_; lean_object* v___x_5341_; uint8_t v_isShared_5342_; uint8_t v_isSharedCheck_5346_; 
v_a_5339_ = lean_ctor_get(v___x_5325_, 0);
v_isSharedCheck_5346_ = !lean_is_exclusive(v___x_5325_);
if (v_isSharedCheck_5346_ == 0)
{
v___x_5341_ = v___x_5325_;
v_isShared_5342_ = v_isSharedCheck_5346_;
goto v_resetjp_5340_;
}
else
{
lean_inc(v_a_5339_);
lean_dec(v___x_5325_);
v___x_5341_ = lean_box(0);
v_isShared_5342_ = v_isSharedCheck_5346_;
goto v_resetjp_5340_;
}
v_resetjp_5340_:
{
lean_object* v___x_5344_; 
if (v_isShared_5342_ == 0)
{
v___x_5344_ = v___x_5341_;
goto v_reusejp_5343_;
}
else
{
lean_object* v_reuseFailAlloc_5345_; 
v_reuseFailAlloc_5345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5345_, 0, v_a_5339_);
v___x_5344_ = v_reuseFailAlloc_5345_;
goto v_reusejp_5343_;
}
v_reusejp_5343_:
{
return v___x_5344_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(lean_object* v_next_5347_, lean_object* v_a_5348_, lean_object* v_a_5349_, lean_object* v_a_5350_, lean_object* v_a_5351_, lean_object* v_a_5352_){
_start:
{
lean_object* v___x_5354_; uint8_t v___x_5355_; 
v___x_5354_ = lean_unsigned_to_nat(0u);
v___x_5355_ = lean_nat_dec_eq(v_next_5347_, v___x_5354_);
if (v___x_5355_ == 0)
{
lean_object* v___x_5356_; 
v___x_5356_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_next_5347_, v_a_5348_, v_a_5349_, v_a_5350_, v_a_5351_, v_a_5352_);
if (lean_obj_tag(v___x_5356_) == 0)
{
lean_object* v_a_5357_; lean_object* v_snd_5358_; lean_object* v_fst_5359_; lean_object* v_fst_5360_; lean_object* v_snd_5361_; lean_object* v___x_5362_; 
v_a_5357_ = lean_ctor_get(v___x_5356_, 0);
lean_inc(v_a_5357_);
lean_dec_ref_known(v___x_5356_, 1);
v_snd_5358_ = lean_ctor_get(v_a_5357_, 1);
lean_inc(v_snd_5358_);
v_fst_5359_ = lean_ctor_get(v_a_5357_, 0);
lean_inc(v_fst_5359_);
lean_dec(v_a_5357_);
v_fst_5360_ = lean_ctor_get(v_snd_5358_, 0);
lean_inc(v_fst_5360_);
v_snd_5361_ = lean_ctor_get(v_snd_5358_, 1);
lean_inc(v_snd_5361_);
lean_dec(v_snd_5358_);
v___x_5362_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_fst_5360_, v_a_5348_, v_a_5349_, v_a_5350_, v_a_5351_, v_a_5352_);
if (lean_obj_tag(v___x_5362_) == 0)
{
lean_object* v_a_5363_; lean_object* v_buckets_5364_; lean_object* v___x_5365_; size_t v_sz_5366_; size_t v___x_5367_; lean_object* v___x_5368_; 
v_a_5363_ = lean_ctor_get(v___x_5362_, 0);
lean_inc(v_a_5363_);
lean_dec_ref_known(v___x_5362_, 1);
v_buckets_5364_ = lean_ctor_get(v_snd_5361_, 1);
v___x_5365_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v_sz_5366_ = lean_array_size(v_buckets_5364_);
v___x_5367_ = ((size_t)0ULL);
v___x_5368_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(v_buckets_5364_, v_sz_5366_, v___x_5367_, v___x_5365_, v_a_5348_, v_a_5349_, v_a_5350_, v_a_5351_, v_a_5352_);
if (lean_obj_tag(v___x_5368_) == 0)
{
lean_object* v_a_5369_; lean_object* v___x_5371_; uint8_t v_isShared_5372_; uint8_t v_isSharedCheck_5382_; 
v_a_5369_ = lean_ctor_get(v___x_5368_, 0);
v_isSharedCheck_5382_ = !lean_is_exclusive(v___x_5368_);
if (v_isSharedCheck_5382_ == 0)
{
v___x_5371_ = v___x_5368_;
v_isShared_5372_ = v_isSharedCheck_5382_;
goto v_resetjp_5370_;
}
else
{
lean_inc(v_a_5369_);
lean_dec(v___x_5368_);
v___x_5371_ = lean_box(0);
v_isShared_5372_ = v_isSharedCheck_5382_;
goto v_resetjp_5370_;
}
v_resetjp_5370_:
{
lean_object* v___x_5373_; lean_object* v___x_5374_; lean_object* v___x_5375_; lean_object* v___x_5376_; lean_object* v___x_5377_; lean_object* v___x_5378_; lean_object* v___x_5380_; 
v___x_5373_ = lean_st_ref_take(v_a_5348_);
v___x_5374_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5374_, 0, v___x_5365_);
lean_ctor_set(v___x_5374_, 1, v_fst_5360_);
lean_ctor_set(v___x_5374_, 2, v_snd_5361_);
lean_ctor_set(v___x_5374_, 3, v___x_5365_);
v___x_5375_ = lean_array_set(v___x_5373_, v_next_5347_, v___x_5374_);
v___x_5376_ = lean_st_ref_put(v_a_5348_, v___x_5375_);
v___x_5377_ = l_Array_append___redArg(v_fst_5359_, v_a_5363_);
lean_dec(v_a_5363_);
v___x_5378_ = l_Array_append___redArg(v___x_5377_, v_a_5369_);
lean_dec(v_a_5369_);
if (v_isShared_5372_ == 0)
{
lean_ctor_set(v___x_5371_, 0, v___x_5378_);
v___x_5380_ = v___x_5371_;
goto v_reusejp_5379_;
}
else
{
lean_object* v_reuseFailAlloc_5381_; 
v_reuseFailAlloc_5381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5381_, 0, v___x_5378_);
v___x_5380_ = v_reuseFailAlloc_5381_;
goto v_reusejp_5379_;
}
v_reusejp_5379_:
{
return v___x_5380_;
}
}
}
else
{
lean_dec(v_a_5363_);
lean_dec(v_snd_5361_);
lean_dec(v_fst_5360_);
lean_dec(v_fst_5359_);
return v___x_5368_;
}
}
else
{
lean_dec(v_snd_5361_);
lean_dec(v_fst_5360_);
lean_dec(v_fst_5359_);
return v___x_5362_;
}
}
else
{
lean_object* v_a_5383_; lean_object* v___x_5385_; uint8_t v_isShared_5386_; uint8_t v_isSharedCheck_5390_; 
v_a_5383_ = lean_ctor_get(v___x_5356_, 0);
v_isSharedCheck_5390_ = !lean_is_exclusive(v___x_5356_);
if (v_isSharedCheck_5390_ == 0)
{
v___x_5385_ = v___x_5356_;
v_isShared_5386_ = v_isSharedCheck_5390_;
goto v_resetjp_5384_;
}
else
{
lean_inc(v_a_5383_);
lean_dec(v___x_5356_);
v___x_5385_ = lean_box(0);
v_isShared_5386_ = v_isSharedCheck_5390_;
goto v_resetjp_5384_;
}
v_resetjp_5384_:
{
lean_object* v___x_5388_; 
if (v_isShared_5386_ == 0)
{
v___x_5388_ = v___x_5385_;
goto v_reusejp_5387_;
}
else
{
lean_object* v_reuseFailAlloc_5389_; 
v_reuseFailAlloc_5389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5389_, 0, v_a_5383_);
v___x_5388_ = v_reuseFailAlloc_5389_;
goto v_reusejp_5387_;
}
v_reusejp_5387_:
{
return v___x_5388_;
}
}
}
}
else
{
lean_object* v___x_5391_; lean_object* v___x_5392_; 
v___x_5391_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___x_5392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5392_, 0, v___x_5391_);
return v___x_5392_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(lean_object* v_a_5393_, lean_object* v_a_5394_, lean_object* v___y_5395_, lean_object* v___y_5396_, lean_object* v___y_5397_, lean_object* v___y_5398_, lean_object* v___y_5399_){
_start:
{
if (lean_obj_tag(v_a_5393_) == 0)
{
lean_object* v___x_5401_; lean_object* v___x_5402_; 
v___x_5401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5401_, 0, v_a_5394_);
v___x_5402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5402_, 0, v___x_5401_);
return v___x_5402_;
}
else
{
lean_object* v_value_5403_; lean_object* v_tail_5404_; lean_object* v___x_5405_; 
v_value_5403_ = lean_ctor_get(v_a_5393_, 1);
v_tail_5404_ = lean_ctor_get(v_a_5393_, 2);
v___x_5405_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_value_5403_, v___y_5395_, v___y_5396_, v___y_5397_, v___y_5398_, v___y_5399_);
if (lean_obj_tag(v___x_5405_) == 0)
{
lean_object* v_a_5406_; lean_object* v___x_5407_; 
v_a_5406_ = lean_ctor_get(v___x_5405_, 0);
lean_inc(v_a_5406_);
lean_dec_ref_known(v___x_5405_, 1);
v___x_5407_ = l_Array_append___redArg(v_a_5394_, v_a_5406_);
lean_dec(v_a_5406_);
v_a_5393_ = v_tail_5404_;
v_a_5394_ = v___x_5407_;
goto _start;
}
else
{
lean_object* v_a_5409_; lean_object* v___x_5411_; uint8_t v_isShared_5412_; uint8_t v_isSharedCheck_5416_; 
lean_dec_ref(v_a_5394_);
v_a_5409_ = lean_ctor_get(v___x_5405_, 0);
v_isSharedCheck_5416_ = !lean_is_exclusive(v___x_5405_);
if (v_isSharedCheck_5416_ == 0)
{
v___x_5411_ = v___x_5405_;
v_isShared_5412_ = v_isSharedCheck_5416_;
goto v_resetjp_5410_;
}
else
{
lean_inc(v_a_5409_);
lean_dec(v___x_5405_);
v___x_5411_ = lean_box(0);
v_isShared_5412_ = v_isSharedCheck_5416_;
goto v_resetjp_5410_;
}
v_resetjp_5410_:
{
lean_object* v___x_5414_; 
if (v_isShared_5412_ == 0)
{
v___x_5414_ = v___x_5411_;
goto v_reusejp_5413_;
}
else
{
lean_object* v_reuseFailAlloc_5415_; 
v_reuseFailAlloc_5415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5415_, 0, v_a_5409_);
v___x_5414_ = v_reuseFailAlloc_5415_;
goto v_reusejp_5413_;
}
v_reusejp_5413_:
{
return v___x_5414_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg___boxed(lean_object* v_a_5417_, lean_object* v_a_5418_, lean_object* v___y_5419_, lean_object* v___y_5420_, lean_object* v___y_5421_, lean_object* v___y_5422_, lean_object* v___y_5423_, lean_object* v___y_5424_){
_start:
{
lean_object* v_res_5425_; 
v_res_5425_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(v_a_5417_, v_a_5418_, v___y_5419_, v___y_5420_, v___y_5421_, v___y_5422_, v___y_5423_);
lean_dec(v___y_5423_);
lean_dec_ref(v___y_5422_);
lean_dec(v___y_5421_);
lean_dec_ref(v___y_5420_);
lean_dec(v___y_5419_);
lean_dec(v_a_5417_);
return v_res_5425_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg___boxed(lean_object* v_as_5426_, lean_object* v_sz_5427_, lean_object* v_i_5428_, lean_object* v_b_5429_, lean_object* v___y_5430_, lean_object* v___y_5431_, lean_object* v___y_5432_, lean_object* v___y_5433_, lean_object* v___y_5434_, lean_object* v___y_5435_){
_start:
{
size_t v_sz_boxed_5436_; size_t v_i_boxed_5437_; lean_object* v_res_5438_; 
v_sz_boxed_5436_ = lean_unbox_usize(v_sz_5427_);
lean_dec(v_sz_5427_);
v_i_boxed_5437_ = lean_unbox_usize(v_i_5428_);
lean_dec(v_i_5428_);
v_res_5438_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(v_as_5426_, v_sz_boxed_5436_, v_i_boxed_5437_, v_b_5429_, v___y_5430_, v___y_5431_, v___y_5432_, v___y_5433_, v___y_5434_);
lean_dec(v___y_5434_);
lean_dec_ref(v___y_5433_);
lean_dec(v___y_5432_);
lean_dec_ref(v___y_5431_);
lean_dec(v___y_5430_);
lean_dec_ref(v_as_5426_);
return v_res_5438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg___boxed(lean_object* v_next_5439_, lean_object* v_a_5440_, lean_object* v_a_5441_, lean_object* v_a_5442_, lean_object* v_a_5443_, lean_object* v_a_5444_, lean_object* v_a_5445_){
_start:
{
lean_object* v_res_5446_; 
v_res_5446_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_next_5439_, v_a_5440_, v_a_5441_, v_a_5442_, v_a_5443_, v_a_5444_);
lean_dec(v_a_5444_);
lean_dec_ref(v_a_5443_);
lean_dec(v_a_5442_);
lean_dec_ref(v_a_5441_);
lean_dec(v_a_5440_);
lean_dec(v_next_5439_);
return v_res_5446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux(lean_object* v_00_u03b1_5447_, lean_object* v_next_5448_, lean_object* v_a_5449_, lean_object* v_a_5450_, lean_object* v_a_5451_, lean_object* v_a_5452_, lean_object* v_a_5453_){
_start:
{
lean_object* v___x_5455_; 
v___x_5455_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_next_5448_, v_a_5449_, v_a_5450_, v_a_5451_, v_a_5452_, v_a_5453_);
return v___x_5455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___boxed(lean_object* v_00_u03b1_5456_, lean_object* v_next_5457_, lean_object* v_a_5458_, lean_object* v_a_5459_, lean_object* v_a_5460_, lean_object* v_a_5461_, lean_object* v_a_5462_, lean_object* v_a_5463_){
_start:
{
lean_object* v_res_5464_; 
v_res_5464_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux(v_00_u03b1_5456_, v_next_5457_, v_a_5458_, v_a_5459_, v_a_5460_, v_a_5461_, v_a_5462_);
lean_dec(v_a_5462_);
lean_dec_ref(v_a_5461_);
lean_dec(v_a_5460_);
lean_dec_ref(v_a_5459_);
lean_dec(v_a_5458_);
lean_dec(v_next_5457_);
return v_res_5464_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0(lean_object* v_00_u03b1_5465_, lean_object* v_a_5466_, lean_object* v_a_5467_, lean_object* v___y_5468_, lean_object* v___y_5469_, lean_object* v___y_5470_, lean_object* v___y_5471_, lean_object* v___y_5472_){
_start:
{
lean_object* v___x_5474_; 
v___x_5474_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(v_a_5466_, v_a_5467_, v___y_5468_, v___y_5469_, v___y_5470_, v___y_5471_, v___y_5472_);
return v___x_5474_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___boxed(lean_object* v_00_u03b1_5475_, lean_object* v_a_5476_, lean_object* v_a_5477_, lean_object* v___y_5478_, lean_object* v___y_5479_, lean_object* v___y_5480_, lean_object* v___y_5481_, lean_object* v___y_5482_, lean_object* v___y_5483_){
_start:
{
lean_object* v_res_5484_; 
v_res_5484_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0(v_00_u03b1_5475_, v_a_5476_, v_a_5477_, v___y_5478_, v___y_5479_, v___y_5480_, v___y_5481_, v___y_5482_);
lean_dec(v___y_5482_);
lean_dec_ref(v___y_5481_);
lean_dec(v___y_5480_);
lean_dec_ref(v___y_5479_);
lean_dec(v___y_5478_);
lean_dec(v_a_5476_);
return v_res_5484_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1(lean_object* v_00_u03b1_5485_, lean_object* v_as_5486_, size_t v_sz_5487_, size_t v_i_5488_, lean_object* v_b_5489_, lean_object* v___y_5490_, lean_object* v___y_5491_, lean_object* v___y_5492_, lean_object* v___y_5493_, lean_object* v___y_5494_){
_start:
{
lean_object* v___x_5496_; 
v___x_5496_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(v_as_5486_, v_sz_5487_, v_i_5488_, v_b_5489_, v___y_5490_, v___y_5491_, v___y_5492_, v___y_5493_, v___y_5494_);
return v___x_5496_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___boxed(lean_object* v_00_u03b1_5497_, lean_object* v_as_5498_, lean_object* v_sz_5499_, lean_object* v_i_5500_, lean_object* v_b_5501_, lean_object* v___y_5502_, lean_object* v___y_5503_, lean_object* v___y_5504_, lean_object* v___y_5505_, lean_object* v___y_5506_, lean_object* v___y_5507_){
_start:
{
size_t v_sz_boxed_5508_; size_t v_i_boxed_5509_; lean_object* v_res_5510_; 
v_sz_boxed_5508_ = lean_unbox_usize(v_sz_5499_);
lean_dec(v_sz_5499_);
v_i_boxed_5509_ = lean_unbox_usize(v_i_5500_);
lean_dec(v_i_5500_);
v_res_5510_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1(v_00_u03b1_5497_, v_as_5498_, v_sz_boxed_5508_, v_i_boxed_5509_, v_b_5501_, v___y_5502_, v___y_5503_, v___y_5504_, v___y_5505_, v___y_5506_);
lean_dec(v___y_5506_);
lean_dec_ref(v___y_5505_);
lean_dec(v___y_5504_);
lean_dec_ref(v___y_5503_);
lean_dec(v___y_5502_);
lean_dec_ref(v_as_5498_);
return v_res_5510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg(lean_object* v_next_5511_, lean_object* v_rest_5512_, lean_object* v_a_5513_, lean_object* v_a_5514_, lean_object* v_a_5515_, lean_object* v_a_5516_, lean_object* v_a_5517_){
_start:
{
lean_object* v___x_5519_; uint8_t v___x_5520_; 
v___x_5519_ = lean_unsigned_to_nat(0u);
v___x_5520_ = lean_nat_dec_eq(v_next_5511_, v___x_5519_);
if (v___x_5520_ == 0)
{
lean_object* v___x_5521_; 
v___x_5521_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_next_5511_, v_a_5513_, v_a_5514_, v_a_5515_, v_a_5516_, v_a_5517_);
if (lean_obj_tag(v___x_5521_) == 0)
{
lean_object* v_a_5522_; lean_object* v_snd_5523_; 
v_a_5522_ = lean_ctor_get(v___x_5521_, 0);
lean_inc(v_a_5522_);
lean_dec_ref_known(v___x_5521_, 1);
v_snd_5523_ = lean_ctor_get(v_a_5522_, 1);
lean_inc(v_snd_5523_);
lean_dec(v_a_5522_);
if (lean_obj_tag(v_rest_5512_) == 0)
{
lean_object* v___x_5524_; 
lean_dec(v_snd_5523_);
v___x_5524_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_next_5511_, v_a_5513_, v_a_5514_, v_a_5515_, v_a_5516_, v_a_5517_);
lean_dec(v_next_5511_);
return v___x_5524_;
}
else
{
lean_object* v_fst_5525_; lean_object* v_snd_5526_; lean_object* v_head_5527_; lean_object* v_tail_5528_; lean_object* v___x_5529_; uint8_t v___x_5530_; 
lean_dec(v_next_5511_);
v_fst_5525_ = lean_ctor_get(v_snd_5523_, 0);
lean_inc(v_fst_5525_);
v_snd_5526_ = lean_ctor_get(v_snd_5523_, 1);
lean_inc(v_snd_5526_);
lean_dec(v_snd_5523_);
v_head_5527_ = lean_ctor_get(v_rest_5512_, 0);
v_tail_5528_ = lean_ctor_get(v_rest_5512_, 1);
v___x_5529_ = lean_box(3);
v___x_5530_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_head_5527_, v___x_5529_);
if (v___x_5530_ == 0)
{
lean_object* v___x_5531_; 
lean_dec(v_fst_5525_);
v___x_5531_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_snd_5526_, v_head_5527_, v___x_5519_);
lean_dec(v_snd_5526_);
v_next_5511_ = v___x_5531_;
v_rest_5512_ = v_tail_5528_;
goto _start;
}
else
{
lean_dec(v_snd_5526_);
v_next_5511_ = v_fst_5525_;
v_rest_5512_ = v_tail_5528_;
goto _start;
}
}
}
else
{
lean_object* v_a_5534_; lean_object* v___x_5536_; uint8_t v_isShared_5537_; uint8_t v_isSharedCheck_5541_; 
lean_dec(v_next_5511_);
v_a_5534_ = lean_ctor_get(v___x_5521_, 0);
v_isSharedCheck_5541_ = !lean_is_exclusive(v___x_5521_);
if (v_isSharedCheck_5541_ == 0)
{
v___x_5536_ = v___x_5521_;
v_isShared_5537_ = v_isSharedCheck_5541_;
goto v_resetjp_5535_;
}
else
{
lean_inc(v_a_5534_);
lean_dec(v___x_5521_);
v___x_5536_ = lean_box(0);
v_isShared_5537_ = v_isSharedCheck_5541_;
goto v_resetjp_5535_;
}
v_resetjp_5535_:
{
lean_object* v___x_5539_; 
if (v_isShared_5537_ == 0)
{
v___x_5539_ = v___x_5536_;
goto v_reusejp_5538_;
}
else
{
lean_object* v_reuseFailAlloc_5540_; 
v_reuseFailAlloc_5540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5540_, 0, v_a_5534_);
v___x_5539_ = v_reuseFailAlloc_5540_;
goto v_reusejp_5538_;
}
v_reusejp_5538_:
{
return v___x_5539_;
}
}
}
}
else
{
lean_object* v___x_5542_; lean_object* v___x_5543_; 
lean_dec(v_next_5511_);
v___x_5542_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___x_5543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5543_, 0, v___x_5542_);
return v___x_5543_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg___boxed(lean_object* v_next_5544_, lean_object* v_rest_5545_, lean_object* v_a_5546_, lean_object* v_a_5547_, lean_object* v_a_5548_, lean_object* v_a_5549_, lean_object* v_a_5550_, lean_object* v_a_5551_){
_start:
{
lean_object* v_res_5552_; 
v_res_5552_ = l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg(v_next_5544_, v_rest_5545_, v_a_5546_, v_a_5547_, v_a_5548_, v_a_5549_, v_a_5550_);
lean_dec(v_a_5550_);
lean_dec_ref(v_a_5549_);
lean_dec(v_a_5548_);
lean_dec_ref(v_a_5547_);
lean_dec(v_a_5546_);
lean_dec(v_rest_5545_);
return v_res_5552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux(lean_object* v_00_u03b1_5553_, lean_object* v_next_5554_, lean_object* v_rest_5555_, lean_object* v_a_5556_, lean_object* v_a_5557_, lean_object* v_a_5558_, lean_object* v_a_5559_, lean_object* v_a_5560_){
_start:
{
lean_object* v___x_5562_; 
v___x_5562_ = l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg(v_next_5554_, v_rest_5555_, v_a_5556_, v_a_5557_, v_a_5558_, v_a_5559_, v_a_5560_);
return v___x_5562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux___boxed(lean_object* v_00_u03b1_5563_, lean_object* v_next_5564_, lean_object* v_rest_5565_, lean_object* v_a_5566_, lean_object* v_a_5567_, lean_object* v_a_5568_, lean_object* v_a_5569_, lean_object* v_a_5570_, lean_object* v_a_5571_){
_start:
{
lean_object* v_res_5572_; 
v_res_5572_ = l_Lean_Meta_LazyDiscrTree_extractKeyAux(v_00_u03b1_5563_, v_next_5564_, v_rest_5565_, v_a_5566_, v_a_5567_, v_a_5568_, v_a_5569_, v_a_5570_);
lean_dec(v_a_5570_);
lean_dec_ref(v_a_5569_);
lean_dec(v_a_5568_);
lean_dec_ref(v_a_5567_);
lean_dec(v_a_5566_);
lean_dec(v_rest_5565_);
return v_res_5572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey___redArg(lean_object* v_t_5573_, lean_object* v_path_5574_, lean_object* v_a_5575_, lean_object* v_a_5576_, lean_object* v_a_5577_, lean_object* v_a_5578_){
_start:
{
if (lean_obj_tag(v_path_5574_) == 0)
{
lean_object* v___x_5580_; lean_object* v___x_5581_; lean_object* v___x_5582_; 
v___x_5580_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___x_5581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5581_, 0, v___x_5580_);
lean_ctor_set(v___x_5581_, 1, v_t_5573_);
v___x_5582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5582_, 0, v___x_5581_);
return v___x_5582_;
}
else
{
lean_object* v_head_5583_; lean_object* v_tail_5584_; lean_object* v_roots_5585_; lean_object* v___x_5586_; lean_object* v_idx_5587_; lean_object* v___x_5588_; lean_object* v___x_5589_; 
v_head_5583_ = lean_ctor_get(v_path_5574_, 0);
lean_inc(v_head_5583_);
v_tail_5584_ = lean_ctor_get(v_path_5574_, 1);
lean_inc(v_tail_5584_);
lean_dec_ref_known(v_path_5574_, 2);
v_roots_5585_ = lean_ctor_get(v_t_5573_, 1);
v___x_5586_ = lean_unsigned_to_nat(0u);
v_idx_5587_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_roots_5585_, v_head_5583_, v___x_5586_);
lean_dec(v_head_5583_);
v___x_5588_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_extractKeyAux___boxed), 9, 3);
lean_closure_set(v___x_5588_, 0, lean_box(0));
lean_closure_set(v___x_5588_, 1, v_idx_5587_);
lean_closure_set(v___x_5588_, 2, v_tail_5584_);
v___x_5589_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_t_5573_, v___x_5588_, v_a_5575_, v_a_5576_, v_a_5577_, v_a_5578_);
return v___x_5589_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey___redArg___boxed(lean_object* v_t_5590_, lean_object* v_path_5591_, lean_object* v_a_5592_, lean_object* v_a_5593_, lean_object* v_a_5594_, lean_object* v_a_5595_, lean_object* v_a_5596_){
_start:
{
lean_object* v_res_5597_; 
v_res_5597_ = l_Lean_Meta_LazyDiscrTree_extractKey___redArg(v_t_5590_, v_path_5591_, v_a_5592_, v_a_5593_, v_a_5594_, v_a_5595_);
lean_dec(v_a_5595_);
lean_dec_ref(v_a_5594_);
lean_dec(v_a_5593_);
lean_dec_ref(v_a_5592_);
return v_res_5597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey(lean_object* v_00_u03b1_5598_, lean_object* v_t_5599_, lean_object* v_path_5600_, lean_object* v_a_5601_, lean_object* v_a_5602_, lean_object* v_a_5603_, lean_object* v_a_5604_){
_start:
{
lean_object* v___x_5606_; 
v___x_5606_ = l_Lean_Meta_LazyDiscrTree_extractKey___redArg(v_t_5599_, v_path_5600_, v_a_5601_, v_a_5602_, v_a_5603_, v_a_5604_);
return v___x_5606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey___boxed(lean_object* v_00_u03b1_5607_, lean_object* v_t_5608_, lean_object* v_path_5609_, lean_object* v_a_5610_, lean_object* v_a_5611_, lean_object* v_a_5612_, lean_object* v_a_5613_, lean_object* v_a_5614_){
_start:
{
lean_object* v_res_5615_; 
v_res_5615_ = l_Lean_Meta_LazyDiscrTree_extractKey(v_00_u03b1_5607_, v_t_5608_, v_path_5609_, v_a_5610_, v_a_5611_, v_a_5612_, v_a_5613_);
lean_dec(v_a_5613_);
lean_dec_ref(v_a_5612_);
lean_dec(v_a_5611_);
lean_dec_ref(v_a_5610_);
return v_res_5615_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(lean_object* v_as_x27_5616_, lean_object* v_b_5617_, lean_object* v___y_5618_, lean_object* v___y_5619_, lean_object* v___y_5620_, lean_object* v___y_5621_){
_start:
{
if (lean_obj_tag(v_as_x27_5616_) == 0)
{
lean_object* v___x_5623_; 
v___x_5623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5623_, 0, v_b_5617_);
return v___x_5623_;
}
else
{
lean_object* v_head_5624_; lean_object* v_tail_5625_; lean_object* v_fst_5626_; lean_object* v_snd_5627_; lean_object* v___x_5628_; 
v_head_5624_ = lean_ctor_get(v_as_x27_5616_, 0);
v_tail_5625_ = lean_ctor_get(v_as_x27_5616_, 1);
v_fst_5626_ = lean_ctor_get(v_b_5617_, 0);
lean_inc(v_fst_5626_);
v_snd_5627_ = lean_ctor_get(v_b_5617_, 1);
lean_inc(v_snd_5627_);
lean_dec_ref(v_b_5617_);
lean_inc(v_head_5624_);
v___x_5628_ = l_Lean_Meta_LazyDiscrTree_extractKey___redArg(v_snd_5627_, v_head_5624_, v___y_5618_, v___y_5619_, v___y_5620_, v___y_5621_);
if (lean_obj_tag(v___x_5628_) == 0)
{
lean_object* v_a_5629_; lean_object* v_fst_5630_; lean_object* v_snd_5631_; lean_object* v___x_5633_; uint8_t v_isShared_5634_; uint8_t v_isSharedCheck_5640_; 
v_a_5629_ = lean_ctor_get(v___x_5628_, 0);
lean_inc(v_a_5629_);
lean_dec_ref_known(v___x_5628_, 1);
v_fst_5630_ = lean_ctor_get(v_a_5629_, 0);
v_snd_5631_ = lean_ctor_get(v_a_5629_, 1);
v_isSharedCheck_5640_ = !lean_is_exclusive(v_a_5629_);
if (v_isSharedCheck_5640_ == 0)
{
v___x_5633_ = v_a_5629_;
v_isShared_5634_ = v_isSharedCheck_5640_;
goto v_resetjp_5632_;
}
else
{
lean_inc(v_snd_5631_);
lean_inc(v_fst_5630_);
lean_dec(v_a_5629_);
v___x_5633_ = lean_box(0);
v_isShared_5634_ = v_isSharedCheck_5640_;
goto v_resetjp_5632_;
}
v_resetjp_5632_:
{
lean_object* v___x_5635_; lean_object* v___x_5637_; 
v___x_5635_ = l_Array_append___redArg(v_fst_5626_, v_fst_5630_);
lean_dec(v_fst_5630_);
if (v_isShared_5634_ == 0)
{
lean_ctor_set(v___x_5633_, 0, v___x_5635_);
v___x_5637_ = v___x_5633_;
goto v_reusejp_5636_;
}
else
{
lean_object* v_reuseFailAlloc_5639_; 
v_reuseFailAlloc_5639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5639_, 0, v___x_5635_);
lean_ctor_set(v_reuseFailAlloc_5639_, 1, v_snd_5631_);
v___x_5637_ = v_reuseFailAlloc_5639_;
goto v_reusejp_5636_;
}
v_reusejp_5636_:
{
v_as_x27_5616_ = v_tail_5625_;
v_b_5617_ = v___x_5637_;
goto _start;
}
}
}
else
{
lean_dec(v_fst_5626_);
return v___x_5628_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg___boxed(lean_object* v_as_x27_5641_, lean_object* v_b_5642_, lean_object* v___y_5643_, lean_object* v___y_5644_, lean_object* v___y_5645_, lean_object* v___y_5646_, lean_object* v___y_5647_){
_start:
{
lean_object* v_res_5648_; 
v_res_5648_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(v_as_x27_5641_, v_b_5642_, v___y_5643_, v___y_5644_, v___y_5645_, v___y_5646_);
lean_dec(v___y_5646_);
lean_dec_ref(v___y_5645_);
lean_dec(v___y_5644_);
lean_dec_ref(v___y_5643_);
lean_dec(v_as_x27_5641_);
return v_res_5648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(lean_object* v_t_5649_, lean_object* v_keys_5650_, lean_object* v_a_5651_, lean_object* v_a_5652_, lean_object* v_a_5653_, lean_object* v_a_5654_){
_start:
{
lean_object* v_allExtracted_5656_; lean_object* v___x_5657_; lean_object* v___x_5658_; 
v_allExtracted_5656_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___x_5657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5657_, 0, v_allExtracted_5656_);
lean_ctor_set(v___x_5657_, 1, v_t_5649_);
v___x_5658_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(v_keys_5650_, v___x_5657_, v_a_5651_, v_a_5652_, v_a_5653_, v_a_5654_);
if (lean_obj_tag(v___x_5658_) == 0)
{
lean_object* v_a_5659_; lean_object* v___x_5661_; uint8_t v_isShared_5662_; uint8_t v_isSharedCheck_5675_; 
v_a_5659_ = lean_ctor_get(v___x_5658_, 0);
v_isSharedCheck_5675_ = !lean_is_exclusive(v___x_5658_);
if (v_isSharedCheck_5675_ == 0)
{
v___x_5661_ = v___x_5658_;
v_isShared_5662_ = v_isSharedCheck_5675_;
goto v_resetjp_5660_;
}
else
{
lean_inc(v_a_5659_);
lean_dec(v___x_5658_);
v___x_5661_ = lean_box(0);
v_isShared_5662_ = v_isSharedCheck_5675_;
goto v_resetjp_5660_;
}
v_resetjp_5660_:
{
lean_object* v_fst_5663_; lean_object* v_snd_5664_; lean_object* v___x_5666_; uint8_t v_isShared_5667_; uint8_t v_isSharedCheck_5674_; 
v_fst_5663_ = lean_ctor_get(v_a_5659_, 0);
v_snd_5664_ = lean_ctor_get(v_a_5659_, 1);
v_isSharedCheck_5674_ = !lean_is_exclusive(v_a_5659_);
if (v_isSharedCheck_5674_ == 0)
{
v___x_5666_ = v_a_5659_;
v_isShared_5667_ = v_isSharedCheck_5674_;
goto v_resetjp_5665_;
}
else
{
lean_inc(v_snd_5664_);
lean_inc(v_fst_5663_);
lean_dec(v_a_5659_);
v___x_5666_ = lean_box(0);
v_isShared_5667_ = v_isSharedCheck_5674_;
goto v_resetjp_5665_;
}
v_resetjp_5665_:
{
lean_object* v___x_5669_; 
if (v_isShared_5667_ == 0)
{
v___x_5669_ = v___x_5666_;
goto v_reusejp_5668_;
}
else
{
lean_object* v_reuseFailAlloc_5673_; 
v_reuseFailAlloc_5673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5673_, 0, v_fst_5663_);
lean_ctor_set(v_reuseFailAlloc_5673_, 1, v_snd_5664_);
v___x_5669_ = v_reuseFailAlloc_5673_;
goto v_reusejp_5668_;
}
v_reusejp_5668_:
{
lean_object* v___x_5671_; 
if (v_isShared_5662_ == 0)
{
lean_ctor_set(v___x_5661_, 0, v___x_5669_);
v___x_5671_ = v___x_5661_;
goto v_reusejp_5670_;
}
else
{
lean_object* v_reuseFailAlloc_5672_; 
v_reuseFailAlloc_5672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5672_, 0, v___x_5669_);
v___x_5671_ = v_reuseFailAlloc_5672_;
goto v_reusejp_5670_;
}
v_reusejp_5670_:
{
return v___x_5671_;
}
}
}
}
}
else
{
return v___x_5658_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys___redArg___boxed(lean_object* v_t_5676_, lean_object* v_keys_5677_, lean_object* v_a_5678_, lean_object* v_a_5679_, lean_object* v_a_5680_, lean_object* v_a_5681_, lean_object* v_a_5682_){
_start:
{
lean_object* v_res_5683_; 
v_res_5683_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_t_5676_, v_keys_5677_, v_a_5678_, v_a_5679_, v_a_5680_, v_a_5681_);
lean_dec(v_a_5681_);
lean_dec_ref(v_a_5680_);
lean_dec(v_a_5679_);
lean_dec_ref(v_a_5678_);
lean_dec(v_keys_5677_);
return v_res_5683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys(lean_object* v_00_u03b1_5684_, lean_object* v_t_5685_, lean_object* v_keys_5686_, lean_object* v_a_5687_, lean_object* v_a_5688_, lean_object* v_a_5689_, lean_object* v_a_5690_){
_start:
{
lean_object* v___x_5692_; 
v___x_5692_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_t_5685_, v_keys_5686_, v_a_5687_, v_a_5688_, v_a_5689_, v_a_5690_);
return v___x_5692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys___boxed(lean_object* v_00_u03b1_5693_, lean_object* v_t_5694_, lean_object* v_keys_5695_, lean_object* v_a_5696_, lean_object* v_a_5697_, lean_object* v_a_5698_, lean_object* v_a_5699_, lean_object* v_a_5700_){
_start:
{
lean_object* v_res_5701_; 
v_res_5701_ = l_Lean_Meta_LazyDiscrTree_extractKeys(v_00_u03b1_5693_, v_t_5694_, v_keys_5695_, v_a_5696_, v_a_5697_, v_a_5698_, v_a_5699_);
lean_dec(v_a_5699_);
lean_dec_ref(v_a_5698_);
lean_dec(v_a_5697_);
lean_dec_ref(v_a_5696_);
lean_dec(v_keys_5695_);
return v_res_5701_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0(lean_object* v_00_u03b1_5702_, lean_object* v_as_5703_, lean_object* v_as_x27_5704_, lean_object* v_b_5705_, lean_object* v_a_5706_, lean_object* v___y_5707_, lean_object* v___y_5708_, lean_object* v___y_5709_, lean_object* v___y_5710_){
_start:
{
lean_object* v___x_5712_; 
v___x_5712_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(v_as_x27_5704_, v_b_5705_, v___y_5707_, v___y_5708_, v___y_5709_, v___y_5710_);
return v___x_5712_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___boxed(lean_object* v_00_u03b1_5713_, lean_object* v_as_5714_, lean_object* v_as_x27_5715_, lean_object* v_b_5716_, lean_object* v_a_5717_, lean_object* v___y_5718_, lean_object* v___y_5719_, lean_object* v___y_5720_, lean_object* v___y_5721_, lean_object* v___y_5722_){
_start:
{
lean_object* v_res_5723_; 
v_res_5723_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0(v_00_u03b1_5713_, v_as_5714_, v_as_x27_5715_, v_b_5716_, v_a_5717_, v___y_5718_, v___y_5719_, v___y_5720_, v___y_5721_);
lean_dec(v___y_5721_);
lean_dec_ref(v___y_5720_);
lean_dec(v___y_5719_);
lean_dec_ref(v___y_5718_);
lean_dec(v_as_x27_5715_);
lean_dec(v_as_5714_);
return v_res_5723_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1(void){
_start:
{
lean_object* v___x_5725_; lean_object* v___x_5726_; 
v___x_5725_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__0));
v___x_5726_ = l_Lean_stringToMessageData(v___x_5725_);
return v___x_5726_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3(void){
_start:
{
lean_object* v___x_5728_; lean_object* v___x_5729_; 
v___x_5728_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__2));
v___x_5729_ = l_Lean_stringToMessageData(v___x_5728_);
return v___x_5729_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5(void){
_start:
{
lean_object* v___x_5731_; lean_object* v___x_5732_; 
v___x_5731_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__4));
v___x_5732_ = l_Lean_stringToMessageData(v___x_5731_);
return v___x_5732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg(lean_object* v_inst_5733_, lean_object* v_inst_5734_, lean_object* v_inst_5735_, lean_object* v_inst_5736_, lean_object* v_f_5737_){
_start:
{
lean_object* v_module_5738_; lean_object* v_const_5739_; lean_object* v_exception_5740_; lean_object* v___x_5741_; lean_object* v___x_5742_; lean_object* v___x_5743_; lean_object* v___x_5744_; lean_object* v___x_5745_; lean_object* v___x_5746_; lean_object* v___x_5747_; lean_object* v___x_5748_; lean_object* v___x_5749_; lean_object* v___x_5750_; lean_object* v___x_5751_; lean_object* v___x_5752_; 
v_module_5738_ = lean_ctor_get(v_f_5737_, 0);
lean_inc(v_module_5738_);
v_const_5739_ = lean_ctor_get(v_f_5737_, 1);
lean_inc(v_const_5739_);
v_exception_5740_ = lean_ctor_get(v_f_5737_, 2);
lean_inc_ref(v_exception_5740_);
lean_dec_ref(v_f_5737_);
v___x_5741_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1);
v___x_5742_ = l_Lean_MessageData_ofName(v_const_5739_);
v___x_5743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5743_, 0, v___x_5741_);
lean_ctor_set(v___x_5743_, 1, v___x_5742_);
v___x_5744_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3);
v___x_5745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5745_, 0, v___x_5743_);
lean_ctor_set(v___x_5745_, 1, v___x_5744_);
v___x_5746_ = l_Lean_MessageData_ofName(v_module_5738_);
v___x_5747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5747_, 0, v___x_5745_);
lean_ctor_set(v___x_5747_, 1, v___x_5746_);
v___x_5748_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5);
v___x_5749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5749_, 0, v___x_5747_);
lean_ctor_set(v___x_5749_, 1, v___x_5748_);
v___x_5750_ = l_Lean_Exception_toMessageData(v_exception_5740_);
v___x_5751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5751_, 0, v___x_5749_);
lean_ctor_set(v___x_5751_, 1, v___x_5750_);
v___x_5752_ = l_Lean_logError___redArg(v_inst_5733_, v_inst_5734_, v_inst_5735_, v_inst_5736_, v___x_5751_);
return v___x_5752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure(lean_object* v_m_5753_, lean_object* v_inst_5754_, lean_object* v_inst_5755_, lean_object* v_inst_5756_, lean_object* v_inst_5757_, lean_object* v_f_5758_){
_start:
{
lean_object* v___x_5759_; 
v___x_5759_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg(v_inst_5754_, v_inst_5755_, v_inst_5756_, v_inst_5757_, v_f_5758_);
return v___x_5759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__0(lean_object* v_tasks_5760_, lean_object* v_toPure_5761_, lean_object* v_t_5762_){
_start:
{
lean_object* v___x_5763_; lean_object* v___x_5764_; 
v___x_5763_ = lean_array_push(v_tasks_5760_, v_t_5762_);
v___x_5764_ = lean_apply_2(v_toPure_5761_, lean_box(0), v___x_5763_);
return v___x_5764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(lean_object* v_inst_5765_, lean_object* v_inst_5766_, lean_object* v_cctx_5767_, lean_object* v_env_5768_, lean_object* v_act_5769_, lean_object* v_constantsPerTask_5770_, lean_object* v_n_5771_, lean_object* v_ngen_5772_, lean_object* v_tasks_5773_, lean_object* v_start_5774_, lean_object* v_cnt_5775_, lean_object* v_idx_5776_){
_start:
{
lean_object* v___x_5777_; lean_object* v_toApplicative_5778_; lean_object* v_moduleData_5779_; lean_object* v_toBind_5780_; lean_object* v_toPure_5781_; lean_object* v___x_5782_; uint8_t v___x_5783_; 
v___x_5777_ = l_Lean_Environment_header(v_env_5768_);
v_toApplicative_5778_ = lean_ctor_get(v_inst_5765_, 0);
v_moduleData_5779_ = lean_ctor_get(v___x_5777_, 6);
lean_inc_ref(v_moduleData_5779_);
lean_dec_ref(v___x_5777_);
v_toBind_5780_ = lean_ctor_get(v_inst_5765_, 1);
v_toPure_5781_ = lean_ctor_get(v_toApplicative_5778_, 1);
v___x_5782_ = lean_array_get_size(v_moduleData_5779_);
v___x_5783_ = lean_nat_dec_lt(v_idx_5776_, v___x_5782_);
if (v___x_5783_ == 0)
{
uint8_t v___x_5784_; 
lean_inc(v_toPure_5781_);
lean_inc(v_toBind_5780_);
lean_dec_ref(v_moduleData_5779_);
lean_dec(v_idx_5776_);
lean_dec(v_cnt_5775_);
lean_dec(v_constantsPerTask_5770_);
lean_dec_ref(v_inst_5765_);
v___x_5784_ = lean_nat_dec_lt(v_start_5774_, v_n_5771_);
if (v___x_5784_ == 0)
{
lean_object* v___x_5785_; 
lean_dec(v_toBind_5780_);
lean_dec(v_start_5774_);
lean_dec_ref(v_ngen_5772_);
lean_dec(v_n_5771_);
lean_dec_ref(v_act_5769_);
lean_dec_ref(v_env_5768_);
lean_dec_ref(v_cctx_5767_);
lean_dec(v_inst_5766_);
v___x_5785_ = lean_apply_2(v_toPure_5781_, lean_box(0), v_tasks_5773_);
return v___x_5785_;
}
else
{
lean_object* v_namePrefix_5786_; lean_object* v_idx_5787_; lean_object* v___x_5789_; uint8_t v_isShared_5790_; uint8_t v_isSharedCheck_5802_; 
v_namePrefix_5786_ = lean_ctor_get(v_ngen_5772_, 0);
v_idx_5787_ = lean_ctor_get(v_ngen_5772_, 1);
v_isSharedCheck_5802_ = !lean_is_exclusive(v_ngen_5772_);
if (v_isSharedCheck_5802_ == 0)
{
v___x_5789_ = v_ngen_5772_;
v_isShared_5790_ = v_isSharedCheck_5802_;
goto v_resetjp_5788_;
}
else
{
lean_inc(v_idx_5787_);
lean_inc(v_namePrefix_5786_);
lean_dec(v_ngen_5772_);
v___x_5789_ = lean_box(0);
v_isShared_5790_ = v_isSharedCheck_5802_;
goto v_resetjp_5788_;
}
v_resetjp_5788_:
{
lean_object* v___f_5791_; lean_object* v___x_5792_; lean_object* v___x_5793_; lean_object* v___x_5795_; 
v___f_5791_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5791_, 0, v_tasks_5773_);
lean_closure_set(v___f_5791_, 1, v_toPure_5781_);
v___x_5792_ = l_Lean_Name_num___override(v_namePrefix_5786_, v_idx_5787_);
v___x_5793_ = lean_unsigned_to_nat(1u);
if (v_isShared_5790_ == 0)
{
lean_ctor_set(v___x_5789_, 1, v___x_5793_);
lean_ctor_set(v___x_5789_, 0, v___x_5792_);
v___x_5795_ = v___x_5789_;
goto v_reusejp_5794_;
}
else
{
lean_object* v_reuseFailAlloc_5801_; 
v_reuseFailAlloc_5801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5801_, 0, v___x_5792_);
lean_ctor_set(v_reuseFailAlloc_5801_, 1, v___x_5793_);
v___x_5795_ = v_reuseFailAlloc_5801_;
goto v_reusejp_5794_;
}
v_reusejp_5794_:
{
lean_object* v___x_5796_; lean_object* v___x_5797_; lean_object* v___x_5798_; lean_object* v___x_5799_; lean_object* v___x_5800_; 
v___x_5796_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_5796_, 0, lean_box(0));
lean_closure_set(v___x_5796_, 1, v_cctx_5767_);
lean_closure_set(v___x_5796_, 2, v___x_5795_);
lean_closure_set(v___x_5796_, 3, v_env_5768_);
lean_closure_set(v___x_5796_, 4, v_act_5769_);
lean_closure_set(v___x_5796_, 5, v_start_5774_);
lean_closure_set(v___x_5796_, 6, v_n_5771_);
v___x_5797_ = lean_unsigned_to_nat(0u);
v___x_5798_ = lean_alloc_closure((void*)(l_BaseIO_asTask___boxed), 4, 3);
lean_closure_set(v___x_5798_, 0, lean_box(0));
lean_closure_set(v___x_5798_, 1, v___x_5796_);
lean_closure_set(v___x_5798_, 2, v___x_5797_);
v___x_5799_ = lean_apply_2(v_inst_5766_, lean_box(0), v___x_5798_);
v___x_5800_ = lean_apply_4(v_toBind_5780_, lean_box(0), lean_box(0), v___x_5799_, v___f_5791_);
return v___x_5800_;
}
}
}
}
else
{
lean_object* v_mdata_5803_; lean_object* v_constants_5804_; lean_object* v___x_5805_; lean_object* v_cnt_5806_; uint8_t v___x_5807_; 
v_mdata_5803_ = lean_array_fget(v_moduleData_5779_, v_idx_5776_);
lean_dec_ref(v_moduleData_5779_);
v_constants_5804_ = lean_ctor_get(v_mdata_5803_, 2);
lean_inc_ref(v_constants_5804_);
lean_dec(v_mdata_5803_);
v___x_5805_ = lean_array_get_size(v_constants_5804_);
lean_dec_ref(v_constants_5804_);
v_cnt_5806_ = lean_nat_add(v_cnt_5775_, v___x_5805_);
lean_dec(v_cnt_5775_);
v___x_5807_ = lean_nat_dec_lt(v_constantsPerTask_5770_, v_cnt_5806_);
if (v___x_5807_ == 0)
{
lean_object* v___x_5808_; lean_object* v___x_5809_; 
v___x_5808_ = lean_unsigned_to_nat(1u);
v___x_5809_ = lean_nat_add(v_idx_5776_, v___x_5808_);
lean_dec(v_idx_5776_);
v_cnt_5775_ = v_cnt_5806_;
v_idx_5776_ = v___x_5809_;
goto _start;
}
else
{
lean_object* v_namePrefix_5811_; lean_object* v_idx_5812_; lean_object* v___x_5814_; uint8_t v_isShared_5815_; uint8_t v_isSharedCheck_5830_; 
lean_inc(v_toBind_5780_);
lean_dec(v_cnt_5806_);
v_namePrefix_5811_ = lean_ctor_get(v_ngen_5772_, 0);
v_idx_5812_ = lean_ctor_get(v_ngen_5772_, 1);
v_isSharedCheck_5830_ = !lean_is_exclusive(v_ngen_5772_);
if (v_isSharedCheck_5830_ == 0)
{
v___x_5814_ = v_ngen_5772_;
v_isShared_5815_ = v_isSharedCheck_5830_;
goto v_resetjp_5813_;
}
else
{
lean_inc(v_idx_5812_);
lean_inc(v_namePrefix_5811_);
lean_dec(v_ngen_5772_);
v___x_5814_ = lean_box(0);
v_isShared_5815_ = v_isSharedCheck_5830_;
goto v_resetjp_5813_;
}
v_resetjp_5813_:
{
lean_object* v___x_5816_; lean_object* v___x_5817_; lean_object* v___x_5819_; 
lean_inc(v_idx_5812_);
lean_inc(v_namePrefix_5811_);
v___x_5816_ = l_Lean_Name_num___override(v_namePrefix_5811_, v_idx_5812_);
v___x_5817_ = lean_unsigned_to_nat(1u);
if (v_isShared_5815_ == 0)
{
lean_ctor_set(v___x_5814_, 1, v___x_5817_);
lean_ctor_set(v___x_5814_, 0, v___x_5816_);
v___x_5819_ = v___x_5814_;
goto v_reusejp_5818_;
}
else
{
lean_object* v_reuseFailAlloc_5829_; 
v_reuseFailAlloc_5829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5829_, 0, v___x_5816_);
lean_ctor_set(v_reuseFailAlloc_5829_, 1, v___x_5817_);
v___x_5819_ = v_reuseFailAlloc_5829_;
goto v_reusejp_5818_;
}
v_reusejp_5818_:
{
lean_object* v___x_5820_; lean_object* v___x_5821_; lean_object* v___x_5822_; lean_object* v___f_5823_; lean_object* v___x_5824_; lean_object* v___x_5825_; lean_object* v___x_5826_; lean_object* v___x_5827_; lean_object* v___x_5828_; 
v___x_5820_ = lean_nat_add(v_idx_5812_, v___x_5817_);
lean_dec(v_idx_5812_);
v___x_5821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5821_, 0, v_namePrefix_5811_);
lean_ctor_set(v___x_5821_, 1, v___x_5820_);
v___x_5822_ = lean_nat_add(v_idx_5776_, v___x_5817_);
lean_dec(v_idx_5776_);
lean_inc(v___x_5822_);
lean_inc_ref(v_act_5769_);
lean_inc_ref(v_env_5768_);
lean_inc_ref(v_cctx_5767_);
lean_inc(v_inst_5766_);
v___f_5823_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__1), 11, 10);
lean_closure_set(v___f_5823_, 0, v_tasks_5773_);
lean_closure_set(v___f_5823_, 1, v_inst_5765_);
lean_closure_set(v___f_5823_, 2, v_inst_5766_);
lean_closure_set(v___f_5823_, 3, v_cctx_5767_);
lean_closure_set(v___f_5823_, 4, v_env_5768_);
lean_closure_set(v___f_5823_, 5, v_act_5769_);
lean_closure_set(v___f_5823_, 6, v_constantsPerTask_5770_);
lean_closure_set(v___f_5823_, 7, v_n_5771_);
lean_closure_set(v___f_5823_, 8, v___x_5821_);
lean_closure_set(v___f_5823_, 9, v___x_5822_);
v___x_5824_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_5824_, 0, lean_box(0));
lean_closure_set(v___x_5824_, 1, v_cctx_5767_);
lean_closure_set(v___x_5824_, 2, v___x_5819_);
lean_closure_set(v___x_5824_, 3, v_env_5768_);
lean_closure_set(v___x_5824_, 4, v_act_5769_);
lean_closure_set(v___x_5824_, 5, v_start_5774_);
lean_closure_set(v___x_5824_, 6, v___x_5822_);
v___x_5825_ = lean_unsigned_to_nat(0u);
v___x_5826_ = lean_alloc_closure((void*)(l_BaseIO_asTask___boxed), 4, 3);
lean_closure_set(v___x_5826_, 0, lean_box(0));
lean_closure_set(v___x_5826_, 1, v___x_5824_);
lean_closure_set(v___x_5826_, 2, v___x_5825_);
v___x_5827_ = lean_apply_2(v_inst_5766_, lean_box(0), v___x_5826_);
v___x_5828_ = lean_apply_4(v_toBind_5780_, lean_box(0), lean_box(0), v___x_5827_, v___f_5823_);
return v___x_5828_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__1(lean_object* v_tasks_5831_, lean_object* v_inst_5832_, lean_object* v_inst_5833_, lean_object* v_cctx_5834_, lean_object* v_env_5835_, lean_object* v_act_5836_, lean_object* v_constantsPerTask_5837_, lean_object* v_n_5838_, lean_object* v___x_5839_, lean_object* v___x_5840_, lean_object* v_t_5841_){
_start:
{
lean_object* v___x_5842_; lean_object* v___x_5843_; lean_object* v___x_5844_; 
v___x_5842_ = lean_array_push(v_tasks_5831_, v_t_5841_);
v___x_5843_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_5840_);
v___x_5844_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(v_inst_5832_, v_inst_5833_, v_cctx_5834_, v_env_5835_, v_act_5836_, v_constantsPerTask_5837_, v_n_5838_, v___x_5839_, v___x_5842_, v___x_5840_, v___x_5843_, v___x_5840_);
return v___x_5844_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go(lean_object* v_m_5845_, lean_object* v_00_u03b1_5846_, lean_object* v_inst_5847_, lean_object* v_inst_5848_, lean_object* v_cctx_5849_, lean_object* v_env_5850_, lean_object* v_act_5851_, lean_object* v_constantsPerTask_5852_, lean_object* v_n_5853_, lean_object* v_ngen_5854_, lean_object* v_tasks_5855_, lean_object* v_start_5856_, lean_object* v_cnt_5857_, lean_object* v_idx_5858_){
_start:
{
lean_object* v___x_5859_; 
v___x_5859_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(v_inst_5847_, v_inst_5848_, v_cctx_5849_, v_env_5850_, v_act_5851_, v_constantsPerTask_5852_, v_n_5853_, v_ngen_5854_, v_tasks_5855_, v_start_5856_, v_cnt_5857_, v_idx_5858_);
return v___x_5859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_getChildNgen_match__1_splitter___redArg(lean_object* v_x_5860_, lean_object* v_h__1_5861_){
_start:
{
lean_object* v_fst_5862_; lean_object* v_snd_5863_; lean_object* v___x_5864_; 
v_fst_5862_ = lean_ctor_get(v_x_5860_, 0);
lean_inc(v_fst_5862_);
v_snd_5863_ = lean_ctor_get(v_x_5860_, 1);
lean_inc(v_snd_5863_);
lean_dec_ref(v_x_5860_);
v___x_5864_ = lean_apply_2(v_h__1_5861_, v_fst_5862_, v_snd_5863_);
return v___x_5864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_getChildNgen_match__1_splitter(lean_object* v_motive_5865_, lean_object* v_x_5866_, lean_object* v_h__1_5867_){
_start:
{
lean_object* v_fst_5868_; lean_object* v_snd_5869_; lean_object* v___x_5870_; 
v_fst_5868_ = lean_ctor_get(v_x_5866_, 0);
lean_inc(v_fst_5868_);
v_snd_5869_ = lean_ctor_get(v_x_5866_, 1);
lean_inc(v_snd_5869_);
lean_dec_ref(v_x_5866_);
v___x_5870_ = lean_apply_2(v_h__1_5867_, v_fst_5868_, v_snd_5869_);
return v___x_5870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__0(lean_object* v_inst_5871_, lean_object* v_inst_5872_, lean_object* v_inst_5873_, lean_object* v_inst_5874_, lean_object* v_x_5875_, lean_object* v___y_5876_){
_start:
{
lean_object* v___x_5877_; 
v___x_5877_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg(v_inst_5871_, v_inst_5872_, v_inst_5873_, v_inst_5874_, v___y_5876_);
return v___x_5877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__1(lean_object* v_r_5878_, lean_object* v_toPure_5879_, lean_object* v_____r_5880_){
_start:
{
lean_object* v_tree_5881_; lean_object* v___x_5882_; lean_object* v___x_5883_; 
v_tree_5881_ = lean_ctor_get(v_r_5878_, 0);
lean_inc_ref(v_tree_5881_);
lean_dec(v_r_5878_);
v___x_5882_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_tree_5881_);
v___x_5883_ = lean_apply_2(v_toPure_5879_, lean_box(0), v___x_5882_);
return v___x_5883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__2(lean_object* v___x_5884_, lean_object* v___x_5885_, lean_object* v_toPure_5886_, lean_object* v_toBind_5887_, lean_object* v_inst_5888_, lean_object* v___f_5889_, lean_object* v_tasks_5890_){
_start:
{
lean_object* v___x_5891_; lean_object* v___x_5892_; lean_object* v___x_5893_; lean_object* v___x_5894_; lean_object* v___x_5895_; lean_object* v_r_5896_; lean_object* v_errors_5897_; lean_object* v___f_5898_; lean_object* v___x_5899_; lean_object* v___x_5900_; uint8_t v___x_5901_; 
v___x_5891_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__1);
lean_inc(v___x_5884_);
v___x_5892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5892_, 0, v___x_5884_);
lean_ctor_set(v___x_5892_, 1, v___x_5891_);
v___x_5893_ = lean_mk_empty_array_with_capacity(v___x_5884_);
lean_inc_ref(v___x_5893_);
v___x_5894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5894_, 0, v___x_5892_);
lean_ctor_set(v___x_5894_, 1, v___x_5893_);
v___x_5895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5895_, 0, v___x_5894_);
lean_ctor_set(v___x_5895_, 1, v___x_5893_);
v_r_5896_ = l_Lean_Meta_LazyDiscrTree_combineGet___redArg(v___x_5885_, v___x_5895_, v_tasks_5890_);
v_errors_5897_ = lean_ctor_get(v_r_5896_, 1);
lean_inc_ref(v_errors_5897_);
lean_inc(v_toPure_5886_);
v___f_5898_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__1), 3, 2);
lean_closure_set(v___f_5898_, 0, v_r_5896_);
lean_closure_set(v___f_5898_, 1, v_toPure_5886_);
v___x_5899_ = lean_array_get_size(v_errors_5897_);
v___x_5900_ = lean_box(0);
v___x_5901_ = lean_nat_dec_lt(v___x_5884_, v___x_5899_);
lean_dec(v___x_5884_);
if (v___x_5901_ == 0)
{
lean_object* v___x_5902_; lean_object* v___x_5903_; 
lean_dec_ref(v_errors_5897_);
lean_dec(v___f_5889_);
lean_dec_ref(v_inst_5888_);
v___x_5902_ = lean_apply_2(v_toPure_5886_, lean_box(0), v___x_5900_);
v___x_5903_ = lean_apply_4(v_toBind_5887_, lean_box(0), lean_box(0), v___x_5902_, v___f_5898_);
return v___x_5903_;
}
else
{
uint8_t v___x_5904_; 
v___x_5904_ = lean_nat_dec_le(v___x_5899_, v___x_5899_);
if (v___x_5904_ == 0)
{
if (v___x_5901_ == 0)
{
lean_object* v___x_5905_; lean_object* v___x_5906_; 
lean_dec_ref(v_errors_5897_);
lean_dec(v___f_5889_);
lean_dec_ref(v_inst_5888_);
v___x_5905_ = lean_apply_2(v_toPure_5886_, lean_box(0), v___x_5900_);
v___x_5906_ = lean_apply_4(v_toBind_5887_, lean_box(0), lean_box(0), v___x_5905_, v___f_5898_);
return v___x_5906_;
}
else
{
size_t v___x_5907_; size_t v___x_5908_; lean_object* v___x_5909_; lean_object* v___x_5910_; 
lean_dec(v_toPure_5886_);
v___x_5907_ = ((size_t)0ULL);
v___x_5908_ = lean_usize_of_nat(v___x_5899_);
v___x_5909_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_5888_, v___f_5889_, v_errors_5897_, v___x_5907_, v___x_5908_, v___x_5900_);
v___x_5910_ = lean_apply_4(v_toBind_5887_, lean_box(0), lean_box(0), v___x_5909_, v___f_5898_);
return v___x_5910_;
}
}
else
{
size_t v___x_5911_; size_t v___x_5912_; lean_object* v___x_5913_; lean_object* v___x_5914_; 
lean_dec(v_toPure_5886_);
v___x_5911_ = ((size_t)0ULL);
v___x_5912_ = lean_usize_of_nat(v___x_5899_);
v___x_5913_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_5888_, v___f_5889_, v_errors_5897_, v___x_5911_, v___x_5912_, v___x_5900_);
v___x_5914_ = lean_apply_4(v_toBind_5887_, lean_box(0), lean_box(0), v___x_5913_, v___f_5898_);
return v___x_5914_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg(lean_object* v_inst_5917_, lean_object* v_inst_5918_, lean_object* v_inst_5919_, lean_object* v_inst_5920_, lean_object* v_inst_5921_, lean_object* v_cctx_5922_, lean_object* v_ngen_5923_, lean_object* v_env_5924_, lean_object* v_act_5925_, lean_object* v_constantsPerTask_5926_){
_start:
{
lean_object* v___x_5927_; lean_object* v_moduleData_5928_; lean_object* v_toApplicative_5929_; lean_object* v_toBind_5930_; lean_object* v_n_5931_; lean_object* v___x_5932_; lean_object* v___x_5933_; lean_object* v___x_5934_; lean_object* v_toPure_5935_; lean_object* v___f_5936_; lean_object* v___x_5937_; lean_object* v___f_5938_; lean_object* v___x_5939_; 
v___x_5927_ = l_Lean_Environment_header(v_env_5924_);
v_moduleData_5928_ = lean_ctor_get(v___x_5927_, 6);
lean_inc_ref(v_moduleData_5928_);
lean_dec_ref(v___x_5927_);
v_toApplicative_5929_ = lean_ctor_get(v_inst_5917_, 0);
v_toBind_5930_ = lean_ctor_get(v_inst_5917_, 1);
lean_inc_n(v_toBind_5930_, 2);
v_n_5931_ = lean_array_get_size(v_moduleData_5928_);
lean_dec_ref(v_moduleData_5928_);
v___x_5932_ = lean_unsigned_to_nat(0u);
v___x_5933_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
lean_inc_ref_n(v_inst_5917_, 2);
v___x_5934_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(v_inst_5917_, v_inst_5921_, v_cctx_5922_, v_env_5924_, v_act_5925_, v_constantsPerTask_5926_, v_n_5931_, v_ngen_5923_, v___x_5933_, v___x_5932_, v___x_5932_, v___x_5932_);
v_toPure_5935_ = lean_ctor_get(v_toApplicative_5929_, 1);
lean_inc(v_toPure_5935_);
v___f_5936_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__0), 6, 4);
lean_closure_set(v___f_5936_, 0, v_inst_5917_);
lean_closure_set(v___f_5936_, 1, v_inst_5918_);
lean_closure_set(v___f_5936_, 2, v_inst_5919_);
lean_closure_set(v___f_5936_, 3, v_inst_5920_);
v___x_5937_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___redArg___closed__0));
v___f_5938_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__2), 7, 6);
lean_closure_set(v___f_5938_, 0, v___x_5932_);
lean_closure_set(v___f_5938_, 1, v___x_5937_);
lean_closure_set(v___f_5938_, 2, v_toPure_5935_);
lean_closure_set(v___f_5938_, 3, v_toBind_5930_);
lean_closure_set(v___f_5938_, 4, v_inst_5917_);
lean_closure_set(v___f_5938_, 5, v___f_5936_);
v___x_5939_ = lean_apply_4(v_toBind_5930_, lean_box(0), lean_box(0), v___x_5934_, v___f_5938_);
return v___x_5939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree(lean_object* v_m_5940_, lean_object* v_00_u03b1_5941_, lean_object* v_inst_5942_, lean_object* v_inst_5943_, lean_object* v_inst_5944_, lean_object* v_inst_5945_, lean_object* v_inst_5946_, lean_object* v_cctx_5947_, lean_object* v_ngen_5948_, lean_object* v_env_5949_, lean_object* v_act_5950_, lean_object* v_constantsPerTask_5951_){
_start:
{
lean_object* v___x_5952_; 
v___x_5952_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg(v_inst_5942_, v_inst_5943_, v_inst_5944_, v_inst_5945_, v_inst_5946_, v_cctx_5947_, v_ngen_5948_, v_env_5949_, v_act_5950_, v_constantsPerTask_5951_);
return v___x_5952_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0(void){
_start:
{
lean_object* v___x_5953_; lean_object* v___x_5954_; lean_object* v___x_5955_; 
v___x_5953_ = lean_box(0);
v___x_5954_ = lean_unsigned_to_nat(16u);
v___x_5955_ = lean_mk_array(v___x_5954_, v___x_5953_);
return v___x_5955_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1(void){
_start:
{
lean_object* v___x_5956_; lean_object* v___x_5957_; lean_object* v___x_5958_; 
v___x_5956_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0, &l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0);
v___x_5957_ = lean_unsigned_to_nat(0u);
v___x_5958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5958_, 0, v___x_5957_);
lean_ctor_set(v___x_5958_, 1, v___x_5956_);
return v___x_5958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createTreeCtx(lean_object* v_ctx_5959_){
_start:
{
lean_object* v_toCold_5960_; lean_object* v_ref_5961_; lean_object* v___x_5963_; uint8_t v_isShared_5964_; uint8_t v_isSharedCheck_5995_; 
v_toCold_5960_ = lean_ctor_get(v_ctx_5959_, 0);
v_ref_5961_ = lean_ctor_get(v_ctx_5959_, 2);
v_isSharedCheck_5995_ = !lean_is_exclusive(v_ctx_5959_);
if (v_isSharedCheck_5995_ == 0)
{
lean_object* v_unused_5996_; 
v_unused_5996_ = lean_ctor_get(v_ctx_5959_, 1);
lean_dec(v_unused_5996_);
v___x_5963_ = v_ctx_5959_;
v_isShared_5964_ = v_isSharedCheck_5995_;
goto v_resetjp_5962_;
}
else
{
lean_inc(v_ref_5961_);
lean_inc(v_toCold_5960_);
lean_dec(v_ctx_5959_);
v___x_5963_ = lean_box(0);
v_isShared_5964_ = v_isSharedCheck_5995_;
goto v_resetjp_5962_;
}
v_resetjp_5962_:
{
lean_object* v_fileName_5965_; lean_object* v_fileMap_5966_; lean_object* v_options_5967_; lean_object* v_maxRecDepth_5968_; lean_object* v___x_5970_; uint8_t v_isShared_5971_; uint8_t v_isSharedCheck_5986_; 
v_fileName_5965_ = lean_ctor_get(v_toCold_5960_, 0);
v_fileMap_5966_ = lean_ctor_get(v_toCold_5960_, 1);
v_options_5967_ = lean_ctor_get(v_toCold_5960_, 2);
v_maxRecDepth_5968_ = lean_ctor_get(v_toCold_5960_, 3);
v_isSharedCheck_5986_ = !lean_is_exclusive(v_toCold_5960_);
if (v_isSharedCheck_5986_ == 0)
{
lean_object* v_unused_5987_; lean_object* v_unused_5988_; lean_object* v_unused_5989_; lean_object* v_unused_5990_; lean_object* v_unused_5991_; lean_object* v_unused_5992_; lean_object* v_unused_5993_; lean_object* v_unused_5994_; 
v_unused_5987_ = lean_ctor_get(v_toCold_5960_, 11);
lean_dec(v_unused_5987_);
v_unused_5988_ = lean_ctor_get(v_toCold_5960_, 10);
lean_dec(v_unused_5988_);
v_unused_5989_ = lean_ctor_get(v_toCold_5960_, 9);
lean_dec(v_unused_5989_);
v_unused_5990_ = lean_ctor_get(v_toCold_5960_, 8);
lean_dec(v_unused_5990_);
v_unused_5991_ = lean_ctor_get(v_toCold_5960_, 7);
lean_dec(v_unused_5991_);
v_unused_5992_ = lean_ctor_get(v_toCold_5960_, 6);
lean_dec(v_unused_5992_);
v_unused_5993_ = lean_ctor_get(v_toCold_5960_, 5);
lean_dec(v_unused_5993_);
v_unused_5994_ = lean_ctor_get(v_toCold_5960_, 4);
lean_dec(v_unused_5994_);
v___x_5970_ = v_toCold_5960_;
v_isShared_5971_ = v_isSharedCheck_5986_;
goto v_resetjp_5969_;
}
else
{
lean_inc(v_maxRecDepth_5968_);
lean_inc(v_options_5967_);
lean_inc(v_fileMap_5966_);
lean_inc(v_fileName_5965_);
lean_dec(v_toCold_5960_);
v___x_5970_ = lean_box(0);
v_isShared_5971_ = v_isSharedCheck_5986_;
goto v_resetjp_5969_;
}
v_resetjp_5969_:
{
lean_object* v___x_5972_; lean_object* v___x_5973_; lean_object* v___x_5974_; lean_object* v___x_5975_; lean_object* v___x_5976_; lean_object* v___x_5977_; lean_object* v___x_5979_; 
v___x_5972_ = lean_box(0);
v___x_5973_ = lean_box(0);
v___x_5974_ = lean_unsigned_to_nat(0u);
v___x_5975_ = l_Lean_firstFrontendMacroScope;
v___x_5976_ = lean_box(0);
v___x_5977_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1, &l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1);
lean_inc_ref(v_options_5967_);
if (v_isShared_5971_ == 0)
{
lean_ctor_set(v___x_5970_, 11, v___x_5977_);
lean_ctor_set(v___x_5970_, 10, v___x_5976_);
lean_ctor_set(v___x_5970_, 9, v___x_5975_);
lean_ctor_set(v___x_5970_, 8, v___x_5972_);
lean_ctor_set(v___x_5970_, 7, v___x_5974_);
lean_ctor_set(v___x_5970_, 6, v___x_5974_);
lean_ctor_set(v___x_5970_, 5, v___x_5973_);
lean_ctor_set(v___x_5970_, 4, v___x_5972_);
v___x_5979_ = v___x_5970_;
goto v_reusejp_5978_;
}
else
{
lean_object* v_reuseFailAlloc_5985_; 
v_reuseFailAlloc_5985_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_5985_, 0, v_fileName_5965_);
lean_ctor_set(v_reuseFailAlloc_5985_, 1, v_fileMap_5966_);
lean_ctor_set(v_reuseFailAlloc_5985_, 2, v_options_5967_);
lean_ctor_set(v_reuseFailAlloc_5985_, 3, v_maxRecDepth_5968_);
lean_ctor_set(v_reuseFailAlloc_5985_, 4, v___x_5972_);
lean_ctor_set(v_reuseFailAlloc_5985_, 5, v___x_5973_);
lean_ctor_set(v_reuseFailAlloc_5985_, 6, v___x_5974_);
lean_ctor_set(v_reuseFailAlloc_5985_, 7, v___x_5974_);
lean_ctor_set(v_reuseFailAlloc_5985_, 8, v___x_5972_);
lean_ctor_set(v_reuseFailAlloc_5985_, 9, v___x_5975_);
lean_ctor_set(v_reuseFailAlloc_5985_, 10, v___x_5976_);
lean_ctor_set(v_reuseFailAlloc_5985_, 11, v___x_5977_);
v___x_5979_ = v_reuseFailAlloc_5985_;
goto v_reusejp_5978_;
}
v_reusejp_5978_:
{
uint8_t v___x_5980_; uint8_t v___x_5981_; lean_object* v___x_5983_; 
v___x_5980_ = l_Lean_getDiag(v_options_5967_);
lean_dec_ref(v_options_5967_);
v___x_5981_ = 0;
if (v_isShared_5964_ == 0)
{
lean_ctor_set(v___x_5963_, 1, v___x_5974_);
lean_ctor_set(v___x_5963_, 0, v___x_5979_);
v___x_5983_ = v___x_5963_;
goto v_reusejp_5982_;
}
else
{
lean_object* v_reuseFailAlloc_5984_; 
v_reuseFailAlloc_5984_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5984_, 0, v___x_5979_);
lean_ctor_set(v_reuseFailAlloc_5984_, 1, v___x_5974_);
lean_ctor_set(v_reuseFailAlloc_5984_, 2, v_ref_5961_);
v___x_5983_ = v_reuseFailAlloc_5984_;
goto v_reusejp_5982_;
}
v_reusejp_5982_:
{
lean_ctor_set_uint8(v___x_5983_, sizeof(void*)*3, v___x_5980_);
lean_ctor_set_uint8(v___x_5983_, sizeof(void*)*3 + 1, v___x_5981_);
return v___x_5983_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(lean_object* v_category_5997_, lean_object* v_opts_5998_, lean_object* v_act_5999_, lean_object* v_decl_6000_, lean_object* v___y_6001_, lean_object* v___y_6002_, lean_object* v___y_6003_, lean_object* v___y_6004_){
_start:
{
lean_object* v___x_6006_; lean_object* v___x_6007_; 
lean_inc(v___y_6004_);
lean_inc_ref(v___y_6003_);
lean_inc(v___y_6002_);
lean_inc_ref(v___y_6001_);
v___x_6006_ = lean_apply_4(v_act_5999_, v___y_6001_, v___y_6002_, v___y_6003_, v___y_6004_);
v___x_6007_ = l_Lean_profileitIOUnsafe___redArg(v_category_5997_, v_opts_5998_, v___x_6006_, v_decl_6000_);
return v___x_6007_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg___boxed(lean_object* v_category_6008_, lean_object* v_opts_6009_, lean_object* v_act_6010_, lean_object* v_decl_6011_, lean_object* v___y_6012_, lean_object* v___y_6013_, lean_object* v___y_6014_, lean_object* v___y_6015_, lean_object* v___y_6016_){
_start:
{
lean_object* v_res_6017_; 
v_res_6017_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v_category_6008_, v_opts_6009_, v_act_6010_, v_decl_6011_, v___y_6012_, v___y_6013_, v___y_6014_, v___y_6015_);
lean_dec(v___y_6015_);
lean_dec_ref(v___y_6014_);
lean_dec(v___y_6013_);
lean_dec_ref(v___y_6012_);
lean_dec_ref(v_opts_6009_);
lean_dec_ref(v_category_6008_);
return v_res_6017_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1(lean_object* v_00_u03b1_6018_, lean_object* v_category_6019_, lean_object* v_opts_6020_, lean_object* v_act_6021_, lean_object* v_decl_6022_, lean_object* v___y_6023_, lean_object* v___y_6024_, lean_object* v___y_6025_, lean_object* v___y_6026_){
_start:
{
lean_object* v___x_6028_; 
v___x_6028_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v_category_6019_, v_opts_6020_, v_act_6021_, v_decl_6022_, v___y_6023_, v___y_6024_, v___y_6025_, v___y_6026_);
return v___x_6028_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___boxed(lean_object* v_00_u03b1_6029_, lean_object* v_category_6030_, lean_object* v_opts_6031_, lean_object* v_act_6032_, lean_object* v_decl_6033_, lean_object* v___y_6034_, lean_object* v___y_6035_, lean_object* v___y_6036_, lean_object* v___y_6037_, lean_object* v___y_6038_){
_start:
{
lean_object* v_res_6039_; 
v_res_6039_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1(v_00_u03b1_6029_, v_category_6030_, v_opts_6031_, v_act_6032_, v_decl_6033_, v___y_6034_, v___y_6035_, v___y_6036_, v___y_6037_);
lean_dec(v___y_6037_);
lean_dec_ref(v___y_6036_);
lean_dec(v___y_6035_);
lean_dec_ref(v___y_6034_);
lean_dec_ref(v_opts_6031_);
lean_dec_ref(v_category_6030_);
return v_res_6039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(lean_object* v_cctx_6040_, lean_object* v_env_6041_, lean_object* v_act_6042_, lean_object* v_constantsPerTask_6043_, lean_object* v_n_6044_, lean_object* v_ngen_6045_, lean_object* v_tasks_6046_, lean_object* v_start_6047_, lean_object* v_cnt_6048_, lean_object* v_idx_6049_){
_start:
{
lean_object* v___x_6051_; lean_object* v_moduleData_6052_; lean_object* v___x_6053_; uint8_t v___x_6054_; 
v___x_6051_ = l_Lean_Environment_header(v_env_6041_);
v_moduleData_6052_ = lean_ctor_get(v___x_6051_, 6);
lean_inc_ref(v_moduleData_6052_);
lean_dec_ref(v___x_6051_);
v___x_6053_ = lean_array_get_size(v_moduleData_6052_);
v___x_6054_ = lean_nat_dec_lt(v_idx_6049_, v___x_6053_);
if (v___x_6054_ == 0)
{
uint8_t v___x_6055_; 
lean_dec_ref(v_moduleData_6052_);
lean_dec(v_idx_6049_);
lean_dec(v_cnt_6048_);
v___x_6055_ = lean_nat_dec_lt(v_start_6047_, v_n_6044_);
if (v___x_6055_ == 0)
{
lean_object* v___x_6056_; 
lean_dec(v_start_6047_);
lean_dec_ref(v_ngen_6045_);
lean_dec(v_n_6044_);
lean_dec_ref(v_act_6042_);
lean_dec_ref(v_env_6041_);
lean_dec_ref(v_cctx_6040_);
v___x_6056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6056_, 0, v_tasks_6046_);
return v___x_6056_;
}
else
{
lean_object* v_namePrefix_6057_; lean_object* v_idx_6058_; lean_object* v___x_6060_; uint8_t v_isShared_6061_; uint8_t v_isSharedCheck_6072_; 
v_namePrefix_6057_ = lean_ctor_get(v_ngen_6045_, 0);
v_idx_6058_ = lean_ctor_get(v_ngen_6045_, 1);
v_isSharedCheck_6072_ = !lean_is_exclusive(v_ngen_6045_);
if (v_isSharedCheck_6072_ == 0)
{
v___x_6060_ = v_ngen_6045_;
v_isShared_6061_ = v_isSharedCheck_6072_;
goto v_resetjp_6059_;
}
else
{
lean_inc(v_idx_6058_);
lean_inc(v_namePrefix_6057_);
lean_dec(v_ngen_6045_);
v___x_6060_ = lean_box(0);
v_isShared_6061_ = v_isSharedCheck_6072_;
goto v_resetjp_6059_;
}
v_resetjp_6059_:
{
lean_object* v___x_6062_; lean_object* v___x_6063_; lean_object* v___x_6065_; 
v___x_6062_ = l_Lean_Name_num___override(v_namePrefix_6057_, v_idx_6058_);
v___x_6063_ = lean_unsigned_to_nat(1u);
if (v_isShared_6061_ == 0)
{
lean_ctor_set(v___x_6060_, 1, v___x_6063_);
lean_ctor_set(v___x_6060_, 0, v___x_6062_);
v___x_6065_ = v___x_6060_;
goto v_reusejp_6064_;
}
else
{
lean_object* v_reuseFailAlloc_6071_; 
v_reuseFailAlloc_6071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6071_, 0, v___x_6062_);
lean_ctor_set(v_reuseFailAlloc_6071_, 1, v___x_6063_);
v___x_6065_ = v_reuseFailAlloc_6071_;
goto v_reusejp_6064_;
}
v_reusejp_6064_:
{
lean_object* v___x_6066_; lean_object* v___x_6067_; lean_object* v___x_6068_; lean_object* v___x_6069_; lean_object* v___x_6070_; 
v___x_6066_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_6066_, 0, lean_box(0));
lean_closure_set(v___x_6066_, 1, v_cctx_6040_);
lean_closure_set(v___x_6066_, 2, v___x_6065_);
lean_closure_set(v___x_6066_, 3, v_env_6041_);
lean_closure_set(v___x_6066_, 4, v_act_6042_);
lean_closure_set(v___x_6066_, 5, v_start_6047_);
lean_closure_set(v___x_6066_, 6, v_n_6044_);
v___x_6067_ = lean_unsigned_to_nat(0u);
v___x_6068_ = lean_io_as_task(v___x_6066_, v___x_6067_);
v___x_6069_ = lean_array_push(v_tasks_6046_, v___x_6068_);
v___x_6070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6070_, 0, v___x_6069_);
return v___x_6070_;
}
}
}
}
else
{
lean_object* v_mdata_6073_; lean_object* v_constants_6074_; lean_object* v___x_6075_; lean_object* v_cnt_6076_; uint8_t v___x_6077_; 
v_mdata_6073_ = lean_array_fget(v_moduleData_6052_, v_idx_6049_);
lean_dec_ref(v_moduleData_6052_);
v_constants_6074_ = lean_ctor_get(v_mdata_6073_, 2);
lean_inc_ref(v_constants_6074_);
lean_dec(v_mdata_6073_);
v___x_6075_ = lean_array_get_size(v_constants_6074_);
lean_dec_ref(v_constants_6074_);
v_cnt_6076_ = lean_nat_add(v_cnt_6048_, v___x_6075_);
lean_dec(v_cnt_6048_);
v___x_6077_ = lean_nat_dec_lt(v_constantsPerTask_6043_, v_cnt_6076_);
if (v___x_6077_ == 0)
{
lean_object* v___x_6078_; lean_object* v___x_6079_; 
v___x_6078_ = lean_unsigned_to_nat(1u);
v___x_6079_ = lean_nat_add(v_idx_6049_, v___x_6078_);
lean_dec(v_idx_6049_);
v_cnt_6048_ = v_cnt_6076_;
v_idx_6049_ = v___x_6079_;
goto _start;
}
else
{
lean_object* v_namePrefix_6081_; lean_object* v_idx_6082_; lean_object* v___x_6084_; uint8_t v_isShared_6085_; uint8_t v_isSharedCheck_6099_; 
lean_dec(v_cnt_6076_);
v_namePrefix_6081_ = lean_ctor_get(v_ngen_6045_, 0);
v_idx_6082_ = lean_ctor_get(v_ngen_6045_, 1);
v_isSharedCheck_6099_ = !lean_is_exclusive(v_ngen_6045_);
if (v_isSharedCheck_6099_ == 0)
{
v___x_6084_ = v_ngen_6045_;
v_isShared_6085_ = v_isSharedCheck_6099_;
goto v_resetjp_6083_;
}
else
{
lean_inc(v_idx_6082_);
lean_inc(v_namePrefix_6081_);
lean_dec(v_ngen_6045_);
v___x_6084_ = lean_box(0);
v_isShared_6085_ = v_isSharedCheck_6099_;
goto v_resetjp_6083_;
}
v_resetjp_6083_:
{
lean_object* v___x_6086_; lean_object* v___x_6087_; lean_object* v___x_6089_; 
lean_inc(v_idx_6082_);
lean_inc(v_namePrefix_6081_);
v___x_6086_ = l_Lean_Name_num___override(v_namePrefix_6081_, v_idx_6082_);
v___x_6087_ = lean_unsigned_to_nat(1u);
if (v_isShared_6085_ == 0)
{
lean_ctor_set(v___x_6084_, 1, v___x_6087_);
lean_ctor_set(v___x_6084_, 0, v___x_6086_);
v___x_6089_ = v___x_6084_;
goto v_reusejp_6088_;
}
else
{
lean_object* v_reuseFailAlloc_6098_; 
v_reuseFailAlloc_6098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6098_, 0, v___x_6086_);
lean_ctor_set(v_reuseFailAlloc_6098_, 1, v___x_6087_);
v___x_6089_ = v_reuseFailAlloc_6098_;
goto v_reusejp_6088_;
}
v_reusejp_6088_:
{
lean_object* v___x_6090_; lean_object* v___x_6091_; lean_object* v___x_6092_; lean_object* v___x_6093_; lean_object* v___x_6094_; lean_object* v___x_6095_; lean_object* v___x_6096_; 
v___x_6090_ = lean_nat_add(v_idx_6082_, v___x_6087_);
lean_dec(v_idx_6082_);
v___x_6091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6091_, 0, v_namePrefix_6081_);
lean_ctor_set(v___x_6091_, 1, v___x_6090_);
v___x_6092_ = lean_nat_add(v_idx_6049_, v___x_6087_);
lean_dec(v_idx_6049_);
lean_inc_n(v___x_6092_, 2);
lean_inc_ref(v_act_6042_);
lean_inc_ref(v_env_6041_);
lean_inc_ref(v_cctx_6040_);
v___x_6093_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_6093_, 0, lean_box(0));
lean_closure_set(v___x_6093_, 1, v_cctx_6040_);
lean_closure_set(v___x_6093_, 2, v___x_6089_);
lean_closure_set(v___x_6093_, 3, v_env_6041_);
lean_closure_set(v___x_6093_, 4, v_act_6042_);
lean_closure_set(v___x_6093_, 5, v_start_6047_);
lean_closure_set(v___x_6093_, 6, v___x_6092_);
v___x_6094_ = lean_unsigned_to_nat(0u);
v___x_6095_ = lean_io_as_task(v___x_6093_, v___x_6094_);
v___x_6096_ = lean_array_push(v_tasks_6046_, v___x_6095_);
v_ngen_6045_ = v___x_6091_;
v_tasks_6046_ = v___x_6096_;
v_start_6047_ = v___x_6092_;
v_cnt_6048_ = v___x_6094_;
v_idx_6049_ = v___x_6092_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg___boxed(lean_object* v_cctx_6100_, lean_object* v_env_6101_, lean_object* v_act_6102_, lean_object* v_constantsPerTask_6103_, lean_object* v_n_6104_, lean_object* v_ngen_6105_, lean_object* v_tasks_6106_, lean_object* v_start_6107_, lean_object* v_cnt_6108_, lean_object* v_idx_6109_, lean_object* v___y_6110_){
_start:
{
lean_object* v_res_6111_; 
v_res_6111_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(v_cctx_6100_, v_env_6101_, v_act_6102_, v_constantsPerTask_6103_, v_n_6104_, v_ngen_6105_, v_tasks_6106_, v_start_6107_, v_cnt_6108_, v_idx_6109_);
lean_dec(v_constantsPerTask_6103_);
return v_res_6111_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0(uint8_t v_suppressElabErrors_6120_, uint8_t v___y_6121_, lean_object* v_x_6122_){
_start:
{
if (lean_obj_tag(v_x_6122_) == 1)
{
lean_object* v_pre_6123_; 
v_pre_6123_ = lean_ctor_get(v_x_6122_, 0);
switch(lean_obj_tag(v_pre_6123_))
{
case 1:
{
lean_object* v_pre_6124_; 
v_pre_6124_ = lean_ctor_get(v_pre_6123_, 0);
switch(lean_obj_tag(v_pre_6124_))
{
case 0:
{
lean_object* v_str_6125_; lean_object* v_str_6126_; lean_object* v___x_6127_; uint8_t v___x_6128_; 
v_str_6125_ = lean_ctor_get(v_x_6122_, 1);
v_str_6126_ = lean_ctor_get(v_pre_6123_, 1);
v___x_6127_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__0));
v___x_6128_ = lean_string_dec_eq(v_str_6126_, v___x_6127_);
if (v___x_6128_ == 0)
{
lean_object* v___x_6129_; uint8_t v___x_6130_; 
v___x_6129_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__1));
v___x_6130_ = lean_string_dec_eq(v_str_6126_, v___x_6129_);
if (v___x_6130_ == 0)
{
return v___x_6130_;
}
else
{
lean_object* v___x_6131_; uint8_t v___x_6132_; 
v___x_6131_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__2));
v___x_6132_ = lean_string_dec_eq(v_str_6125_, v___x_6131_);
if (v___x_6132_ == 0)
{
return v___x_6132_;
}
else
{
return v_suppressElabErrors_6120_;
}
}
}
else
{
lean_object* v___x_6133_; uint8_t v___x_6134_; 
v___x_6133_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__3));
v___x_6134_ = lean_string_dec_eq(v_str_6125_, v___x_6133_);
if (v___x_6134_ == 0)
{
return v___x_6134_;
}
else
{
return v_suppressElabErrors_6120_;
}
}
}
case 1:
{
lean_object* v_pre_6135_; 
v_pre_6135_ = lean_ctor_get(v_pre_6124_, 0);
if (lean_obj_tag(v_pre_6135_) == 0)
{
lean_object* v_str_6136_; lean_object* v_str_6137_; lean_object* v_str_6138_; lean_object* v___x_6139_; uint8_t v___x_6140_; 
v_str_6136_ = lean_ctor_get(v_x_6122_, 1);
v_str_6137_ = lean_ctor_get(v_pre_6123_, 1);
v_str_6138_ = lean_ctor_get(v_pre_6124_, 1);
v___x_6139_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__4));
v___x_6140_ = lean_string_dec_eq(v_str_6138_, v___x_6139_);
if (v___x_6140_ == 0)
{
return v___x_6140_;
}
else
{
lean_object* v___x_6141_; uint8_t v___x_6142_; 
v___x_6141_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__5));
v___x_6142_ = lean_string_dec_eq(v_str_6137_, v___x_6141_);
if (v___x_6142_ == 0)
{
return v___x_6142_;
}
else
{
lean_object* v___x_6143_; uint8_t v___x_6144_; 
v___x_6143_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__6));
v___x_6144_ = lean_string_dec_eq(v_str_6136_, v___x_6143_);
if (v___x_6144_ == 0)
{
return v___x_6144_;
}
else
{
return v_suppressElabErrors_6120_;
}
}
}
}
else
{
return v___y_6121_;
}
}
default: 
{
return v___y_6121_;
}
}
}
case 0:
{
lean_object* v_str_6145_; lean_object* v___x_6146_; uint8_t v___x_6147_; 
v_str_6145_ = lean_ctor_get(v_x_6122_, 1);
v___x_6146_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__7));
v___x_6147_ = lean_string_dec_eq(v_str_6145_, v___x_6146_);
if (v___x_6147_ == 0)
{
return v___x_6147_;
}
else
{
return v_suppressElabErrors_6120_;
}
}
default: 
{
return v___y_6121_;
}
}
}
else
{
return v___y_6121_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___boxed(lean_object* v_suppressElabErrors_6148_, lean_object* v___y_6149_, lean_object* v_x_6150_){
_start:
{
uint8_t v_suppressElabErrors_boxed_6151_; uint8_t v___y_8135__boxed_6152_; uint8_t v_res_6153_; lean_object* v_r_6154_; 
v_suppressElabErrors_boxed_6151_ = lean_unbox(v_suppressElabErrors_6148_);
v___y_8135__boxed_6152_ = lean_unbox(v___y_6149_);
v_res_6153_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0(v_suppressElabErrors_boxed_6151_, v___y_8135__boxed_6152_, v_x_6150_);
lean_dec(v_x_6150_);
v_r_6154_ = lean_box(v_res_6153_);
return v_r_6154_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7(lean_object* v_ref_6156_, lean_object* v_msgData_6157_, uint8_t v_severity_6158_, uint8_t v_isSilent_6159_, lean_object* v___y_6160_, lean_object* v___y_6161_, lean_object* v___y_6162_, lean_object* v___y_6163_){
_start:
{
lean_object* v___y_6166_; lean_object* v___y_6167_; uint8_t v___y_6168_; lean_object* v___y_6169_; lean_object* v___y_6170_; uint8_t v___y_6171_; lean_object* v___y_6172_; lean_object* v_currNamespace_6173_; lean_object* v_openDecls_6174_; lean_object* v___y_6175_; lean_object* v___y_6201_; lean_object* v___y_6202_; lean_object* v___y_6203_; uint8_t v___y_6204_; uint8_t v___y_6205_; lean_object* v___y_6206_; lean_object* v___y_6207_; uint8_t v___y_6208_; lean_object* v___y_6209_; lean_object* v___y_6210_; lean_object* v___y_6228_; lean_object* v___y_6229_; lean_object* v___y_6230_; uint8_t v___y_6231_; lean_object* v___y_6232_; uint8_t v___y_6233_; lean_object* v___y_6234_; lean_object* v___y_6235_; uint8_t v___y_6236_; lean_object* v___y_6237_; lean_object* v___y_6241_; lean_object* v___y_6242_; lean_object* v___y_6243_; uint8_t v___y_6244_; lean_object* v___y_6245_; lean_object* v___y_6246_; uint8_t v___y_6247_; lean_object* v___y_6248_; uint8_t v___y_6249_; uint8_t v___x_6254_; lean_object* v___y_6256_; lean_object* v___y_6257_; lean_object* v___y_6258_; lean_object* v___y_6259_; lean_object* v___y_6260_; uint8_t v___y_6261_; uint8_t v___y_6262_; lean_object* v___y_6263_; uint8_t v___y_6264_; uint8_t v___y_6266_; uint8_t v___x_6284_; 
v___x_6254_ = 2;
v___x_6284_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6158_, v___x_6254_);
if (v___x_6284_ == 0)
{
v___y_6266_ = v___x_6284_;
goto v___jp_6265_;
}
else
{
uint8_t v___x_6285_; 
lean_inc_ref(v_msgData_6157_);
v___x_6285_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_6157_);
v___y_6266_ = v___x_6285_;
goto v___jp_6265_;
}
v___jp_6165_:
{
lean_object* v___x_6176_; lean_object* v___x_6177_; lean_object* v___x_6178_; lean_object* v___x_6179_; lean_object* v_env_6180_; lean_object* v_nextMacroScope_6181_; lean_object* v_ngen_6182_; lean_object* v_auxDeclNGen_6183_; lean_object* v_traceState_6184_; lean_object* v_cache_6185_; lean_object* v_messages_6186_; lean_object* v_infoState_6187_; lean_object* v_snapshotTasks_6188_; lean_object* v___x_6190_; uint8_t v_isShared_6191_; uint8_t v_isSharedCheck_6199_; 
lean_inc(v_openDecls_6174_);
lean_inc(v_currNamespace_6173_);
v___x_6176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6176_, 0, v_currNamespace_6173_);
lean_ctor_set(v___x_6176_, 1, v_openDecls_6174_);
v___x_6177_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6177_, 0, v___x_6176_);
lean_ctor_set(v___x_6177_, 1, v___y_6167_);
lean_inc_ref(v___y_6172_);
lean_inc_ref(v___y_6170_);
v___x_6178_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_6178_, 0, v___y_6170_);
lean_ctor_set(v___x_6178_, 1, v___y_6166_);
lean_ctor_set(v___x_6178_, 2, v___y_6169_);
lean_ctor_set(v___x_6178_, 3, v___y_6172_);
lean_ctor_set(v___x_6178_, 4, v___x_6177_);
lean_ctor_set_uint8(v___x_6178_, sizeof(void*)*5, v___y_6171_);
lean_ctor_set_uint8(v___x_6178_, sizeof(void*)*5 + 1, v___y_6168_);
lean_ctor_set_uint8(v___x_6178_, sizeof(void*)*5 + 2, v_isSilent_6159_);
v___x_6179_ = lean_st_ref_take(v___y_6175_);
v_env_6180_ = lean_ctor_get(v___x_6179_, 0);
v_nextMacroScope_6181_ = lean_ctor_get(v___x_6179_, 1);
v_ngen_6182_ = lean_ctor_get(v___x_6179_, 2);
v_auxDeclNGen_6183_ = lean_ctor_get(v___x_6179_, 3);
v_traceState_6184_ = lean_ctor_get(v___x_6179_, 4);
v_cache_6185_ = lean_ctor_get(v___x_6179_, 5);
v_messages_6186_ = lean_ctor_get(v___x_6179_, 6);
v_infoState_6187_ = lean_ctor_get(v___x_6179_, 7);
v_snapshotTasks_6188_ = lean_ctor_get(v___x_6179_, 8);
v_isSharedCheck_6199_ = !lean_is_exclusive(v___x_6179_);
if (v_isSharedCheck_6199_ == 0)
{
v___x_6190_ = v___x_6179_;
v_isShared_6191_ = v_isSharedCheck_6199_;
goto v_resetjp_6189_;
}
else
{
lean_inc(v_snapshotTasks_6188_);
lean_inc(v_infoState_6187_);
lean_inc(v_messages_6186_);
lean_inc(v_cache_6185_);
lean_inc(v_traceState_6184_);
lean_inc(v_auxDeclNGen_6183_);
lean_inc(v_ngen_6182_);
lean_inc(v_nextMacroScope_6181_);
lean_inc(v_env_6180_);
lean_dec(v___x_6179_);
v___x_6190_ = lean_box(0);
v_isShared_6191_ = v_isSharedCheck_6199_;
goto v_resetjp_6189_;
}
v_resetjp_6189_:
{
lean_object* v___x_6192_; lean_object* v___x_6193_; lean_object* v___x_6195_; 
v___x_6192_ = lean_box(0);
v___x_6193_ = l_Lean_MessageLog_add(v___x_6178_, v_messages_6186_);
if (v_isShared_6191_ == 0)
{
lean_ctor_set(v___x_6190_, 6, v___x_6193_);
v___x_6195_ = v___x_6190_;
goto v_reusejp_6194_;
}
else
{
lean_object* v_reuseFailAlloc_6198_; 
v_reuseFailAlloc_6198_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6198_, 0, v_env_6180_);
lean_ctor_set(v_reuseFailAlloc_6198_, 1, v_nextMacroScope_6181_);
lean_ctor_set(v_reuseFailAlloc_6198_, 2, v_ngen_6182_);
lean_ctor_set(v_reuseFailAlloc_6198_, 3, v_auxDeclNGen_6183_);
lean_ctor_set(v_reuseFailAlloc_6198_, 4, v_traceState_6184_);
lean_ctor_set(v_reuseFailAlloc_6198_, 5, v_cache_6185_);
lean_ctor_set(v_reuseFailAlloc_6198_, 6, v___x_6193_);
lean_ctor_set(v_reuseFailAlloc_6198_, 7, v_infoState_6187_);
lean_ctor_set(v_reuseFailAlloc_6198_, 8, v_snapshotTasks_6188_);
v___x_6195_ = v_reuseFailAlloc_6198_;
goto v_reusejp_6194_;
}
v_reusejp_6194_:
{
lean_object* v___x_6196_; lean_object* v___x_6197_; 
v___x_6196_ = lean_st_ref_put(v___y_6175_, v___x_6195_);
v___x_6197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6197_, 0, v___x_6192_);
return v___x_6197_;
}
}
}
v___jp_6200_:
{
lean_object* v___x_6211_; lean_object* v___x_6212_; lean_object* v_a_6213_; lean_object* v___x_6215_; uint8_t v_isShared_6216_; uint8_t v_isSharedCheck_6226_; 
v___x_6211_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_6157_);
v___x_6212_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(v___x_6211_, v___y_6160_, v___y_6161_, v___y_6162_, v___y_6163_);
v_a_6213_ = lean_ctor_get(v___x_6212_, 0);
v_isSharedCheck_6226_ = !lean_is_exclusive(v___x_6212_);
if (v_isSharedCheck_6226_ == 0)
{
v___x_6215_ = v___x_6212_;
v_isShared_6216_ = v_isSharedCheck_6226_;
goto v_resetjp_6214_;
}
else
{
lean_inc(v_a_6213_);
lean_dec(v___x_6212_);
v___x_6215_ = lean_box(0);
v_isShared_6216_ = v_isSharedCheck_6226_;
goto v_resetjp_6214_;
}
v_resetjp_6214_:
{
lean_object* v___x_6217_; lean_object* v___x_6218_; lean_object* v___x_6219_; lean_object* v___x_6220_; 
lean_inc_ref_n(v___y_6206_, 2);
v___x_6217_ = l_Lean_FileMap_toPosition(v___y_6206_, v___y_6209_);
lean_dec(v___y_6209_);
v___x_6218_ = l_Lean_FileMap_toPosition(v___y_6206_, v___y_6210_);
lean_dec(v___y_6210_);
v___x_6219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6219_, 0, v___x_6218_);
v___x_6220_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___closed__0));
if (v___y_6204_ == 0)
{
lean_del_object(v___x_6215_);
lean_dec_ref(v___y_6203_);
v___y_6166_ = v___x_6217_;
v___y_6167_ = v_a_6213_;
v___y_6168_ = v___y_6205_;
v___y_6169_ = v___x_6219_;
v___y_6170_ = v___y_6207_;
v___y_6171_ = v___y_6208_;
v___y_6172_ = v___x_6220_;
v_currNamespace_6173_ = v___y_6201_;
v_openDecls_6174_ = v___y_6202_;
v___y_6175_ = v___y_6163_;
goto v___jp_6165_;
}
else
{
uint8_t v___x_6221_; 
lean_inc(v_a_6213_);
v___x_6221_ = l_Lean_MessageData_hasTag(v___y_6203_, v_a_6213_);
if (v___x_6221_ == 0)
{
lean_object* v___x_6222_; lean_object* v___x_6224_; 
lean_dec_ref_known(v___x_6219_, 1);
lean_dec_ref(v___x_6217_);
lean_dec(v_a_6213_);
v___x_6222_ = lean_box(0);
if (v_isShared_6216_ == 0)
{
lean_ctor_set(v___x_6215_, 0, v___x_6222_);
v___x_6224_ = v___x_6215_;
goto v_reusejp_6223_;
}
else
{
lean_object* v_reuseFailAlloc_6225_; 
v_reuseFailAlloc_6225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6225_, 0, v___x_6222_);
v___x_6224_ = v_reuseFailAlloc_6225_;
goto v_reusejp_6223_;
}
v_reusejp_6223_:
{
return v___x_6224_;
}
}
else
{
lean_del_object(v___x_6215_);
v___y_6166_ = v___x_6217_;
v___y_6167_ = v_a_6213_;
v___y_6168_ = v___y_6205_;
v___y_6169_ = v___x_6219_;
v___y_6170_ = v___y_6207_;
v___y_6171_ = v___y_6208_;
v___y_6172_ = v___x_6220_;
v_currNamespace_6173_ = v___y_6201_;
v_openDecls_6174_ = v___y_6202_;
v___y_6175_ = v___y_6163_;
goto v___jp_6165_;
}
}
}
}
v___jp_6227_:
{
lean_object* v___x_6238_; 
v___x_6238_ = l_Lean_Syntax_getTailPos_x3f(v___y_6232_, v___y_6236_);
lean_dec(v___y_6232_);
if (lean_obj_tag(v___x_6238_) == 0)
{
lean_inc(v___y_6237_);
v___y_6201_ = v___y_6228_;
v___y_6202_ = v___y_6229_;
v___y_6203_ = v___y_6230_;
v___y_6204_ = v___y_6231_;
v___y_6205_ = v___y_6233_;
v___y_6206_ = v___y_6234_;
v___y_6207_ = v___y_6235_;
v___y_6208_ = v___y_6236_;
v___y_6209_ = v___y_6237_;
v___y_6210_ = v___y_6237_;
goto v___jp_6200_;
}
else
{
lean_object* v_val_6239_; 
v_val_6239_ = lean_ctor_get(v___x_6238_, 0);
lean_inc(v_val_6239_);
lean_dec_ref_known(v___x_6238_, 1);
v___y_6201_ = v___y_6228_;
v___y_6202_ = v___y_6229_;
v___y_6203_ = v___y_6230_;
v___y_6204_ = v___y_6231_;
v___y_6205_ = v___y_6233_;
v___y_6206_ = v___y_6234_;
v___y_6207_ = v___y_6235_;
v___y_6208_ = v___y_6236_;
v___y_6209_ = v___y_6237_;
v___y_6210_ = v_val_6239_;
goto v___jp_6200_;
}
}
v___jp_6240_:
{
lean_object* v_ref_6250_; lean_object* v___x_6251_; 
v_ref_6250_ = l_Lean_replaceRef(v_ref_6156_, v___y_6248_);
v___x_6251_ = l_Lean_Syntax_getPos_x3f(v_ref_6250_, v___y_6247_);
if (lean_obj_tag(v___x_6251_) == 0)
{
lean_object* v___x_6252_; 
v___x_6252_ = lean_unsigned_to_nat(0u);
v___y_6228_ = v___y_6241_;
v___y_6229_ = v___y_6242_;
v___y_6230_ = v___y_6243_;
v___y_6231_ = v___y_6244_;
v___y_6232_ = v_ref_6250_;
v___y_6233_ = v___y_6249_;
v___y_6234_ = v___y_6245_;
v___y_6235_ = v___y_6246_;
v___y_6236_ = v___y_6247_;
v___y_6237_ = v___x_6252_;
goto v___jp_6227_;
}
else
{
lean_object* v_val_6253_; 
v_val_6253_ = lean_ctor_get(v___x_6251_, 0);
lean_inc(v_val_6253_);
lean_dec_ref_known(v___x_6251_, 1);
v___y_6228_ = v___y_6241_;
v___y_6229_ = v___y_6242_;
v___y_6230_ = v___y_6243_;
v___y_6231_ = v___y_6244_;
v___y_6232_ = v_ref_6250_;
v___y_6233_ = v___y_6249_;
v___y_6234_ = v___y_6245_;
v___y_6235_ = v___y_6246_;
v___y_6236_ = v___y_6247_;
v___y_6237_ = v_val_6253_;
goto v___jp_6227_;
}
}
v___jp_6255_:
{
if (v___y_6264_ == 0)
{
v___y_6241_ = v___y_6256_;
v___y_6242_ = v___y_6257_;
v___y_6243_ = v___y_6259_;
v___y_6244_ = v___y_6261_;
v___y_6245_ = v___y_6258_;
v___y_6246_ = v___y_6260_;
v___y_6247_ = v___y_6262_;
v___y_6248_ = v___y_6263_;
v___y_6249_ = v_severity_6158_;
goto v___jp_6240_;
}
else
{
v___y_6241_ = v___y_6256_;
v___y_6242_ = v___y_6257_;
v___y_6243_ = v___y_6259_;
v___y_6244_ = v___y_6261_;
v___y_6245_ = v___y_6258_;
v___y_6246_ = v___y_6260_;
v___y_6247_ = v___y_6262_;
v___y_6248_ = v___y_6263_;
v___y_6249_ = v___x_6254_;
goto v___jp_6240_;
}
}
v___jp_6265_:
{
if (v___y_6266_ == 0)
{
lean_object* v_toCold_6267_; lean_object* v_ref_6268_; uint8_t v_suppressElabErrors_6269_; lean_object* v_fileName_6270_; lean_object* v_fileMap_6271_; lean_object* v_options_6272_; lean_object* v_currNamespace_6273_; lean_object* v_openDecls_6274_; lean_object* v___x_6275_; lean_object* v___x_6276_; lean_object* v___f_6277_; uint8_t v___x_6278_; uint8_t v___x_6279_; 
v_toCold_6267_ = lean_ctor_get(v___y_6162_, 0);
v_ref_6268_ = lean_ctor_get(v___y_6162_, 2);
v_suppressElabErrors_6269_ = lean_ctor_get_uint8(v___y_6162_, sizeof(void*)*3 + 1);
v_fileName_6270_ = lean_ctor_get(v_toCold_6267_, 0);
v_fileMap_6271_ = lean_ctor_get(v_toCold_6267_, 1);
v_options_6272_ = lean_ctor_get(v_toCold_6267_, 2);
v_currNamespace_6273_ = lean_ctor_get(v_toCold_6267_, 4);
v_openDecls_6274_ = lean_ctor_get(v_toCold_6267_, 5);
v___x_6275_ = lean_box(v_suppressElabErrors_6269_);
v___x_6276_ = lean_box(v___y_6266_);
v___f_6277_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_6277_, 0, v___x_6275_);
lean_closure_set(v___f_6277_, 1, v___x_6276_);
v___x_6278_ = 1;
v___x_6279_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6158_, v___x_6278_);
if (v___x_6279_ == 0)
{
v___y_6256_ = v_currNamespace_6273_;
v___y_6257_ = v_openDecls_6274_;
v___y_6258_ = v_fileMap_6271_;
v___y_6259_ = v___f_6277_;
v___y_6260_ = v_fileName_6270_;
v___y_6261_ = v_suppressElabErrors_6269_;
v___y_6262_ = v___y_6266_;
v___y_6263_ = v_ref_6268_;
v___y_6264_ = v___x_6279_;
goto v___jp_6255_;
}
else
{
lean_object* v___x_6280_; uint8_t v___x_6281_; 
v___x_6280_ = l_Lean_warningAsError;
v___x_6281_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(v_options_6272_, v___x_6280_);
v___y_6256_ = v_currNamespace_6273_;
v___y_6257_ = v_openDecls_6274_;
v___y_6258_ = v_fileMap_6271_;
v___y_6259_ = v___f_6277_;
v___y_6260_ = v_fileName_6270_;
v___y_6261_ = v_suppressElabErrors_6269_;
v___y_6262_ = v___y_6266_;
v___y_6263_ = v_ref_6268_;
v___y_6264_ = v___x_6281_;
goto v___jp_6255_;
}
}
else
{
lean_object* v___x_6282_; lean_object* v___x_6283_; 
lean_dec_ref(v_msgData_6157_);
v___x_6282_ = lean_box(0);
v___x_6283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6283_, 0, v___x_6282_);
return v___x_6283_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___boxed(lean_object* v_ref_6286_, lean_object* v_msgData_6287_, lean_object* v_severity_6288_, lean_object* v_isSilent_6289_, lean_object* v___y_6290_, lean_object* v___y_6291_, lean_object* v___y_6292_, lean_object* v___y_6293_, lean_object* v___y_6294_){
_start:
{
uint8_t v_severity_boxed_6295_; uint8_t v_isSilent_boxed_6296_; lean_object* v_res_6297_; 
v_severity_boxed_6295_ = lean_unbox(v_severity_6288_);
v_isSilent_boxed_6296_ = lean_unbox(v_isSilent_6289_);
v_res_6297_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7(v_ref_6286_, v_msgData_6287_, v_severity_boxed_6295_, v_isSilent_boxed_6296_, v___y_6290_, v___y_6291_, v___y_6292_, v___y_6293_);
lean_dec(v___y_6293_);
lean_dec_ref(v___y_6292_);
lean_dec(v___y_6291_);
lean_dec_ref(v___y_6290_);
lean_dec(v_ref_6286_);
return v_res_6297_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3(lean_object* v_msgData_6298_, uint8_t v_severity_6299_, uint8_t v_isSilent_6300_, lean_object* v___y_6301_, lean_object* v___y_6302_, lean_object* v___y_6303_, lean_object* v___y_6304_){
_start:
{
lean_object* v_ref_6306_; lean_object* v___x_6307_; 
v_ref_6306_ = lean_ctor_get(v___y_6303_, 2);
v___x_6307_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7(v_ref_6306_, v_msgData_6298_, v_severity_6299_, v_isSilent_6300_, v___y_6301_, v___y_6302_, v___y_6303_, v___y_6304_);
return v___x_6307_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_msgData_6308_, lean_object* v_severity_6309_, lean_object* v_isSilent_6310_, lean_object* v___y_6311_, lean_object* v___y_6312_, lean_object* v___y_6313_, lean_object* v___y_6314_, lean_object* v___y_6315_){
_start:
{
uint8_t v_severity_boxed_6316_; uint8_t v_isSilent_boxed_6317_; lean_object* v_res_6318_; 
v_severity_boxed_6316_ = lean_unbox(v_severity_6309_);
v_isSilent_boxed_6317_ = lean_unbox(v_isSilent_6310_);
v_res_6318_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3(v_msgData_6308_, v_severity_boxed_6316_, v_isSilent_boxed_6317_, v___y_6311_, v___y_6312_, v___y_6313_, v___y_6314_);
lean_dec(v___y_6314_);
lean_dec_ref(v___y_6313_);
lean_dec(v___y_6312_);
lean_dec_ref(v___y_6311_);
return v_res_6318_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2(lean_object* v_msgData_6319_, lean_object* v___y_6320_, lean_object* v___y_6321_, lean_object* v___y_6322_, lean_object* v___y_6323_){
_start:
{
uint8_t v___x_6325_; uint8_t v___x_6326_; lean_object* v___x_6327_; 
v___x_6325_ = 2;
v___x_6326_ = 0;
v___x_6327_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3(v_msgData_6319_, v___x_6325_, v___x_6326_, v___y_6320_, v___y_6321_, v___y_6322_, v___y_6323_);
return v___x_6327_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_6328_, lean_object* v___y_6329_, lean_object* v___y_6330_, lean_object* v___y_6331_, lean_object* v___y_6332_, lean_object* v___y_6333_){
_start:
{
lean_object* v_res_6334_; 
v_res_6334_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2(v_msgData_6328_, v___y_6329_, v___y_6330_, v___y_6331_, v___y_6332_);
lean_dec(v___y_6332_);
lean_dec_ref(v___y_6331_);
lean_dec(v___y_6330_);
lean_dec_ref(v___y_6329_);
return v_res_6334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0(lean_object* v_f_6335_, lean_object* v___y_6336_, lean_object* v___y_6337_, lean_object* v___y_6338_, lean_object* v___y_6339_){
_start:
{
lean_object* v_module_6341_; lean_object* v_const_6342_; lean_object* v_exception_6343_; lean_object* v___x_6344_; lean_object* v___x_6345_; lean_object* v___x_6346_; lean_object* v___x_6347_; lean_object* v___x_6348_; lean_object* v___x_6349_; lean_object* v___x_6350_; lean_object* v___x_6351_; lean_object* v___x_6352_; lean_object* v___x_6353_; lean_object* v___x_6354_; lean_object* v___x_6355_; 
v_module_6341_ = lean_ctor_get(v_f_6335_, 0);
lean_inc(v_module_6341_);
v_const_6342_ = lean_ctor_get(v_f_6335_, 1);
lean_inc(v_const_6342_);
v_exception_6343_ = lean_ctor_get(v_f_6335_, 2);
lean_inc_ref(v_exception_6343_);
lean_dec_ref(v_f_6335_);
v___x_6344_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1);
v___x_6345_ = l_Lean_MessageData_ofName(v_const_6342_);
v___x_6346_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6346_, 0, v___x_6344_);
lean_ctor_set(v___x_6346_, 1, v___x_6345_);
v___x_6347_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3);
v___x_6348_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6348_, 0, v___x_6346_);
lean_ctor_set(v___x_6348_, 1, v___x_6347_);
v___x_6349_ = l_Lean_MessageData_ofName(v_module_6341_);
v___x_6350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6350_, 0, v___x_6348_);
lean_ctor_set(v___x_6350_, 1, v___x_6349_);
v___x_6351_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5);
v___x_6352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6352_, 0, v___x_6350_);
lean_ctor_set(v___x_6352_, 1, v___x_6351_);
v___x_6353_ = l_Lean_Exception_toMessageData(v_exception_6343_);
v___x_6354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6354_, 0, v___x_6352_);
lean_ctor_set(v___x_6354_, 1, v___x_6353_);
v___x_6355_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2(v___x_6354_, v___y_6336_, v___y_6337_, v___y_6338_, v___y_6339_);
return v___x_6355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0___boxed(lean_object* v_f_6356_, lean_object* v___y_6357_, lean_object* v___y_6358_, lean_object* v___y_6359_, lean_object* v___y_6360_, lean_object* v___y_6361_){
_start:
{
lean_object* v_res_6362_; 
v_res_6362_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0(v_f_6356_, v___y_6357_, v___y_6358_, v___y_6359_, v___y_6360_);
lean_dec(v___y_6360_);
lean_dec_ref(v___y_6359_);
lean_dec(v___y_6358_);
lean_dec_ref(v___y_6357_);
return v_res_6362_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3(lean_object* v_as_6363_, size_t v_i_6364_, size_t v_stop_6365_, lean_object* v_b_6366_, lean_object* v___y_6367_, lean_object* v___y_6368_, lean_object* v___y_6369_, lean_object* v___y_6370_){
_start:
{
uint8_t v___x_6372_; 
v___x_6372_ = lean_usize_dec_eq(v_i_6364_, v_stop_6365_);
if (v___x_6372_ == 0)
{
lean_object* v___x_6373_; lean_object* v___x_6374_; 
v___x_6373_ = lean_array_uget_borrowed(v_as_6363_, v_i_6364_);
lean_inc(v___x_6373_);
v___x_6374_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0(v___x_6373_, v___y_6367_, v___y_6368_, v___y_6369_, v___y_6370_);
if (lean_obj_tag(v___x_6374_) == 0)
{
lean_object* v_a_6375_; size_t v___x_6376_; size_t v___x_6377_; 
v_a_6375_ = lean_ctor_get(v___x_6374_, 0);
lean_inc(v_a_6375_);
lean_dec_ref_known(v___x_6374_, 1);
v___x_6376_ = ((size_t)1ULL);
v___x_6377_ = lean_usize_add(v_i_6364_, v___x_6376_);
v_i_6364_ = v___x_6377_;
v_b_6366_ = v_a_6375_;
goto _start;
}
else
{
return v___x_6374_;
}
}
else
{
lean_object* v___x_6379_; 
v___x_6379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6379_, 0, v_b_6366_);
return v___x_6379_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3___boxed(lean_object* v_as_6380_, lean_object* v_i_6381_, lean_object* v_stop_6382_, lean_object* v_b_6383_, lean_object* v___y_6384_, lean_object* v___y_6385_, lean_object* v___y_6386_, lean_object* v___y_6387_, lean_object* v___y_6388_){
_start:
{
size_t v_i_boxed_6389_; size_t v_stop_boxed_6390_; lean_object* v_res_6391_; 
v_i_boxed_6389_ = lean_unbox_usize(v_i_6381_);
lean_dec(v_i_6381_);
v_stop_boxed_6390_ = lean_unbox_usize(v_stop_6382_);
lean_dec(v_stop_6382_);
v_res_6391_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3(v_as_6380_, v_i_boxed_6389_, v_stop_boxed_6390_, v_b_6383_, v___y_6384_, v___y_6385_, v___y_6386_, v___y_6387_);
lean_dec(v___y_6387_);
lean_dec_ref(v___y_6386_);
lean_dec(v___y_6385_);
lean_dec_ref(v___y_6384_);
lean_dec_ref(v_as_6380_);
return v_res_6391_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(lean_object* v_as_6392_, size_t v_i_6393_, size_t v_stop_6394_, lean_object* v_b_6395_){
_start:
{
uint8_t v___x_6396_; 
v___x_6396_ = lean_usize_dec_eq(v_i_6393_, v_stop_6394_);
if (v___x_6396_ == 0)
{
lean_object* v___x_6397_; lean_object* v___x_6398_; lean_object* v___x_6399_; size_t v___x_6400_; size_t v___x_6401_; 
v___x_6397_ = lean_array_uget_borrowed(v_as_6392_, v_i_6393_);
lean_inc(v___x_6397_);
v___x_6398_ = lean_task_get_own(v___x_6397_);
v___x_6399_ = l_Lean_Meta_LazyDiscrTree_InitResults_append___redArg(v_b_6395_, v___x_6398_);
v___x_6400_ = ((size_t)1ULL);
v___x_6401_ = lean_usize_add(v_i_6393_, v___x_6400_);
v_i_6393_ = v___x_6401_;
v_b_6395_ = v___x_6399_;
goto _start;
}
else
{
return v_b_6395_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_as_6403_, lean_object* v_i_6404_, lean_object* v_stop_6405_, lean_object* v_b_6406_){
_start:
{
size_t v_i_boxed_6407_; size_t v_stop_boxed_6408_; lean_object* v_res_6409_; 
v_i_boxed_6407_ = lean_unbox_usize(v_i_6404_);
lean_dec(v_i_6404_);
v_stop_boxed_6408_ = lean_unbox_usize(v_stop_6405_);
lean_dec(v_stop_6405_);
v_res_6409_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(v_as_6403_, v_i_boxed_6407_, v_stop_boxed_6408_, v_b_6406_);
lean_dec_ref(v_as_6403_);
return v_res_6409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(lean_object* v_z_6410_, lean_object* v_tasks_6411_){
_start:
{
lean_object* v___x_6412_; lean_object* v___x_6413_; uint8_t v___x_6414_; 
v___x_6412_ = lean_unsigned_to_nat(0u);
v___x_6413_ = lean_array_get_size(v_tasks_6411_);
v___x_6414_ = lean_nat_dec_lt(v___x_6412_, v___x_6413_);
if (v___x_6414_ == 0)
{
return v_z_6410_;
}
else
{
size_t v___x_6415_; size_t v___x_6416_; lean_object* v___x_6417_; 
v___x_6415_ = ((size_t)0ULL);
v___x_6416_ = lean_usize_of_nat(v___x_6413_);
v___x_6417_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(v_tasks_6411_, v___x_6415_, v___x_6416_, v_z_6410_);
return v___x_6417_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg___boxed(lean_object* v_z_6418_, lean_object* v_tasks_6419_){
_start:
{
lean_object* v_res_6420_; 
v_res_6420_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(v_z_6418_, v_tasks_6419_);
lean_dec_ref(v_tasks_6419_);
return v_res_6420_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_6421_; lean_object* v___x_6422_; lean_object* v___x_6423_; 
v___x_6421_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
v___x_6422_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2);
v___x_6423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6423_, 0, v___x_6422_);
lean_ctor_set(v___x_6423_, 1, v___x_6421_);
return v___x_6423_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_6424_; lean_object* v___x_6425_; lean_object* v___x_6426_; 
v___x_6424_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
v___x_6425_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0);
v___x_6426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6426_, 0, v___x_6425_);
lean_ctor_set(v___x_6426_, 1, v___x_6424_);
return v___x_6426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(lean_object* v_cctx_6427_, lean_object* v_ngen_6428_, lean_object* v_env_6429_, lean_object* v_act_6430_, lean_object* v_constantsPerTask_6431_, lean_object* v___y_6432_, lean_object* v___y_6433_, lean_object* v___y_6434_, lean_object* v___y_6435_){
_start:
{
lean_object* v___x_6437_; lean_object* v_moduleData_6438_; lean_object* v_n_6439_; lean_object* v___x_6440_; lean_object* v___x_6441_; lean_object* v___x_6442_; lean_object* v_a_6443_; lean_object* v___x_6445_; uint8_t v_isShared_6446_; uint8_t v_isSharedCheck_6478_; 
v___x_6437_ = l_Lean_Environment_header(v_env_6429_);
v_moduleData_6438_ = lean_ctor_get(v___x_6437_, 6);
lean_inc_ref(v_moduleData_6438_);
lean_dec_ref(v___x_6437_);
v_n_6439_ = lean_array_get_size(v_moduleData_6438_);
lean_dec_ref(v_moduleData_6438_);
v___x_6440_ = lean_unsigned_to_nat(0u);
v___x_6441_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
v___x_6442_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(v_cctx_6427_, v_env_6429_, v_act_6430_, v_constantsPerTask_6431_, v_n_6439_, v_ngen_6428_, v___x_6441_, v___x_6440_, v___x_6440_, v___x_6440_);
v_a_6443_ = lean_ctor_get(v___x_6442_, 0);
v_isSharedCheck_6478_ = !lean_is_exclusive(v___x_6442_);
if (v_isSharedCheck_6478_ == 0)
{
v___x_6445_ = v___x_6442_;
v_isShared_6446_ = v_isSharedCheck_6478_;
goto v_resetjp_6444_;
}
else
{
lean_inc(v_a_6443_);
lean_dec(v___x_6442_);
v___x_6445_ = lean_box(0);
v_isShared_6446_ = v_isSharedCheck_6478_;
goto v_resetjp_6444_;
}
v_resetjp_6444_:
{
lean_object* v___x_6447_; lean_object* v_r_6448_; lean_object* v_tree_6449_; lean_object* v_errors_6450_; lean_object* v___x_6451_; uint8_t v___x_6452_; 
v___x_6447_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1);
v_r_6448_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(v___x_6447_, v_a_6443_);
lean_dec(v_a_6443_);
v_tree_6449_ = lean_ctor_get(v_r_6448_, 0);
lean_inc_ref(v_tree_6449_);
v_errors_6450_ = lean_ctor_get(v_r_6448_, 1);
lean_inc_ref(v_errors_6450_);
lean_dec_ref(v_r_6448_);
v___x_6451_ = lean_array_get_size(v_errors_6450_);
v___x_6452_ = lean_nat_dec_lt(v___x_6440_, v___x_6451_);
if (v___x_6452_ == 0)
{
lean_object* v___x_6453_; lean_object* v___x_6455_; 
lean_dec_ref(v_errors_6450_);
v___x_6453_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_tree_6449_);
if (v_isShared_6446_ == 0)
{
lean_ctor_set(v___x_6445_, 0, v___x_6453_);
v___x_6455_ = v___x_6445_;
goto v_reusejp_6454_;
}
else
{
lean_object* v_reuseFailAlloc_6456_; 
v_reuseFailAlloc_6456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6456_, 0, v___x_6453_);
v___x_6455_ = v_reuseFailAlloc_6456_;
goto v_reusejp_6454_;
}
v_reusejp_6454_:
{
return v___x_6455_;
}
}
else
{
lean_object* v___x_6457_; size_t v___x_6458_; size_t v___x_6459_; lean_object* v___x_6460_; 
lean_del_object(v___x_6445_);
v___x_6457_ = lean_box(0);
v___x_6458_ = ((size_t)0ULL);
v___x_6459_ = lean_usize_of_nat(v___x_6451_);
v___x_6460_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3(v_errors_6450_, v___x_6458_, v___x_6459_, v___x_6457_, v___y_6432_, v___y_6433_, v___y_6434_, v___y_6435_);
lean_dec_ref(v_errors_6450_);
if (lean_obj_tag(v___x_6460_) == 0)
{
lean_object* v___x_6462_; uint8_t v_isShared_6463_; uint8_t v_isSharedCheck_6468_; 
v_isSharedCheck_6468_ = !lean_is_exclusive(v___x_6460_);
if (v_isSharedCheck_6468_ == 0)
{
lean_object* v_unused_6469_; 
v_unused_6469_ = lean_ctor_get(v___x_6460_, 0);
lean_dec(v_unused_6469_);
v___x_6462_ = v___x_6460_;
v_isShared_6463_ = v_isSharedCheck_6468_;
goto v_resetjp_6461_;
}
else
{
lean_dec(v___x_6460_);
v___x_6462_ = lean_box(0);
v_isShared_6463_ = v_isSharedCheck_6468_;
goto v_resetjp_6461_;
}
v_resetjp_6461_:
{
lean_object* v___x_6464_; lean_object* v___x_6466_; 
v___x_6464_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_tree_6449_);
if (v_isShared_6463_ == 0)
{
lean_ctor_set(v___x_6462_, 0, v___x_6464_);
v___x_6466_ = v___x_6462_;
goto v_reusejp_6465_;
}
else
{
lean_object* v_reuseFailAlloc_6467_; 
v_reuseFailAlloc_6467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6467_, 0, v___x_6464_);
v___x_6466_ = v_reuseFailAlloc_6467_;
goto v_reusejp_6465_;
}
v_reusejp_6465_:
{
return v___x_6466_;
}
}
}
else
{
lean_object* v_a_6470_; lean_object* v___x_6472_; uint8_t v_isShared_6473_; uint8_t v_isSharedCheck_6477_; 
lean_dec_ref(v_tree_6449_);
v_a_6470_ = lean_ctor_get(v___x_6460_, 0);
v_isSharedCheck_6477_ = !lean_is_exclusive(v___x_6460_);
if (v_isSharedCheck_6477_ == 0)
{
v___x_6472_ = v___x_6460_;
v_isShared_6473_ = v_isSharedCheck_6477_;
goto v_resetjp_6471_;
}
else
{
lean_inc(v_a_6470_);
lean_dec(v___x_6460_);
v___x_6472_ = lean_box(0);
v_isShared_6473_ = v_isSharedCheck_6477_;
goto v_resetjp_6471_;
}
v_resetjp_6471_:
{
lean_object* v___x_6475_; 
if (v_isShared_6473_ == 0)
{
v___x_6475_ = v___x_6472_;
goto v_reusejp_6474_;
}
else
{
lean_object* v_reuseFailAlloc_6476_; 
v_reuseFailAlloc_6476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6476_, 0, v_a_6470_);
v___x_6475_ = v_reuseFailAlloc_6476_;
goto v_reusejp_6474_;
}
v_reusejp_6474_:
{
return v___x_6475_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___boxed(lean_object* v_cctx_6479_, lean_object* v_ngen_6480_, lean_object* v_env_6481_, lean_object* v_act_6482_, lean_object* v_constantsPerTask_6483_, lean_object* v___y_6484_, lean_object* v___y_6485_, lean_object* v___y_6486_, lean_object* v___y_6487_, lean_object* v___y_6488_){
_start:
{
lean_object* v_res_6489_; 
v_res_6489_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(v_cctx_6479_, v_ngen_6480_, v_env_6481_, v_act_6482_, v_constantsPerTask_6483_, v___y_6484_, v___y_6485_, v___y_6486_, v___y_6487_);
lean_dec(v___y_6487_);
lean_dec_ref(v___y_6486_);
lean_dec(v___y_6485_);
lean_dec_ref(v___y_6484_);
lean_dec(v_constantsPerTask_6483_);
return v_res_6489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0(lean_object* v_a_6490_, lean_object* v___x_6491_, lean_object* v_addEntry_6492_, lean_object* v_constantsPerTask_6493_, lean_object* v_droppedEntriesRef_6494_, lean_object* v_droppedKeys_6495_, lean_object* v___y_6496_, lean_object* v___y_6497_, lean_object* v___y_6498_, lean_object* v___y_6499_){
_start:
{
lean_object* v___x_6501_; lean_object* v_env_6502_; lean_object* v___x_6503_; lean_object* v___x_6504_; 
v___x_6501_ = lean_st_ref_get(v___y_6499_);
v_env_6502_ = lean_ctor_get(v___x_6501_, 0);
lean_inc_ref(v_env_6502_);
lean_dec(v___x_6501_);
lean_inc_ref(v_a_6490_);
v___x_6503_ = l_Lean_Meta_LazyDiscrTree_createTreeCtx(v_a_6490_);
v___x_6504_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(v___x_6503_, v___x_6491_, v_env_6502_, v_addEntry_6492_, v_constantsPerTask_6493_, v___y_6496_, v___y_6497_, v___y_6498_, v___y_6499_);
if (lean_obj_tag(v___x_6504_) == 0)
{
if (lean_obj_tag(v_droppedEntriesRef_6494_) == 1)
{
lean_object* v_a_6505_; lean_object* v_val_6506_; lean_object* v___x_6508_; uint8_t v_isShared_6509_; uint8_t v_isSharedCheck_6539_; 
v_a_6505_ = lean_ctor_get(v___x_6504_, 0);
lean_inc(v_a_6505_);
lean_dec_ref_known(v___x_6504_, 1);
v_val_6506_ = lean_ctor_get(v_droppedEntriesRef_6494_, 0);
v_isSharedCheck_6539_ = !lean_is_exclusive(v_droppedEntriesRef_6494_);
if (v_isSharedCheck_6539_ == 0)
{
v___x_6508_ = v_droppedEntriesRef_6494_;
v_isShared_6509_ = v_isSharedCheck_6539_;
goto v_resetjp_6507_;
}
else
{
lean_inc(v_val_6506_);
lean_dec(v_droppedEntriesRef_6494_);
v___x_6508_ = lean_box(0);
v_isShared_6509_ = v_isSharedCheck_6539_;
goto v_resetjp_6507_;
}
v_resetjp_6507_:
{
lean_object* v___x_6510_; 
v___x_6510_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_a_6505_, v_droppedKeys_6495_, v___y_6496_, v___y_6497_, v___y_6498_, v___y_6499_);
lean_dec(v_droppedKeys_6495_);
if (lean_obj_tag(v___x_6510_) == 0)
{
lean_object* v_a_6511_; lean_object* v___x_6513_; uint8_t v_isShared_6514_; uint8_t v_isSharedCheck_6530_; 
v_a_6511_ = lean_ctor_get(v___x_6510_, 0);
v_isSharedCheck_6530_ = !lean_is_exclusive(v___x_6510_);
if (v_isSharedCheck_6530_ == 0)
{
v___x_6513_ = v___x_6510_;
v_isShared_6514_ = v_isSharedCheck_6530_;
goto v_resetjp_6512_;
}
else
{
lean_inc(v_a_6511_);
lean_dec(v___x_6510_);
v___x_6513_ = lean_box(0);
v_isShared_6514_ = v_isSharedCheck_6530_;
goto v_resetjp_6512_;
}
v_resetjp_6512_:
{
lean_object* v_fst_6515_; lean_object* v_snd_6516_; lean_object* v___x_6517_; lean_object* v___y_6519_; 
v_fst_6515_ = lean_ctor_get(v_a_6511_, 0);
lean_inc(v_fst_6515_);
v_snd_6516_ = lean_ctor_get(v_a_6511_, 1);
lean_inc(v_snd_6516_);
lean_dec(v_a_6511_);
v___x_6517_ = lean_st_ref_get(v_val_6506_);
if (lean_obj_tag(v___x_6517_) == 0)
{
lean_object* v___x_6528_; 
v___x_6528_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___y_6519_ = v___x_6528_;
goto v___jp_6518_;
}
else
{
lean_object* v_val_6529_; 
v_val_6529_ = lean_ctor_get(v___x_6517_, 0);
lean_inc(v_val_6529_);
lean_dec_ref_known(v___x_6517_, 1);
v___y_6519_ = v_val_6529_;
goto v___jp_6518_;
}
v___jp_6518_:
{
lean_object* v___x_6520_; lean_object* v___x_6522_; 
v___x_6520_ = l_Array_append___redArg(v___y_6519_, v_fst_6515_);
lean_dec(v_fst_6515_);
if (v_isShared_6509_ == 0)
{
lean_ctor_set(v___x_6508_, 0, v___x_6520_);
v___x_6522_ = v___x_6508_;
goto v_reusejp_6521_;
}
else
{
lean_object* v_reuseFailAlloc_6527_; 
v_reuseFailAlloc_6527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6527_, 0, v___x_6520_);
v___x_6522_ = v_reuseFailAlloc_6527_;
goto v_reusejp_6521_;
}
v_reusejp_6521_:
{
lean_object* v___x_6523_; lean_object* v___x_6525_; 
v___x_6523_ = lean_st_ref_swap(v_val_6506_, v___x_6522_);
lean_dec(v_val_6506_);
lean_dec(v___x_6523_);
if (v_isShared_6514_ == 0)
{
lean_ctor_set(v___x_6513_, 0, v_snd_6516_);
v___x_6525_ = v___x_6513_;
goto v_reusejp_6524_;
}
else
{
lean_object* v_reuseFailAlloc_6526_; 
v_reuseFailAlloc_6526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6526_, 0, v_snd_6516_);
v___x_6525_ = v_reuseFailAlloc_6526_;
goto v_reusejp_6524_;
}
v_reusejp_6524_:
{
return v___x_6525_;
}
}
}
}
}
else
{
lean_object* v_a_6531_; lean_object* v___x_6533_; uint8_t v_isShared_6534_; uint8_t v_isSharedCheck_6538_; 
lean_del_object(v___x_6508_);
lean_dec(v_val_6506_);
v_a_6531_ = lean_ctor_get(v___x_6510_, 0);
v_isSharedCheck_6538_ = !lean_is_exclusive(v___x_6510_);
if (v_isSharedCheck_6538_ == 0)
{
v___x_6533_ = v___x_6510_;
v_isShared_6534_ = v_isSharedCheck_6538_;
goto v_resetjp_6532_;
}
else
{
lean_inc(v_a_6531_);
lean_dec(v___x_6510_);
v___x_6533_ = lean_box(0);
v_isShared_6534_ = v_isSharedCheck_6538_;
goto v_resetjp_6532_;
}
v_resetjp_6532_:
{
lean_object* v___x_6536_; 
if (v_isShared_6534_ == 0)
{
v___x_6536_ = v___x_6533_;
goto v_reusejp_6535_;
}
else
{
lean_object* v_reuseFailAlloc_6537_; 
v_reuseFailAlloc_6537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6537_, 0, v_a_6531_);
v___x_6536_ = v_reuseFailAlloc_6537_;
goto v_reusejp_6535_;
}
v_reusejp_6535_:
{
return v___x_6536_;
}
}
}
}
}
else
{
lean_object* v_a_6540_; lean_object* v___x_6541_; 
lean_dec(v_droppedEntriesRef_6494_);
v_a_6540_ = lean_ctor_get(v___x_6504_, 0);
lean_inc(v_a_6540_);
lean_dec_ref_known(v___x_6504_, 1);
v___x_6541_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_a_6540_, v_droppedKeys_6495_, v___y_6496_, v___y_6497_, v___y_6498_, v___y_6499_);
return v___x_6541_;
}
}
else
{
lean_dec(v_droppedKeys_6495_);
lean_dec(v_droppedEntriesRef_6494_);
return v___x_6504_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0___boxed(lean_object* v_a_6542_, lean_object* v___x_6543_, lean_object* v_addEntry_6544_, lean_object* v_constantsPerTask_6545_, lean_object* v_droppedEntriesRef_6546_, lean_object* v_droppedKeys_6547_, lean_object* v___y_6548_, lean_object* v___y_6549_, lean_object* v___y_6550_, lean_object* v___y_6551_, lean_object* v___y_6552_){
_start:
{
lean_object* v_res_6553_; 
v_res_6553_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0(v_a_6542_, v___x_6543_, v_addEntry_6544_, v_constantsPerTask_6545_, v_droppedEntriesRef_6546_, v_droppedKeys_6547_, v___y_6548_, v___y_6549_, v___y_6550_, v___y_6551_);
lean_dec(v___y_6551_);
lean_dec_ref(v___y_6550_);
lean_dec(v___y_6549_);
lean_dec_ref(v___y_6548_);
lean_dec(v_constantsPerTask_6545_);
lean_dec_ref(v_a_6542_);
return v_res_6553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(lean_object* v_ref_6555_, lean_object* v_addEntry_6556_, lean_object* v_droppedKeys_6557_, lean_object* v_constantsPerTask_6558_, lean_object* v_droppedEntriesRef_6559_, lean_object* v_ty_6560_, lean_object* v_a_6561_, lean_object* v_a_6562_, lean_object* v_a_6563_, lean_object* v_a_6564_){
_start:
{
lean_object* v_a_6567_; lean_object* v___x_6589_; lean_object* v_ngen_6590_; lean_object* v_namePrefix_6591_; lean_object* v_idx_6592_; lean_object* v___x_6594_; uint8_t v_isShared_6595_; uint8_t v_isSharedCheck_6638_; 
v___x_6589_ = lean_st_ref_get(v_a_6564_);
v_ngen_6590_ = lean_ctor_get(v___x_6589_, 2);
lean_inc_ref(v_ngen_6590_);
lean_dec(v___x_6589_);
v_namePrefix_6591_ = lean_ctor_get(v_ngen_6590_, 0);
v_idx_6592_ = lean_ctor_get(v_ngen_6590_, 1);
v_isSharedCheck_6638_ = !lean_is_exclusive(v_ngen_6590_);
if (v_isSharedCheck_6638_ == 0)
{
v___x_6594_ = v_ngen_6590_;
v_isShared_6595_ = v_isSharedCheck_6638_;
goto v_resetjp_6593_;
}
else
{
lean_inc(v_idx_6592_);
lean_inc(v_namePrefix_6591_);
lean_dec(v_ngen_6590_);
v___x_6594_ = lean_box(0);
v_isShared_6595_ = v_isSharedCheck_6638_;
goto v_resetjp_6593_;
}
v___jp_6566_:
{
lean_object* v___x_6568_; 
v___x_6568_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v_a_6567_, v_ty_6560_, v_a_6561_, v_a_6562_, v_a_6563_, v_a_6564_);
if (lean_obj_tag(v___x_6568_) == 0)
{
lean_object* v_a_6569_; lean_object* v___x_6571_; uint8_t v_isShared_6572_; uint8_t v_isSharedCheck_6580_; 
v_a_6569_ = lean_ctor_get(v___x_6568_, 0);
v_isSharedCheck_6580_ = !lean_is_exclusive(v___x_6568_);
if (v_isSharedCheck_6580_ == 0)
{
v___x_6571_ = v___x_6568_;
v_isShared_6572_ = v_isSharedCheck_6580_;
goto v_resetjp_6570_;
}
else
{
lean_inc(v_a_6569_);
lean_dec(v___x_6568_);
v___x_6571_ = lean_box(0);
v_isShared_6572_ = v_isSharedCheck_6580_;
goto v_resetjp_6570_;
}
v_resetjp_6570_:
{
lean_object* v_fst_6573_; lean_object* v_snd_6574_; lean_object* v___x_6575_; lean_object* v___x_6576_; lean_object* v___x_6578_; 
v_fst_6573_ = lean_ctor_get(v_a_6569_, 0);
lean_inc(v_fst_6573_);
v_snd_6574_ = lean_ctor_get(v_a_6569_, 1);
lean_inc(v_snd_6574_);
lean_dec(v_a_6569_);
v___x_6575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6575_, 0, v_snd_6574_);
v___x_6576_ = lean_st_ref_swap(v_ref_6555_, v___x_6575_);
lean_dec(v___x_6576_);
if (v_isShared_6572_ == 0)
{
lean_ctor_set(v___x_6571_, 0, v_fst_6573_);
v___x_6578_ = v___x_6571_;
goto v_reusejp_6577_;
}
else
{
lean_object* v_reuseFailAlloc_6579_; 
v_reuseFailAlloc_6579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6579_, 0, v_fst_6573_);
v___x_6578_ = v_reuseFailAlloc_6579_;
goto v_reusejp_6577_;
}
v_reusejp_6577_:
{
return v___x_6578_;
}
}
}
else
{
lean_object* v_a_6581_; lean_object* v___x_6583_; uint8_t v_isShared_6584_; uint8_t v_isSharedCheck_6588_; 
v_a_6581_ = lean_ctor_get(v___x_6568_, 0);
v_isSharedCheck_6588_ = !lean_is_exclusive(v___x_6568_);
if (v_isSharedCheck_6588_ == 0)
{
v___x_6583_ = v___x_6568_;
v_isShared_6584_ = v_isSharedCheck_6588_;
goto v_resetjp_6582_;
}
else
{
lean_inc(v_a_6581_);
lean_dec(v___x_6568_);
v___x_6583_ = lean_box(0);
v_isShared_6584_ = v_isSharedCheck_6588_;
goto v_resetjp_6582_;
}
v_resetjp_6582_:
{
lean_object* v___x_6586_; 
if (v_isShared_6584_ == 0)
{
v___x_6586_ = v___x_6583_;
goto v_reusejp_6585_;
}
else
{
lean_object* v_reuseFailAlloc_6587_; 
v_reuseFailAlloc_6587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6587_, 0, v_a_6581_);
v___x_6586_ = v_reuseFailAlloc_6587_;
goto v_reusejp_6585_;
}
v_reusejp_6585_:
{
return v___x_6586_;
}
}
}
}
v_resetjp_6593_:
{
lean_object* v___x_6596_; lean_object* v___x_6597_; lean_object* v___x_6599_; 
lean_inc(v_idx_6592_);
lean_inc(v_namePrefix_6591_);
v___x_6596_ = l_Lean_Name_num___override(v_namePrefix_6591_, v_idx_6592_);
v___x_6597_ = lean_unsigned_to_nat(1u);
if (v_isShared_6595_ == 0)
{
lean_ctor_set(v___x_6594_, 1, v___x_6597_);
lean_ctor_set(v___x_6594_, 0, v___x_6596_);
v___x_6599_ = v___x_6594_;
goto v_reusejp_6598_;
}
else
{
lean_object* v_reuseFailAlloc_6637_; 
v_reuseFailAlloc_6637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6637_, 0, v___x_6596_);
lean_ctor_set(v_reuseFailAlloc_6637_, 1, v___x_6597_);
v___x_6599_ = v_reuseFailAlloc_6637_;
goto v_reusejp_6598_;
}
v_reusejp_6598_:
{
lean_object* v___f_6600_; lean_object* v___x_6601_; lean_object* v___x_6602_; lean_object* v___x_6603_; lean_object* v_env_6604_; lean_object* v_nextMacroScope_6605_; lean_object* v_auxDeclNGen_6606_; lean_object* v_traceState_6607_; lean_object* v_cache_6608_; lean_object* v_messages_6609_; lean_object* v_infoState_6610_; lean_object* v_snapshotTasks_6611_; lean_object* v___x_6613_; uint8_t v_isShared_6614_; uint8_t v_isSharedCheck_6635_; 
lean_inc_ref(v_a_6563_);
v___f_6600_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_6600_, 0, v_a_6563_);
lean_closure_set(v___f_6600_, 1, v___x_6599_);
lean_closure_set(v___f_6600_, 2, v_addEntry_6556_);
lean_closure_set(v___f_6600_, 3, v_constantsPerTask_6558_);
lean_closure_set(v___f_6600_, 4, v_droppedEntriesRef_6559_);
lean_closure_set(v___f_6600_, 5, v_droppedKeys_6557_);
v___x_6601_ = lean_nat_add(v_idx_6592_, v___x_6597_);
lean_dec(v_idx_6592_);
v___x_6602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6602_, 0, v_namePrefix_6591_);
lean_ctor_set(v___x_6602_, 1, v___x_6601_);
v___x_6603_ = lean_st_ref_take(v_a_6564_);
v_env_6604_ = lean_ctor_get(v___x_6603_, 0);
v_nextMacroScope_6605_ = lean_ctor_get(v___x_6603_, 1);
v_auxDeclNGen_6606_ = lean_ctor_get(v___x_6603_, 3);
v_traceState_6607_ = lean_ctor_get(v___x_6603_, 4);
v_cache_6608_ = lean_ctor_get(v___x_6603_, 5);
v_messages_6609_ = lean_ctor_get(v___x_6603_, 6);
v_infoState_6610_ = lean_ctor_get(v___x_6603_, 7);
v_snapshotTasks_6611_ = lean_ctor_get(v___x_6603_, 8);
v_isSharedCheck_6635_ = !lean_is_exclusive(v___x_6603_);
if (v_isSharedCheck_6635_ == 0)
{
lean_object* v_unused_6636_; 
v_unused_6636_ = lean_ctor_get(v___x_6603_, 2);
lean_dec(v_unused_6636_);
v___x_6613_ = v___x_6603_;
v_isShared_6614_ = v_isSharedCheck_6635_;
goto v_resetjp_6612_;
}
else
{
lean_inc(v_snapshotTasks_6611_);
lean_inc(v_infoState_6610_);
lean_inc(v_messages_6609_);
lean_inc(v_cache_6608_);
lean_inc(v_traceState_6607_);
lean_inc(v_auxDeclNGen_6606_);
lean_inc(v_nextMacroScope_6605_);
lean_inc(v_env_6604_);
lean_dec(v___x_6603_);
v___x_6613_ = lean_box(0);
v_isShared_6614_ = v_isSharedCheck_6635_;
goto v_resetjp_6612_;
}
v_resetjp_6612_:
{
lean_object* v___x_6616_; 
if (v_isShared_6614_ == 0)
{
lean_ctor_set(v___x_6613_, 2, v___x_6602_);
v___x_6616_ = v___x_6613_;
goto v_reusejp_6615_;
}
else
{
lean_object* v_reuseFailAlloc_6634_; 
v_reuseFailAlloc_6634_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6634_, 0, v_env_6604_);
lean_ctor_set(v_reuseFailAlloc_6634_, 1, v_nextMacroScope_6605_);
lean_ctor_set(v_reuseFailAlloc_6634_, 2, v___x_6602_);
lean_ctor_set(v_reuseFailAlloc_6634_, 3, v_auxDeclNGen_6606_);
lean_ctor_set(v_reuseFailAlloc_6634_, 4, v_traceState_6607_);
lean_ctor_set(v_reuseFailAlloc_6634_, 5, v_cache_6608_);
lean_ctor_set(v_reuseFailAlloc_6634_, 6, v_messages_6609_);
lean_ctor_set(v_reuseFailAlloc_6634_, 7, v_infoState_6610_);
lean_ctor_set(v_reuseFailAlloc_6634_, 8, v_snapshotTasks_6611_);
v___x_6616_ = v_reuseFailAlloc_6634_;
goto v_reusejp_6615_;
}
v_reusejp_6615_:
{
lean_object* v___x_6617_; lean_object* v___x_6618_; 
v___x_6617_ = lean_st_ref_put(v_a_6564_, v___x_6616_);
v___x_6618_ = lean_st_ref_get(v_ref_6555_);
if (lean_obj_tag(v___x_6618_) == 0)
{
lean_object* v_toCold_6619_; lean_object* v_options_6620_; lean_object* v___x_6621_; lean_object* v___x_6622_; lean_object* v___x_6623_; 
v_toCold_6619_ = lean_ctor_get(v_a_6563_, 0);
v_options_6620_ = lean_ctor_get(v_toCold_6619_, 2);
v___x_6621_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___closed__0));
v___x_6622_ = lean_box(0);
v___x_6623_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v___x_6621_, v_options_6620_, v___f_6600_, v___x_6622_, v_a_6561_, v_a_6562_, v_a_6563_, v_a_6564_);
if (lean_obj_tag(v___x_6623_) == 0)
{
lean_object* v_a_6624_; 
v_a_6624_ = lean_ctor_get(v___x_6623_, 0);
lean_inc(v_a_6624_);
lean_dec_ref_known(v___x_6623_, 1);
v_a_6567_ = v_a_6624_;
goto v___jp_6566_;
}
else
{
lean_object* v_a_6625_; lean_object* v___x_6627_; uint8_t v_isShared_6628_; uint8_t v_isSharedCheck_6632_; 
lean_dec_ref(v_ty_6560_);
v_a_6625_ = lean_ctor_get(v___x_6623_, 0);
v_isSharedCheck_6632_ = !lean_is_exclusive(v___x_6623_);
if (v_isSharedCheck_6632_ == 0)
{
v___x_6627_ = v___x_6623_;
v_isShared_6628_ = v_isSharedCheck_6632_;
goto v_resetjp_6626_;
}
else
{
lean_inc(v_a_6625_);
lean_dec(v___x_6623_);
v___x_6627_ = lean_box(0);
v_isShared_6628_ = v_isSharedCheck_6632_;
goto v_resetjp_6626_;
}
v_resetjp_6626_:
{
lean_object* v___x_6630_; 
if (v_isShared_6628_ == 0)
{
v___x_6630_ = v___x_6627_;
goto v_reusejp_6629_;
}
else
{
lean_object* v_reuseFailAlloc_6631_; 
v_reuseFailAlloc_6631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6631_, 0, v_a_6625_);
v___x_6630_ = v_reuseFailAlloc_6631_;
goto v_reusejp_6629_;
}
v_reusejp_6629_:
{
return v___x_6630_;
}
}
}
}
else
{
lean_object* v_val_6633_; 
lean_dec_ref(v___f_6600_);
v_val_6633_ = lean_ctor_get(v___x_6618_, 0);
lean_inc(v_val_6633_);
lean_dec_ref_known(v___x_6618_, 1);
v_a_6567_ = v_val_6633_;
goto v___jp_6566_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___boxed(lean_object* v_ref_6639_, lean_object* v_addEntry_6640_, lean_object* v_droppedKeys_6641_, lean_object* v_constantsPerTask_6642_, lean_object* v_droppedEntriesRef_6643_, lean_object* v_ty_6644_, lean_object* v_a_6645_, lean_object* v_a_6646_, lean_object* v_a_6647_, lean_object* v_a_6648_, lean_object* v_a_6649_){
_start:
{
lean_object* v_res_6650_; 
v_res_6650_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(v_ref_6639_, v_addEntry_6640_, v_droppedKeys_6641_, v_constantsPerTask_6642_, v_droppedEntriesRef_6643_, v_ty_6644_, v_a_6645_, v_a_6646_, v_a_6647_, v_a_6648_);
lean_dec(v_a_6648_);
lean_dec_ref(v_a_6647_);
lean_dec(v_a_6646_);
lean_dec_ref(v_a_6645_);
lean_dec(v_ref_6639_);
return v_res_6650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches(lean_object* v_00_u03b1_6651_, lean_object* v_ref_6652_, lean_object* v_addEntry_6653_, lean_object* v_droppedKeys_6654_, lean_object* v_constantsPerTask_6655_, lean_object* v_droppedEntriesRef_6656_, lean_object* v_ty_6657_, lean_object* v_a_6658_, lean_object* v_a_6659_, lean_object* v_a_6660_, lean_object* v_a_6661_){
_start:
{
lean_object* v___x_6663_; 
v___x_6663_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(v_ref_6652_, v_addEntry_6653_, v_droppedKeys_6654_, v_constantsPerTask_6655_, v_droppedEntriesRef_6656_, v_ty_6657_, v_a_6658_, v_a_6659_, v_a_6660_, v_a_6661_);
return v___x_6663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___boxed(lean_object* v_00_u03b1_6664_, lean_object* v_ref_6665_, lean_object* v_addEntry_6666_, lean_object* v_droppedKeys_6667_, lean_object* v_constantsPerTask_6668_, lean_object* v_droppedEntriesRef_6669_, lean_object* v_ty_6670_, lean_object* v_a_6671_, lean_object* v_a_6672_, lean_object* v_a_6673_, lean_object* v_a_6674_, lean_object* v_a_6675_){
_start:
{
lean_object* v_res_6676_; 
v_res_6676_ = l_Lean_Meta_LazyDiscrTree_findImportMatches(v_00_u03b1_6664_, v_ref_6665_, v_addEntry_6666_, v_droppedKeys_6667_, v_constantsPerTask_6668_, v_droppedEntriesRef_6669_, v_ty_6670_, v_a_6671_, v_a_6672_, v_a_6673_, v_a_6674_);
lean_dec(v_a_6674_);
lean_dec_ref(v_a_6673_);
lean_dec(v_a_6672_);
lean_dec_ref(v_a_6671_);
lean_dec(v_ref_6665_);
return v_res_6676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0(lean_object* v_00_u03b1_6677_, lean_object* v_cctx_6678_, lean_object* v_ngen_6679_, lean_object* v_env_6680_, lean_object* v_act_6681_, lean_object* v_constantsPerTask_6682_, lean_object* v___y_6683_, lean_object* v___y_6684_, lean_object* v___y_6685_, lean_object* v___y_6686_){
_start:
{
lean_object* v___x_6688_; 
v___x_6688_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(v_cctx_6678_, v_ngen_6679_, v_env_6680_, v_act_6681_, v_constantsPerTask_6682_, v___y_6683_, v___y_6684_, v___y_6685_, v___y_6686_);
return v___x_6688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___boxed(lean_object* v_00_u03b1_6689_, lean_object* v_cctx_6690_, lean_object* v_ngen_6691_, lean_object* v_env_6692_, lean_object* v_act_6693_, lean_object* v_constantsPerTask_6694_, lean_object* v___y_6695_, lean_object* v___y_6696_, lean_object* v___y_6697_, lean_object* v___y_6698_, lean_object* v___y_6699_){
_start:
{
lean_object* v_res_6700_; 
v_res_6700_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0(v_00_u03b1_6689_, v_cctx_6690_, v_ngen_6691_, v_env_6692_, v_act_6693_, v_constantsPerTask_6694_, v___y_6695_, v___y_6696_, v___y_6697_, v___y_6698_);
lean_dec(v___y_6698_);
lean_dec_ref(v___y_6697_);
lean_dec(v___y_6696_);
lean_dec_ref(v___y_6695_);
lean_dec(v_constantsPerTask_6694_);
return v_res_6700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1(lean_object* v_00_u03b1_6701_, lean_object* v_cctx_6702_, lean_object* v_env_6703_, lean_object* v_act_6704_, lean_object* v_constantsPerTask_6705_, lean_object* v_n_6706_, lean_object* v_ngen_6707_, lean_object* v_tasks_6708_, lean_object* v_start_6709_, lean_object* v_cnt_6710_, lean_object* v_idx_6711_, lean_object* v___y_6712_, lean_object* v___y_6713_, lean_object* v___y_6714_, lean_object* v___y_6715_){
_start:
{
lean_object* v___x_6717_; 
v___x_6717_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(v_cctx_6702_, v_env_6703_, v_act_6704_, v_constantsPerTask_6705_, v_n_6706_, v_ngen_6707_, v_tasks_6708_, v_start_6709_, v_cnt_6710_, v_idx_6711_);
return v___x_6717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___boxed(lean_object* v_00_u03b1_6718_, lean_object* v_cctx_6719_, lean_object* v_env_6720_, lean_object* v_act_6721_, lean_object* v_constantsPerTask_6722_, lean_object* v_n_6723_, lean_object* v_ngen_6724_, lean_object* v_tasks_6725_, lean_object* v_start_6726_, lean_object* v_cnt_6727_, lean_object* v_idx_6728_, lean_object* v___y_6729_, lean_object* v___y_6730_, lean_object* v___y_6731_, lean_object* v___y_6732_, lean_object* v___y_6733_){
_start:
{
lean_object* v_res_6734_; 
v_res_6734_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1(v_00_u03b1_6718_, v_cctx_6719_, v_env_6720_, v_act_6721_, v_constantsPerTask_6722_, v_n_6723_, v_ngen_6724_, v_tasks_6725_, v_start_6726_, v_cnt_6727_, v_idx_6728_, v___y_6729_, v___y_6730_, v___y_6731_, v___y_6732_);
lean_dec(v___y_6732_);
lean_dec_ref(v___y_6731_);
lean_dec(v___y_6730_);
lean_dec_ref(v___y_6729_);
lean_dec(v_constantsPerTask_6722_);
return v_res_6734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2(lean_object* v_00_u03b1_6735_, lean_object* v_z_6736_, lean_object* v_tasks_6737_){
_start:
{
lean_object* v___x_6738_; 
v___x_6738_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(v_z_6736_, v_tasks_6737_);
return v___x_6738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___boxed(lean_object* v_00_u03b1_6739_, lean_object* v_z_6740_, lean_object* v_tasks_6741_){
_start:
{
lean_object* v_res_6742_; 
v_res_6742_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2(v_00_u03b1_6739_, v_z_6740_, v_tasks_6741_);
lean_dec_ref(v_tasks_6741_);
return v_res_6742_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5(lean_object* v_00_u03b1_6743_, lean_object* v_as_6744_, size_t v_i_6745_, size_t v_stop_6746_, lean_object* v_b_6747_){
_start:
{
lean_object* v___x_6748_; 
v___x_6748_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(v_as_6744_, v_i_6745_, v_stop_6746_, v_b_6747_);
return v___x_6748_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b1_6749_, lean_object* v_as_6750_, lean_object* v_i_6751_, lean_object* v_stop_6752_, lean_object* v_b_6753_){
_start:
{
size_t v_i_boxed_6754_; size_t v_stop_boxed_6755_; lean_object* v_res_6756_; 
v_i_boxed_6754_ = lean_unbox_usize(v_i_6751_);
lean_dec(v_i_6751_);
v_stop_boxed_6755_ = lean_unbox_usize(v_stop_6752_);
lean_dec(v_stop_6752_);
v_res_6756_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5(v_00_u03b1_6749_, v_as_6750_, v_i_boxed_6754_, v_stop_boxed_6755_, v_b_6753_);
lean_dec_ref(v_as_6750_);
return v_res_6756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(lean_object* v___y_6757_){
_start:
{
lean_object* v___x_6759_; lean_object* v_ngen_6760_; lean_object* v_namePrefix_6761_; lean_object* v_idx_6762_; lean_object* v___x_6764_; uint8_t v_isShared_6765_; uint8_t v_isSharedCheck_6792_; 
v___x_6759_ = lean_st_ref_get(v___y_6757_);
v_ngen_6760_ = lean_ctor_get(v___x_6759_, 2);
lean_inc_ref(v_ngen_6760_);
lean_dec(v___x_6759_);
v_namePrefix_6761_ = lean_ctor_get(v_ngen_6760_, 0);
v_idx_6762_ = lean_ctor_get(v_ngen_6760_, 1);
v_isSharedCheck_6792_ = !lean_is_exclusive(v_ngen_6760_);
if (v_isSharedCheck_6792_ == 0)
{
v___x_6764_ = v_ngen_6760_;
v_isShared_6765_ = v_isSharedCheck_6792_;
goto v_resetjp_6763_;
}
else
{
lean_inc(v_idx_6762_);
lean_inc(v_namePrefix_6761_);
lean_dec(v_ngen_6760_);
v___x_6764_ = lean_box(0);
v_isShared_6765_ = v_isSharedCheck_6792_;
goto v_resetjp_6763_;
}
v_resetjp_6763_:
{
lean_object* v___x_6766_; lean_object* v___x_6767_; lean_object* v___x_6769_; 
lean_inc(v_idx_6762_);
lean_inc(v_namePrefix_6761_);
v___x_6766_ = l_Lean_Name_num___override(v_namePrefix_6761_, v_idx_6762_);
v___x_6767_ = lean_unsigned_to_nat(1u);
if (v_isShared_6765_ == 0)
{
lean_ctor_set(v___x_6764_, 1, v___x_6767_);
lean_ctor_set(v___x_6764_, 0, v___x_6766_);
v___x_6769_ = v___x_6764_;
goto v_reusejp_6768_;
}
else
{
lean_object* v_reuseFailAlloc_6791_; 
v_reuseFailAlloc_6791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6791_, 0, v___x_6766_);
lean_ctor_set(v_reuseFailAlloc_6791_, 1, v___x_6767_);
v___x_6769_ = v_reuseFailAlloc_6791_;
goto v_reusejp_6768_;
}
v_reusejp_6768_:
{
lean_object* v___x_6770_; lean_object* v___x_6771_; lean_object* v___x_6772_; lean_object* v_env_6773_; lean_object* v_nextMacroScope_6774_; lean_object* v_auxDeclNGen_6775_; lean_object* v_traceState_6776_; lean_object* v_cache_6777_; lean_object* v_messages_6778_; lean_object* v_infoState_6779_; lean_object* v_snapshotTasks_6780_; lean_object* v___x_6782_; uint8_t v_isShared_6783_; uint8_t v_isSharedCheck_6789_; 
v___x_6770_ = lean_nat_add(v_idx_6762_, v___x_6767_);
lean_dec(v_idx_6762_);
v___x_6771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6771_, 0, v_namePrefix_6761_);
lean_ctor_set(v___x_6771_, 1, v___x_6770_);
v___x_6772_ = lean_st_ref_take(v___y_6757_);
v_env_6773_ = lean_ctor_get(v___x_6772_, 0);
v_nextMacroScope_6774_ = lean_ctor_get(v___x_6772_, 1);
v_auxDeclNGen_6775_ = lean_ctor_get(v___x_6772_, 3);
v_traceState_6776_ = lean_ctor_get(v___x_6772_, 4);
v_cache_6777_ = lean_ctor_get(v___x_6772_, 5);
v_messages_6778_ = lean_ctor_get(v___x_6772_, 6);
v_infoState_6779_ = lean_ctor_get(v___x_6772_, 7);
v_snapshotTasks_6780_ = lean_ctor_get(v___x_6772_, 8);
v_isSharedCheck_6789_ = !lean_is_exclusive(v___x_6772_);
if (v_isSharedCheck_6789_ == 0)
{
lean_object* v_unused_6790_; 
v_unused_6790_ = lean_ctor_get(v___x_6772_, 2);
lean_dec(v_unused_6790_);
v___x_6782_ = v___x_6772_;
v_isShared_6783_ = v_isSharedCheck_6789_;
goto v_resetjp_6781_;
}
else
{
lean_inc(v_snapshotTasks_6780_);
lean_inc(v_infoState_6779_);
lean_inc(v_messages_6778_);
lean_inc(v_cache_6777_);
lean_inc(v_traceState_6776_);
lean_inc(v_auxDeclNGen_6775_);
lean_inc(v_nextMacroScope_6774_);
lean_inc(v_env_6773_);
lean_dec(v___x_6772_);
v___x_6782_ = lean_box(0);
v_isShared_6783_ = v_isSharedCheck_6789_;
goto v_resetjp_6781_;
}
v_resetjp_6781_:
{
lean_object* v___x_6785_; 
if (v_isShared_6783_ == 0)
{
lean_ctor_set(v___x_6782_, 2, v___x_6771_);
v___x_6785_ = v___x_6782_;
goto v_reusejp_6784_;
}
else
{
lean_object* v_reuseFailAlloc_6788_; 
v_reuseFailAlloc_6788_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6788_, 0, v_env_6773_);
lean_ctor_set(v_reuseFailAlloc_6788_, 1, v_nextMacroScope_6774_);
lean_ctor_set(v_reuseFailAlloc_6788_, 2, v___x_6771_);
lean_ctor_set(v_reuseFailAlloc_6788_, 3, v_auxDeclNGen_6775_);
lean_ctor_set(v_reuseFailAlloc_6788_, 4, v_traceState_6776_);
lean_ctor_set(v_reuseFailAlloc_6788_, 5, v_cache_6777_);
lean_ctor_set(v_reuseFailAlloc_6788_, 6, v_messages_6778_);
lean_ctor_set(v_reuseFailAlloc_6788_, 7, v_infoState_6779_);
lean_ctor_set(v_reuseFailAlloc_6788_, 8, v_snapshotTasks_6780_);
v___x_6785_ = v_reuseFailAlloc_6788_;
goto v_reusejp_6784_;
}
v_reusejp_6784_:
{
lean_object* v___x_6786_; lean_object* v___x_6787_; 
v___x_6786_ = lean_st_ref_put(v___y_6757_, v___x_6785_);
v___x_6787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6787_, 0, v___x_6769_);
return v___x_6787_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg___boxed(lean_object* v___y_6793_, lean_object* v___y_6794_){
_start:
{
lean_object* v_res_6795_; 
v_res_6795_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(v___y_6793_);
lean_dec(v___y_6793_);
return v_res_6795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1(lean_object* v___y_6796_, lean_object* v___y_6797_){
_start:
{
lean_object* v___x_6799_; 
v___x_6799_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(v___y_6797_);
return v___x_6799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___boxed(lean_object* v___y_6800_, lean_object* v___y_6801_, lean_object* v___y_6802_){
_start:
{
lean_object* v_res_6803_; 
v_res_6803_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1(v___y_6800_, v___y_6801_);
lean_dec(v___y_6801_);
lean_dec_ref(v___y_6800_);
return v_res_6803_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0(void){
_start:
{
lean_object* v___x_6804_; lean_object* v___x_6805_; lean_object* v___x_6806_; 
v___x_6804_ = lean_unsigned_to_nat(32u);
v___x_6805_ = lean_mk_empty_array_with_capacity(v___x_6804_);
v___x_6806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6806_, 0, v___x_6805_);
return v___x_6806_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1(void){
_start:
{
size_t v___x_6807_; lean_object* v___x_6808_; lean_object* v___x_6809_; lean_object* v___x_6810_; lean_object* v___x_6811_; lean_object* v___x_6812_; 
v___x_6807_ = ((size_t)5ULL);
v___x_6808_ = lean_unsigned_to_nat(0u);
v___x_6809_ = lean_unsigned_to_nat(32u);
v___x_6810_ = lean_mk_empty_array_with_capacity(v___x_6809_);
v___x_6811_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0);
v___x_6812_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_6812_, 0, v___x_6811_);
lean_ctor_set(v___x_6812_, 1, v___x_6810_);
lean_ctor_set(v___x_6812_, 2, v___x_6808_);
lean_ctor_set(v___x_6812_, 3, v___x_6808_);
lean_ctor_set_usize(v___x_6812_, 4, v___x_6807_);
return v___x_6812_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2(void){
_start:
{
lean_object* v___x_6813_; lean_object* v___x_6814_; lean_object* v___x_6815_; lean_object* v___x_6816_; 
v___x_6813_ = lean_box(1);
v___x_6814_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1);
v___x_6815_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0);
v___x_6816_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6816_, 0, v___x_6815_);
lean_ctor_set(v___x_6816_, 1, v___x_6814_);
lean_ctor_set(v___x_6816_, 2, v___x_6813_);
return v___x_6816_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_msgData_6817_, lean_object* v___y_6818_, lean_object* v___y_6819_){
_start:
{
lean_object* v___x_6821_; lean_object* v_toCold_6822_; lean_object* v_env_6823_; lean_object* v_options_6824_; lean_object* v___x_6825_; lean_object* v___x_6826_; lean_object* v___x_6827_; lean_object* v___x_6828_; lean_object* v___x_6829_; 
v___x_6821_ = lean_st_ref_get(v___y_6819_);
v_toCold_6822_ = lean_ctor_get(v___y_6818_, 0);
v_env_6823_ = lean_ctor_get(v___x_6821_, 0);
lean_inc_ref(v_env_6823_);
lean_dec(v___x_6821_);
v_options_6824_ = lean_ctor_get(v_toCold_6822_, 2);
v___x_6825_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_6826_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2);
lean_inc_ref(v_options_6824_);
v___x_6827_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6827_, 0, v_env_6823_);
lean_ctor_set(v___x_6827_, 1, v___x_6825_);
lean_ctor_set(v___x_6827_, 2, v___x_6826_);
lean_ctor_set(v___x_6827_, 3, v_options_6824_);
v___x_6828_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_6828_, 0, v___x_6827_);
lean_ctor_set(v___x_6828_, 1, v_msgData_6817_);
v___x_6829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6829_, 0, v___x_6828_);
return v___x_6829_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(lean_object* v_msgData_6830_, lean_object* v___y_6831_, lean_object* v___y_6832_, lean_object* v___y_6833_){
_start:
{
lean_object* v_res_6834_; 
v_res_6834_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5(v_msgData_6830_, v___y_6831_, v___y_6832_);
lean_dec(v___y_6832_);
lean_dec_ref(v___y_6831_);
return v_res_6834_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4(lean_object* v_ref_6835_, lean_object* v_msgData_6836_, uint8_t v_severity_6837_, uint8_t v_isSilent_6838_, lean_object* v___y_6839_, lean_object* v___y_6840_){
_start:
{
lean_object* v___y_6843_; lean_object* v___y_6844_; uint8_t v___y_6845_; uint8_t v___y_6846_; lean_object* v___y_6847_; lean_object* v___y_6848_; lean_object* v___y_6849_; lean_object* v_currNamespace_6850_; lean_object* v_openDecls_6851_; lean_object* v___y_6852_; lean_object* v___y_6878_; lean_object* v___y_6879_; lean_object* v___y_6880_; lean_object* v___y_6881_; uint8_t v___y_6882_; uint8_t v___y_6883_; uint8_t v___y_6884_; lean_object* v___y_6885_; lean_object* v___y_6886_; lean_object* v___y_6887_; lean_object* v___y_6905_; lean_object* v___y_6906_; lean_object* v___y_6907_; lean_object* v___y_6908_; lean_object* v___y_6909_; uint8_t v___y_6910_; uint8_t v___y_6911_; uint8_t v___y_6912_; lean_object* v___y_6913_; lean_object* v___y_6914_; lean_object* v___y_6918_; lean_object* v___y_6919_; lean_object* v___y_6920_; lean_object* v___y_6921_; uint8_t v___y_6922_; uint8_t v___y_6923_; lean_object* v___y_6924_; lean_object* v___y_6925_; uint8_t v___y_6926_; uint8_t v___x_6931_; lean_object* v___y_6933_; lean_object* v___y_6934_; lean_object* v___y_6935_; lean_object* v___y_6936_; lean_object* v___y_6937_; uint8_t v___y_6938_; lean_object* v___y_6939_; uint8_t v___y_6940_; uint8_t v___y_6941_; uint8_t v___y_6943_; uint8_t v___x_6961_; 
v___x_6931_ = 2;
v___x_6961_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6837_, v___x_6931_);
if (v___x_6961_ == 0)
{
v___y_6943_ = v___x_6961_;
goto v___jp_6942_;
}
else
{
uint8_t v___x_6962_; 
lean_inc_ref(v_msgData_6836_);
v___x_6962_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_6836_);
v___y_6943_ = v___x_6962_;
goto v___jp_6942_;
}
v___jp_6842_:
{
lean_object* v___x_6853_; lean_object* v___x_6854_; lean_object* v___x_6855_; lean_object* v___x_6856_; lean_object* v_env_6857_; lean_object* v_nextMacroScope_6858_; lean_object* v_ngen_6859_; lean_object* v_auxDeclNGen_6860_; lean_object* v_traceState_6861_; lean_object* v_cache_6862_; lean_object* v_messages_6863_; lean_object* v_infoState_6864_; lean_object* v_snapshotTasks_6865_; lean_object* v___x_6867_; uint8_t v_isShared_6868_; uint8_t v_isSharedCheck_6876_; 
lean_inc(v_openDecls_6851_);
lean_inc(v_currNamespace_6850_);
v___x_6853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6853_, 0, v_currNamespace_6850_);
lean_ctor_set(v___x_6853_, 1, v_openDecls_6851_);
v___x_6854_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6854_, 0, v___x_6853_);
lean_ctor_set(v___x_6854_, 1, v___y_6849_);
lean_inc_ref(v___y_6848_);
lean_inc_ref(v___y_6847_);
v___x_6855_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_6855_, 0, v___y_6847_);
lean_ctor_set(v___x_6855_, 1, v___y_6844_);
lean_ctor_set(v___x_6855_, 2, v___y_6843_);
lean_ctor_set(v___x_6855_, 3, v___y_6848_);
lean_ctor_set(v___x_6855_, 4, v___x_6854_);
lean_ctor_set_uint8(v___x_6855_, sizeof(void*)*5, v___y_6845_);
lean_ctor_set_uint8(v___x_6855_, sizeof(void*)*5 + 1, v___y_6846_);
lean_ctor_set_uint8(v___x_6855_, sizeof(void*)*5 + 2, v_isSilent_6838_);
v___x_6856_ = lean_st_ref_take(v___y_6852_);
v_env_6857_ = lean_ctor_get(v___x_6856_, 0);
v_nextMacroScope_6858_ = lean_ctor_get(v___x_6856_, 1);
v_ngen_6859_ = lean_ctor_get(v___x_6856_, 2);
v_auxDeclNGen_6860_ = lean_ctor_get(v___x_6856_, 3);
v_traceState_6861_ = lean_ctor_get(v___x_6856_, 4);
v_cache_6862_ = lean_ctor_get(v___x_6856_, 5);
v_messages_6863_ = lean_ctor_get(v___x_6856_, 6);
v_infoState_6864_ = lean_ctor_get(v___x_6856_, 7);
v_snapshotTasks_6865_ = lean_ctor_get(v___x_6856_, 8);
v_isSharedCheck_6876_ = !lean_is_exclusive(v___x_6856_);
if (v_isSharedCheck_6876_ == 0)
{
v___x_6867_ = v___x_6856_;
v_isShared_6868_ = v_isSharedCheck_6876_;
goto v_resetjp_6866_;
}
else
{
lean_inc(v_snapshotTasks_6865_);
lean_inc(v_infoState_6864_);
lean_inc(v_messages_6863_);
lean_inc(v_cache_6862_);
lean_inc(v_traceState_6861_);
lean_inc(v_auxDeclNGen_6860_);
lean_inc(v_ngen_6859_);
lean_inc(v_nextMacroScope_6858_);
lean_inc(v_env_6857_);
lean_dec(v___x_6856_);
v___x_6867_ = lean_box(0);
v_isShared_6868_ = v_isSharedCheck_6876_;
goto v_resetjp_6866_;
}
v_resetjp_6866_:
{
lean_object* v___x_6869_; lean_object* v___x_6870_; lean_object* v___x_6872_; 
v___x_6869_ = lean_box(0);
v___x_6870_ = l_Lean_MessageLog_add(v___x_6855_, v_messages_6863_);
if (v_isShared_6868_ == 0)
{
lean_ctor_set(v___x_6867_, 6, v___x_6870_);
v___x_6872_ = v___x_6867_;
goto v_reusejp_6871_;
}
else
{
lean_object* v_reuseFailAlloc_6875_; 
v_reuseFailAlloc_6875_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6875_, 0, v_env_6857_);
lean_ctor_set(v_reuseFailAlloc_6875_, 1, v_nextMacroScope_6858_);
lean_ctor_set(v_reuseFailAlloc_6875_, 2, v_ngen_6859_);
lean_ctor_set(v_reuseFailAlloc_6875_, 3, v_auxDeclNGen_6860_);
lean_ctor_set(v_reuseFailAlloc_6875_, 4, v_traceState_6861_);
lean_ctor_set(v_reuseFailAlloc_6875_, 5, v_cache_6862_);
lean_ctor_set(v_reuseFailAlloc_6875_, 6, v___x_6870_);
lean_ctor_set(v_reuseFailAlloc_6875_, 7, v_infoState_6864_);
lean_ctor_set(v_reuseFailAlloc_6875_, 8, v_snapshotTasks_6865_);
v___x_6872_ = v_reuseFailAlloc_6875_;
goto v_reusejp_6871_;
}
v_reusejp_6871_:
{
lean_object* v___x_6873_; lean_object* v___x_6874_; 
v___x_6873_ = lean_st_ref_put(v___y_6852_, v___x_6872_);
v___x_6874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6874_, 0, v___x_6869_);
return v___x_6874_;
}
}
}
v___jp_6877_:
{
lean_object* v___x_6888_; lean_object* v___x_6889_; lean_object* v_a_6890_; lean_object* v___x_6892_; uint8_t v_isShared_6893_; uint8_t v_isSharedCheck_6903_; 
v___x_6888_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_6836_);
v___x_6889_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5(v___x_6888_, v___y_6839_, v___y_6840_);
v_a_6890_ = lean_ctor_get(v___x_6889_, 0);
v_isSharedCheck_6903_ = !lean_is_exclusive(v___x_6889_);
if (v_isSharedCheck_6903_ == 0)
{
v___x_6892_ = v___x_6889_;
v_isShared_6893_ = v_isSharedCheck_6903_;
goto v_resetjp_6891_;
}
else
{
lean_inc(v_a_6890_);
lean_dec(v___x_6889_);
v___x_6892_ = lean_box(0);
v_isShared_6893_ = v_isSharedCheck_6903_;
goto v_resetjp_6891_;
}
v_resetjp_6891_:
{
lean_object* v___x_6894_; lean_object* v___x_6895_; lean_object* v___x_6896_; lean_object* v___x_6897_; 
lean_inc_ref_n(v___y_6881_, 2);
v___x_6894_ = l_Lean_FileMap_toPosition(v___y_6881_, v___y_6885_);
lean_dec(v___y_6885_);
v___x_6895_ = l_Lean_FileMap_toPosition(v___y_6881_, v___y_6887_);
lean_dec(v___y_6887_);
v___x_6896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6896_, 0, v___x_6895_);
v___x_6897_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___closed__0));
if (v___y_6882_ == 0)
{
lean_del_object(v___x_6892_);
lean_dec_ref(v___y_6879_);
v___y_6843_ = v___x_6896_;
v___y_6844_ = v___x_6894_;
v___y_6845_ = v___y_6883_;
v___y_6846_ = v___y_6884_;
v___y_6847_ = v___y_6886_;
v___y_6848_ = v___x_6897_;
v___y_6849_ = v_a_6890_;
v_currNamespace_6850_ = v___y_6878_;
v_openDecls_6851_ = v___y_6880_;
v___y_6852_ = v___y_6840_;
goto v___jp_6842_;
}
else
{
uint8_t v___x_6898_; 
lean_inc(v_a_6890_);
v___x_6898_ = l_Lean_MessageData_hasTag(v___y_6879_, v_a_6890_);
if (v___x_6898_ == 0)
{
lean_object* v___x_6899_; lean_object* v___x_6901_; 
lean_dec_ref_known(v___x_6896_, 1);
lean_dec_ref(v___x_6894_);
lean_dec(v_a_6890_);
v___x_6899_ = lean_box(0);
if (v_isShared_6893_ == 0)
{
lean_ctor_set(v___x_6892_, 0, v___x_6899_);
v___x_6901_ = v___x_6892_;
goto v_reusejp_6900_;
}
else
{
lean_object* v_reuseFailAlloc_6902_; 
v_reuseFailAlloc_6902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6902_, 0, v___x_6899_);
v___x_6901_ = v_reuseFailAlloc_6902_;
goto v_reusejp_6900_;
}
v_reusejp_6900_:
{
return v___x_6901_;
}
}
else
{
lean_del_object(v___x_6892_);
v___y_6843_ = v___x_6896_;
v___y_6844_ = v___x_6894_;
v___y_6845_ = v___y_6883_;
v___y_6846_ = v___y_6884_;
v___y_6847_ = v___y_6886_;
v___y_6848_ = v___x_6897_;
v___y_6849_ = v_a_6890_;
v_currNamespace_6850_ = v___y_6878_;
v_openDecls_6851_ = v___y_6880_;
v___y_6852_ = v___y_6840_;
goto v___jp_6842_;
}
}
}
}
v___jp_6904_:
{
lean_object* v___x_6915_; 
v___x_6915_ = l_Lean_Syntax_getTailPos_x3f(v___y_6908_, v___y_6911_);
lean_dec(v___y_6908_);
if (lean_obj_tag(v___x_6915_) == 0)
{
lean_inc(v___y_6914_);
v___y_6878_ = v___y_6905_;
v___y_6879_ = v___y_6906_;
v___y_6880_ = v___y_6907_;
v___y_6881_ = v___y_6909_;
v___y_6882_ = v___y_6910_;
v___y_6883_ = v___y_6911_;
v___y_6884_ = v___y_6912_;
v___y_6885_ = v___y_6914_;
v___y_6886_ = v___y_6913_;
v___y_6887_ = v___y_6914_;
goto v___jp_6877_;
}
else
{
lean_object* v_val_6916_; 
v_val_6916_ = lean_ctor_get(v___x_6915_, 0);
lean_inc(v_val_6916_);
lean_dec_ref_known(v___x_6915_, 1);
v___y_6878_ = v___y_6905_;
v___y_6879_ = v___y_6906_;
v___y_6880_ = v___y_6907_;
v___y_6881_ = v___y_6909_;
v___y_6882_ = v___y_6910_;
v___y_6883_ = v___y_6911_;
v___y_6884_ = v___y_6912_;
v___y_6885_ = v___y_6914_;
v___y_6886_ = v___y_6913_;
v___y_6887_ = v_val_6916_;
goto v___jp_6877_;
}
}
v___jp_6917_:
{
lean_object* v_ref_6927_; lean_object* v___x_6928_; 
v_ref_6927_ = l_Lean_replaceRef(v_ref_6835_, v___y_6924_);
v___x_6928_ = l_Lean_Syntax_getPos_x3f(v_ref_6927_, v___y_6923_);
if (lean_obj_tag(v___x_6928_) == 0)
{
lean_object* v___x_6929_; 
v___x_6929_ = lean_unsigned_to_nat(0u);
v___y_6905_ = v___y_6918_;
v___y_6906_ = v___y_6919_;
v___y_6907_ = v___y_6920_;
v___y_6908_ = v_ref_6927_;
v___y_6909_ = v___y_6921_;
v___y_6910_ = v___y_6922_;
v___y_6911_ = v___y_6923_;
v___y_6912_ = v___y_6926_;
v___y_6913_ = v___y_6925_;
v___y_6914_ = v___x_6929_;
goto v___jp_6904_;
}
else
{
lean_object* v_val_6930_; 
v_val_6930_ = lean_ctor_get(v___x_6928_, 0);
lean_inc(v_val_6930_);
lean_dec_ref_known(v___x_6928_, 1);
v___y_6905_ = v___y_6918_;
v___y_6906_ = v___y_6919_;
v___y_6907_ = v___y_6920_;
v___y_6908_ = v_ref_6927_;
v___y_6909_ = v___y_6921_;
v___y_6910_ = v___y_6922_;
v___y_6911_ = v___y_6923_;
v___y_6912_ = v___y_6926_;
v___y_6913_ = v___y_6925_;
v___y_6914_ = v_val_6930_;
goto v___jp_6904_;
}
}
v___jp_6932_:
{
if (v___y_6941_ == 0)
{
v___y_6918_ = v___y_6934_;
v___y_6919_ = v___y_6936_;
v___y_6920_ = v___y_6937_;
v___y_6921_ = v___y_6933_;
v___y_6922_ = v___y_6938_;
v___y_6923_ = v___y_6940_;
v___y_6924_ = v___y_6939_;
v___y_6925_ = v___y_6935_;
v___y_6926_ = v_severity_6837_;
goto v___jp_6917_;
}
else
{
v___y_6918_ = v___y_6934_;
v___y_6919_ = v___y_6936_;
v___y_6920_ = v___y_6937_;
v___y_6921_ = v___y_6933_;
v___y_6922_ = v___y_6938_;
v___y_6923_ = v___y_6940_;
v___y_6924_ = v___y_6939_;
v___y_6925_ = v___y_6935_;
v___y_6926_ = v___x_6931_;
goto v___jp_6917_;
}
}
v___jp_6942_:
{
if (v___y_6943_ == 0)
{
lean_object* v_toCold_6944_; lean_object* v_ref_6945_; uint8_t v_suppressElabErrors_6946_; lean_object* v_fileName_6947_; lean_object* v_fileMap_6948_; lean_object* v_options_6949_; lean_object* v_currNamespace_6950_; lean_object* v_openDecls_6951_; lean_object* v___x_6952_; lean_object* v___x_6953_; lean_object* v___f_6954_; uint8_t v___x_6955_; uint8_t v___x_6956_; 
v_toCold_6944_ = lean_ctor_get(v___y_6839_, 0);
v_ref_6945_ = lean_ctor_get(v___y_6839_, 2);
v_suppressElabErrors_6946_ = lean_ctor_get_uint8(v___y_6839_, sizeof(void*)*3 + 1);
v_fileName_6947_ = lean_ctor_get(v_toCold_6944_, 0);
v_fileMap_6948_ = lean_ctor_get(v_toCold_6944_, 1);
v_options_6949_ = lean_ctor_get(v_toCold_6944_, 2);
v_currNamespace_6950_ = lean_ctor_get(v_toCold_6944_, 4);
v_openDecls_6951_ = lean_ctor_get(v_toCold_6944_, 5);
v___x_6952_ = lean_box(v_suppressElabErrors_6946_);
v___x_6953_ = lean_box(v___y_6943_);
v___f_6954_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_6954_, 0, v___x_6952_);
lean_closure_set(v___f_6954_, 1, v___x_6953_);
v___x_6955_ = 1;
v___x_6956_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6837_, v___x_6955_);
if (v___x_6956_ == 0)
{
v___y_6933_ = v_fileMap_6948_;
v___y_6934_ = v_currNamespace_6950_;
v___y_6935_ = v_fileName_6947_;
v___y_6936_ = v___f_6954_;
v___y_6937_ = v_openDecls_6951_;
v___y_6938_ = v_suppressElabErrors_6946_;
v___y_6939_ = v_ref_6945_;
v___y_6940_ = v___y_6943_;
v___y_6941_ = v___x_6956_;
goto v___jp_6932_;
}
else
{
lean_object* v___x_6957_; uint8_t v___x_6958_; 
v___x_6957_ = l_Lean_warningAsError;
v___x_6958_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(v_options_6949_, v___x_6957_);
v___y_6933_ = v_fileMap_6948_;
v___y_6934_ = v_currNamespace_6950_;
v___y_6935_ = v_fileName_6947_;
v___y_6936_ = v___f_6954_;
v___y_6937_ = v_openDecls_6951_;
v___y_6938_ = v_suppressElabErrors_6946_;
v___y_6939_ = v_ref_6945_;
v___y_6940_ = v___y_6943_;
v___y_6941_ = v___x_6958_;
goto v___jp_6932_;
}
}
else
{
lean_object* v___x_6959_; lean_object* v___x_6960_; 
lean_dec_ref(v_msgData_6836_);
v___x_6959_ = lean_box(0);
v___x_6960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6960_, 0, v___x_6959_);
return v___x_6960_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_ref_6963_, lean_object* v_msgData_6964_, lean_object* v_severity_6965_, lean_object* v_isSilent_6966_, lean_object* v___y_6967_, lean_object* v___y_6968_, lean_object* v___y_6969_){
_start:
{
uint8_t v_severity_boxed_6970_; uint8_t v_isSilent_boxed_6971_; lean_object* v_res_6972_; 
v_severity_boxed_6970_ = lean_unbox(v_severity_6965_);
v_isSilent_boxed_6971_ = lean_unbox(v_isSilent_6966_);
v_res_6972_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4(v_ref_6963_, v_msgData_6964_, v_severity_boxed_6970_, v_isSilent_boxed_6971_, v___y_6967_, v___y_6968_);
lean_dec(v___y_6968_);
lean_dec_ref(v___y_6967_);
lean_dec(v_ref_6963_);
return v_res_6972_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2(lean_object* v_msgData_6973_, uint8_t v_severity_6974_, uint8_t v_isSilent_6975_, lean_object* v___y_6976_, lean_object* v___y_6977_){
_start:
{
lean_object* v_ref_6979_; lean_object* v___x_6980_; 
v_ref_6979_ = lean_ctor_get(v___y_6976_, 2);
v___x_6980_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4(v_ref_6979_, v_msgData_6973_, v_severity_6974_, v_isSilent_6975_, v___y_6976_, v___y_6977_);
return v___x_6980_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_6981_, lean_object* v_severity_6982_, lean_object* v_isSilent_6983_, lean_object* v___y_6984_, lean_object* v___y_6985_, lean_object* v___y_6986_){
_start:
{
uint8_t v_severity_boxed_6987_; uint8_t v_isSilent_boxed_6988_; lean_object* v_res_6989_; 
v_severity_boxed_6987_ = lean_unbox(v_severity_6982_);
v_isSilent_boxed_6988_ = lean_unbox(v_isSilent_6983_);
v_res_6989_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2(v_msgData_6981_, v_severity_boxed_6987_, v_isSilent_boxed_6988_, v___y_6984_, v___y_6985_);
lean_dec(v___y_6985_);
lean_dec_ref(v___y_6984_);
return v_res_6989_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0(lean_object* v_msgData_6990_, lean_object* v___y_6991_, lean_object* v___y_6992_){
_start:
{
uint8_t v___x_6994_; uint8_t v___x_6995_; lean_object* v___x_6996_; 
v___x_6994_ = 2;
v___x_6995_ = 0;
v___x_6996_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2(v_msgData_6990_, v___x_6994_, v___x_6995_, v___y_6991_, v___y_6992_);
return v___x_6996_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0___boxed(lean_object* v_msgData_6997_, lean_object* v___y_6998_, lean_object* v___y_6999_, lean_object* v___y_7000_){
_start:
{
lean_object* v_res_7001_; 
v_res_7001_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0(v_msgData_6997_, v___y_6998_, v___y_6999_);
lean_dec(v___y_6999_);
lean_dec_ref(v___y_6998_);
return v_res_7001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0(lean_object* v_f_7002_, lean_object* v___y_7003_, lean_object* v___y_7004_){
_start:
{
lean_object* v_module_7006_; lean_object* v_const_7007_; lean_object* v_exception_7008_; lean_object* v___x_7009_; lean_object* v___x_7010_; lean_object* v___x_7011_; lean_object* v___x_7012_; lean_object* v___x_7013_; lean_object* v___x_7014_; lean_object* v___x_7015_; lean_object* v___x_7016_; lean_object* v___x_7017_; lean_object* v___x_7018_; lean_object* v___x_7019_; lean_object* v___x_7020_; 
v_module_7006_ = lean_ctor_get(v_f_7002_, 0);
lean_inc(v_module_7006_);
v_const_7007_ = lean_ctor_get(v_f_7002_, 1);
lean_inc(v_const_7007_);
v_exception_7008_ = lean_ctor_get(v_f_7002_, 2);
lean_inc_ref(v_exception_7008_);
lean_dec_ref(v_f_7002_);
v___x_7009_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1);
v___x_7010_ = l_Lean_MessageData_ofName(v_const_7007_);
v___x_7011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_7011_, 0, v___x_7009_);
lean_ctor_set(v___x_7011_, 1, v___x_7010_);
v___x_7012_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3);
v___x_7013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_7013_, 0, v___x_7011_);
lean_ctor_set(v___x_7013_, 1, v___x_7012_);
v___x_7014_ = l_Lean_MessageData_ofName(v_module_7006_);
v___x_7015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_7015_, 0, v___x_7013_);
lean_ctor_set(v___x_7015_, 1, v___x_7014_);
v___x_7016_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5);
v___x_7017_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_7017_, 0, v___x_7015_);
lean_ctor_set(v___x_7017_, 1, v___x_7016_);
v___x_7018_ = l_Lean_Exception_toMessageData(v_exception_7008_);
v___x_7019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_7019_, 0, v___x_7017_);
lean_ctor_set(v___x_7019_, 1, v___x_7018_);
v___x_7020_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0(v___x_7019_, v___y_7003_, v___y_7004_);
return v___x_7020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0___boxed(lean_object* v_f_7021_, lean_object* v___y_7022_, lean_object* v___y_7023_, lean_object* v___y_7024_){
_start:
{
lean_object* v_res_7025_; 
v_res_7025_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0(v_f_7021_, v___y_7022_, v___y_7023_);
lean_dec(v___y_7023_);
lean_dec_ref(v___y_7022_);
return v_res_7025_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2(lean_object* v_as_7026_, size_t v_i_7027_, size_t v_stop_7028_, lean_object* v_b_7029_, lean_object* v___y_7030_, lean_object* v___y_7031_){
_start:
{
uint8_t v___x_7033_; 
v___x_7033_ = lean_usize_dec_eq(v_i_7027_, v_stop_7028_);
if (v___x_7033_ == 0)
{
lean_object* v___x_7034_; lean_object* v___x_7035_; 
v___x_7034_ = lean_array_uget_borrowed(v_as_7026_, v_i_7027_);
lean_inc(v___x_7034_);
v___x_7035_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0(v___x_7034_, v___y_7030_, v___y_7031_);
if (lean_obj_tag(v___x_7035_) == 0)
{
lean_object* v_a_7036_; size_t v___x_7037_; size_t v___x_7038_; 
v_a_7036_ = lean_ctor_get(v___x_7035_, 0);
lean_inc(v_a_7036_);
lean_dec_ref_known(v___x_7035_, 1);
v___x_7037_ = ((size_t)1ULL);
v___x_7038_ = lean_usize_add(v_i_7027_, v___x_7037_);
v_i_7027_ = v___x_7038_;
v_b_7029_ = v_a_7036_;
goto _start;
}
else
{
return v___x_7035_;
}
}
else
{
lean_object* v___x_7040_; 
v___x_7040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7040_, 0, v_b_7029_);
return v___x_7040_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2___boxed(lean_object* v_as_7041_, lean_object* v_i_7042_, lean_object* v_stop_7043_, lean_object* v_b_7044_, lean_object* v___y_7045_, lean_object* v___y_7046_, lean_object* v___y_7047_){
_start:
{
size_t v_i_boxed_7048_; size_t v_stop_boxed_7049_; lean_object* v_res_7050_; 
v_i_boxed_7048_ = lean_unbox_usize(v_i_7042_);
lean_dec(v_i_7042_);
v_stop_boxed_7049_ = lean_unbox_usize(v_stop_7043_);
lean_dec(v_stop_7043_);
v_res_7050_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2(v_as_7041_, v_i_boxed_7048_, v_stop_boxed_7049_, v_b_7044_, v___y_7045_, v___y_7046_);
lean_dec(v___y_7046_);
lean_dec_ref(v___y_7045_);
lean_dec_ref(v_as_7041_);
return v_res_7050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(lean_object* v_entriesForConst_7051_, lean_object* v_a_7052_, lean_object* v_a_7053_){
_start:
{
lean_object* v___x_7055_; lean_object* v_env_7056_; lean_object* v___x_7057_; lean_object* v_a_7058_; lean_object* v___x_7060_; uint8_t v_isShared_7061_; uint8_t v_isSharedCheck_7091_; 
v___x_7055_ = lean_st_ref_get(v_a_7053_);
v_env_7056_ = lean_ctor_get(v___x_7055_, 0);
lean_inc_ref(v_env_7056_);
lean_dec(v___x_7055_);
v___x_7057_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(v_a_7053_);
v_a_7058_ = lean_ctor_get(v___x_7057_, 0);
v_isSharedCheck_7091_ = !lean_is_exclusive(v___x_7057_);
if (v_isSharedCheck_7091_ == 0)
{
v___x_7060_ = v___x_7057_;
v_isShared_7061_ = v_isSharedCheck_7091_;
goto v_resetjp_7059_;
}
else
{
lean_inc(v_a_7058_);
lean_dec(v___x_7057_);
v___x_7060_ = lean_box(0);
v_isShared_7061_ = v_isSharedCheck_7091_;
goto v_resetjp_7059_;
}
v_resetjp_7059_:
{
lean_object* v___x_7062_; lean_object* v___x_7063_; lean_object* v___y_7070_; lean_object* v___x_7079_; lean_object* v___x_7080_; lean_object* v___x_7081_; uint8_t v___x_7082_; 
v___x_7062_ = l_Lean_Meta_LazyDiscrTree_ImportData_new();
lean_inc_ref(v_a_7052_);
v___x_7063_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(v_a_7052_, v_a_7058_, v_env_7056_, v___x_7062_, v_entriesForConst_7051_);
v___x_7079_ = lean_st_ref_get(v___x_7062_);
lean_dec(v___x_7062_);
v___x_7080_ = lean_unsigned_to_nat(0u);
v___x_7081_ = lean_array_get_size(v___x_7079_);
v___x_7082_ = lean_nat_dec_lt(v___x_7080_, v___x_7081_);
if (v___x_7082_ == 0)
{
lean_dec(v___x_7079_);
goto v___jp_7064_;
}
else
{
lean_object* v___x_7083_; uint8_t v___x_7084_; 
v___x_7083_ = lean_box(0);
v___x_7084_ = lean_nat_dec_le(v___x_7081_, v___x_7081_);
if (v___x_7084_ == 0)
{
if (v___x_7082_ == 0)
{
lean_dec(v___x_7079_);
goto v___jp_7064_;
}
else
{
size_t v___x_7085_; size_t v___x_7086_; lean_object* v___x_7087_; 
v___x_7085_ = ((size_t)0ULL);
v___x_7086_ = lean_usize_of_nat(v___x_7081_);
v___x_7087_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2(v___x_7079_, v___x_7085_, v___x_7086_, v___x_7083_, v_a_7052_, v_a_7053_);
lean_dec(v___x_7079_);
v___y_7070_ = v___x_7087_;
goto v___jp_7069_;
}
}
else
{
size_t v___x_7088_; size_t v___x_7089_; lean_object* v___x_7090_; 
v___x_7088_ = ((size_t)0ULL);
v___x_7089_ = lean_usize_of_nat(v___x_7081_);
v___x_7090_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2(v___x_7079_, v___x_7088_, v___x_7089_, v___x_7083_, v_a_7052_, v_a_7053_);
lean_dec(v___x_7079_);
v___y_7070_ = v___x_7090_;
goto v___jp_7069_;
}
}
v___jp_7064_:
{
lean_object* v___x_7065_; lean_object* v___x_7067_; 
v___x_7065_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v___x_7063_);
if (v_isShared_7061_ == 0)
{
lean_ctor_set(v___x_7060_, 0, v___x_7065_);
v___x_7067_ = v___x_7060_;
goto v_reusejp_7066_;
}
else
{
lean_object* v_reuseFailAlloc_7068_; 
v_reuseFailAlloc_7068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7068_, 0, v___x_7065_);
v___x_7067_ = v_reuseFailAlloc_7068_;
goto v_reusejp_7066_;
}
v_reusejp_7066_:
{
return v___x_7067_;
}
}
v___jp_7069_:
{
if (lean_obj_tag(v___y_7070_) == 0)
{
lean_dec_ref_known(v___y_7070_, 1);
goto v___jp_7064_;
}
else
{
lean_object* v_a_7071_; lean_object* v___x_7073_; uint8_t v_isShared_7074_; uint8_t v_isSharedCheck_7078_; 
lean_dec_ref(v___x_7063_);
lean_del_object(v___x_7060_);
v_a_7071_ = lean_ctor_get(v___y_7070_, 0);
v_isSharedCheck_7078_ = !lean_is_exclusive(v___y_7070_);
if (v_isSharedCheck_7078_ == 0)
{
v___x_7073_ = v___y_7070_;
v_isShared_7074_ = v_isSharedCheck_7078_;
goto v_resetjp_7072_;
}
else
{
lean_inc(v_a_7071_);
lean_dec(v___y_7070_);
v___x_7073_ = lean_box(0);
v_isShared_7074_ = v_isSharedCheck_7078_;
goto v_resetjp_7072_;
}
v_resetjp_7072_:
{
lean_object* v___x_7076_; 
if (v_isShared_7074_ == 0)
{
v___x_7076_ = v___x_7073_;
goto v_reusejp_7075_;
}
else
{
lean_object* v_reuseFailAlloc_7077_; 
v_reuseFailAlloc_7077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7077_, 0, v_a_7071_);
v___x_7076_ = v_reuseFailAlloc_7077_;
goto v_reusejp_7075_;
}
v_reusejp_7075_:
{
return v___x_7076_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg___boxed(lean_object* v_entriesForConst_7092_, lean_object* v_a_7093_, lean_object* v_a_7094_, lean_object* v_a_7095_){
_start:
{
lean_object* v_res_7096_; 
v_res_7096_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(v_entriesForConst_7092_, v_a_7093_, v_a_7094_);
lean_dec(v_a_7094_);
lean_dec_ref(v_a_7093_);
return v_res_7096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree(lean_object* v_00_u03b1_7097_, lean_object* v_entriesForConst_7098_, lean_object* v_a_7099_, lean_object* v_a_7100_){
_start:
{
lean_object* v___x_7102_; 
v___x_7102_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(v_entriesForConst_7098_, v_a_7099_, v_a_7100_);
return v___x_7102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___boxed(lean_object* v_00_u03b1_7103_, lean_object* v_entriesForConst_7104_, lean_object* v_a_7105_, lean_object* v_a_7106_, lean_object* v_a_7107_){
_start:
{
lean_object* v_res_7108_; 
v_res_7108_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree(v_00_u03b1_7103_, v_entriesForConst_7104_, v_a_7105_, v_a_7106_);
lean_dec(v_a_7106_);
lean_dec_ref(v_a_7105_);
return v_res_7108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0(lean_object* v_entriesForConst_7109_, lean_object* v_droppedEntriesRef_7110_, lean_object* v_droppedKeys_7111_, lean_object* v___y_7112_, lean_object* v___y_7113_, lean_object* v___y_7114_, lean_object* v___y_7115_){
_start:
{
lean_object* v_t_7118_; lean_object* v___x_7121_; 
v___x_7121_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(v_entriesForConst_7109_, v___y_7114_, v___y_7115_);
if (lean_obj_tag(v___x_7121_) == 0)
{
if (lean_obj_tag(v_droppedEntriesRef_7110_) == 1)
{
lean_object* v_a_7122_; lean_object* v_val_7123_; lean_object* v___x_7125_; uint8_t v_isShared_7126_; uint8_t v_isSharedCheck_7149_; 
v_a_7122_ = lean_ctor_get(v___x_7121_, 0);
lean_inc(v_a_7122_);
lean_dec_ref_known(v___x_7121_, 1);
v_val_7123_ = lean_ctor_get(v_droppedEntriesRef_7110_, 0);
v_isSharedCheck_7149_ = !lean_is_exclusive(v_droppedEntriesRef_7110_);
if (v_isSharedCheck_7149_ == 0)
{
v___x_7125_ = v_droppedEntriesRef_7110_;
v_isShared_7126_ = v_isSharedCheck_7149_;
goto v_resetjp_7124_;
}
else
{
lean_inc(v_val_7123_);
lean_dec(v_droppedEntriesRef_7110_);
v___x_7125_ = lean_box(0);
v_isShared_7126_ = v_isSharedCheck_7149_;
goto v_resetjp_7124_;
}
v_resetjp_7124_:
{
lean_object* v___x_7127_; 
v___x_7127_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_a_7122_, v_droppedKeys_7111_, v___y_7112_, v___y_7113_, v___y_7114_, v___y_7115_);
lean_dec(v_droppedKeys_7111_);
if (lean_obj_tag(v___x_7127_) == 0)
{
lean_object* v_a_7128_; lean_object* v_fst_7129_; lean_object* v_snd_7130_; lean_object* v___x_7131_; lean_object* v___y_7133_; 
v_a_7128_ = lean_ctor_get(v___x_7127_, 0);
lean_inc(v_a_7128_);
lean_dec_ref_known(v___x_7127_, 1);
v_fst_7129_ = lean_ctor_get(v_a_7128_, 0);
lean_inc(v_fst_7129_);
v_snd_7130_ = lean_ctor_get(v_a_7128_, 1);
lean_inc(v_snd_7130_);
lean_dec(v_a_7128_);
v___x_7131_ = lean_st_ref_get(v_val_7123_);
if (lean_obj_tag(v___x_7131_) == 0)
{
lean_object* v___x_7139_; 
v___x_7139_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___y_7133_ = v___x_7139_;
goto v___jp_7132_;
}
else
{
lean_object* v_val_7140_; 
v_val_7140_ = lean_ctor_get(v___x_7131_, 0);
lean_inc(v_val_7140_);
lean_dec_ref_known(v___x_7131_, 1);
v___y_7133_ = v_val_7140_;
goto v___jp_7132_;
}
v___jp_7132_:
{
lean_object* v___x_7134_; lean_object* v___x_7136_; 
v___x_7134_ = l_Array_append___redArg(v___y_7133_, v_fst_7129_);
lean_dec(v_fst_7129_);
if (v_isShared_7126_ == 0)
{
lean_ctor_set(v___x_7125_, 0, v___x_7134_);
v___x_7136_ = v___x_7125_;
goto v_reusejp_7135_;
}
else
{
lean_object* v_reuseFailAlloc_7138_; 
v_reuseFailAlloc_7138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7138_, 0, v___x_7134_);
v___x_7136_ = v_reuseFailAlloc_7138_;
goto v_reusejp_7135_;
}
v_reusejp_7135_:
{
lean_object* v___x_7137_; 
v___x_7137_ = lean_st_ref_swap(v_val_7123_, v___x_7136_);
lean_dec(v_val_7123_);
lean_dec(v___x_7137_);
v_t_7118_ = v_snd_7130_;
goto v___jp_7117_;
}
}
}
else
{
lean_object* v_a_7141_; lean_object* v___x_7143_; uint8_t v_isShared_7144_; uint8_t v_isSharedCheck_7148_; 
lean_del_object(v___x_7125_);
lean_dec(v_val_7123_);
v_a_7141_ = lean_ctor_get(v___x_7127_, 0);
v_isSharedCheck_7148_ = !lean_is_exclusive(v___x_7127_);
if (v_isSharedCheck_7148_ == 0)
{
v___x_7143_ = v___x_7127_;
v_isShared_7144_ = v_isSharedCheck_7148_;
goto v_resetjp_7142_;
}
else
{
lean_inc(v_a_7141_);
lean_dec(v___x_7127_);
v___x_7143_ = lean_box(0);
v_isShared_7144_ = v_isSharedCheck_7148_;
goto v_resetjp_7142_;
}
v_resetjp_7142_:
{
lean_object* v___x_7146_; 
if (v_isShared_7144_ == 0)
{
v___x_7146_ = v___x_7143_;
goto v_reusejp_7145_;
}
else
{
lean_object* v_reuseFailAlloc_7147_; 
v_reuseFailAlloc_7147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7147_, 0, v_a_7141_);
v___x_7146_ = v_reuseFailAlloc_7147_;
goto v_reusejp_7145_;
}
v_reusejp_7145_:
{
return v___x_7146_;
}
}
}
}
}
else
{
lean_object* v_a_7150_; lean_object* v___x_7151_; 
lean_dec(v_droppedEntriesRef_7110_);
v_a_7150_ = lean_ctor_get(v___x_7121_, 0);
lean_inc(v_a_7150_);
lean_dec_ref_known(v___x_7121_, 1);
v___x_7151_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_a_7150_, v_droppedKeys_7111_, v___y_7112_, v___y_7113_, v___y_7114_, v___y_7115_);
if (lean_obj_tag(v___x_7151_) == 0)
{
lean_object* v_a_7152_; 
v_a_7152_ = lean_ctor_get(v___x_7151_, 0);
lean_inc(v_a_7152_);
lean_dec_ref_known(v___x_7151_, 1);
v_t_7118_ = v_a_7152_;
goto v___jp_7117_;
}
else
{
lean_object* v_a_7153_; lean_object* v___x_7155_; uint8_t v_isShared_7156_; uint8_t v_isSharedCheck_7160_; 
v_a_7153_ = lean_ctor_get(v___x_7151_, 0);
v_isSharedCheck_7160_ = !lean_is_exclusive(v___x_7151_);
if (v_isSharedCheck_7160_ == 0)
{
v___x_7155_ = v___x_7151_;
v_isShared_7156_ = v_isSharedCheck_7160_;
goto v_resetjp_7154_;
}
else
{
lean_inc(v_a_7153_);
lean_dec(v___x_7151_);
v___x_7155_ = lean_box(0);
v_isShared_7156_ = v_isSharedCheck_7160_;
goto v_resetjp_7154_;
}
v_resetjp_7154_:
{
lean_object* v___x_7158_; 
if (v_isShared_7156_ == 0)
{
v___x_7158_ = v___x_7155_;
goto v_reusejp_7157_;
}
else
{
lean_object* v_reuseFailAlloc_7159_; 
v_reuseFailAlloc_7159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7159_, 0, v_a_7153_);
v___x_7158_ = v_reuseFailAlloc_7159_;
goto v_reusejp_7157_;
}
v_reusejp_7157_:
{
return v___x_7158_;
}
}
}
}
}
else
{
lean_object* v_a_7161_; lean_object* v___x_7163_; uint8_t v_isShared_7164_; uint8_t v_isSharedCheck_7168_; 
lean_dec(v_droppedKeys_7111_);
lean_dec(v_droppedEntriesRef_7110_);
v_a_7161_ = lean_ctor_get(v___x_7121_, 0);
v_isSharedCheck_7168_ = !lean_is_exclusive(v___x_7121_);
if (v_isSharedCheck_7168_ == 0)
{
v___x_7163_ = v___x_7121_;
v_isShared_7164_ = v_isSharedCheck_7168_;
goto v_resetjp_7162_;
}
else
{
lean_inc(v_a_7161_);
lean_dec(v___x_7121_);
v___x_7163_ = lean_box(0);
v_isShared_7164_ = v_isSharedCheck_7168_;
goto v_resetjp_7162_;
}
v_resetjp_7162_:
{
lean_object* v___x_7166_; 
if (v_isShared_7164_ == 0)
{
v___x_7166_ = v___x_7163_;
goto v_reusejp_7165_;
}
else
{
lean_object* v_reuseFailAlloc_7167_; 
v_reuseFailAlloc_7167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7167_, 0, v_a_7161_);
v___x_7166_ = v_reuseFailAlloc_7167_;
goto v_reusejp_7165_;
}
v_reusejp_7165_:
{
return v___x_7166_;
}
}
}
v___jp_7117_:
{
lean_object* v___x_7119_; lean_object* v___x_7120_; 
v___x_7119_ = lean_st_mk_ref(v_t_7118_);
v___x_7120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7120_, 0, v___x_7119_);
return v___x_7120_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0___boxed(lean_object* v_entriesForConst_7169_, lean_object* v_droppedEntriesRef_7170_, lean_object* v_droppedKeys_7171_, lean_object* v___y_7172_, lean_object* v___y_7173_, lean_object* v___y_7174_, lean_object* v___y_7175_, lean_object* v___y_7176_){
_start:
{
lean_object* v_res_7177_; 
v_res_7177_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0(v_entriesForConst_7169_, v_droppedEntriesRef_7170_, v_droppedKeys_7171_, v___y_7172_, v___y_7173_, v___y_7174_, v___y_7175_);
lean_dec(v___y_7175_);
lean_dec_ref(v___y_7174_);
lean_dec(v___y_7173_);
lean_dec_ref(v___y_7172_);
return v_res_7177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(lean_object* v_entriesForConst_7179_, lean_object* v_droppedKeys_7180_, lean_object* v_droppedEntriesRef_7181_, lean_object* v_a_7182_, lean_object* v_a_7183_, lean_object* v_a_7184_, lean_object* v_a_7185_){
_start:
{
lean_object* v_toCold_7187_; lean_object* v_options_7188_; lean_object* v___f_7189_; lean_object* v___x_7190_; lean_object* v___x_7191_; lean_object* v___x_7192_; 
v_toCold_7187_ = lean_ctor_get(v_a_7184_, 0);
v_options_7188_ = lean_ctor_get(v_toCold_7187_, 2);
v___f_7189_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_7189_, 0, v_entriesForConst_7179_);
lean_closure_set(v___f_7189_, 1, v_droppedEntriesRef_7181_);
lean_closure_set(v___f_7189_, 2, v_droppedKeys_7180_);
v___x_7190_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___closed__0));
v___x_7191_ = lean_box(0);
v___x_7192_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v___x_7190_, v_options_7188_, v___f_7189_, v___x_7191_, v_a_7182_, v_a_7183_, v_a_7184_, v_a_7185_);
return v___x_7192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___boxed(lean_object* v_entriesForConst_7193_, lean_object* v_droppedKeys_7194_, lean_object* v_droppedEntriesRef_7195_, lean_object* v_a_7196_, lean_object* v_a_7197_, lean_object* v_a_7198_, lean_object* v_a_7199_, lean_object* v_a_7200_){
_start:
{
lean_object* v_res_7201_; 
v_res_7201_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v_entriesForConst_7193_, v_droppedKeys_7194_, v_droppedEntriesRef_7195_, v_a_7196_, v_a_7197_, v_a_7198_, v_a_7199_);
lean_dec(v_a_7199_);
lean_dec_ref(v_a_7198_);
lean_dec(v_a_7197_);
lean_dec_ref(v_a_7196_);
return v_res_7201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef(lean_object* v_00_u03b1_7202_, lean_object* v_entriesForConst_7203_, lean_object* v_droppedKeys_7204_, lean_object* v_droppedEntriesRef_7205_, lean_object* v_a_7206_, lean_object* v_a_7207_, lean_object* v_a_7208_, lean_object* v_a_7209_){
_start:
{
lean_object* v___x_7211_; 
v___x_7211_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v_entriesForConst_7203_, v_droppedKeys_7204_, v_droppedEntriesRef_7205_, v_a_7206_, v_a_7207_, v_a_7208_, v_a_7209_);
return v___x_7211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___boxed(lean_object* v_00_u03b1_7212_, lean_object* v_entriesForConst_7213_, lean_object* v_droppedKeys_7214_, lean_object* v_droppedEntriesRef_7215_, lean_object* v_a_7216_, lean_object* v_a_7217_, lean_object* v_a_7218_, lean_object* v_a_7219_, lean_object* v_a_7220_){
_start:
{
lean_object* v_res_7221_; 
v_res_7221_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef(v_00_u03b1_7212_, v_entriesForConst_7213_, v_droppedKeys_7214_, v_droppedEntriesRef_7215_, v_a_7216_, v_a_7217_, v_a_7218_, v_a_7219_);
lean_dec(v_a_7219_);
lean_dec_ref(v_a_7218_);
lean_dec(v_a_7217_);
lean_dec_ref(v_a_7216_);
return v_res_7221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0(lean_object* v_moduleRef_7222_, lean_object* v_ty_7223_, lean_object* v___y_7224_, lean_object* v___y_7225_, lean_object* v___y_7226_, lean_object* v___y_7227_){
_start:
{
lean_object* v___x_7229_; lean_object* v___x_7230_; 
v___x_7229_ = lean_st_ref_get(v_moduleRef_7222_);
v___x_7230_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v___x_7229_, v_ty_7223_, v___y_7224_, v___y_7225_, v___y_7226_, v___y_7227_);
if (lean_obj_tag(v___x_7230_) == 0)
{
lean_object* v_a_7231_; lean_object* v___x_7233_; uint8_t v_isShared_7234_; uint8_t v_isSharedCheck_7241_; 
v_a_7231_ = lean_ctor_get(v___x_7230_, 0);
v_isSharedCheck_7241_ = !lean_is_exclusive(v___x_7230_);
if (v_isSharedCheck_7241_ == 0)
{
v___x_7233_ = v___x_7230_;
v_isShared_7234_ = v_isSharedCheck_7241_;
goto v_resetjp_7232_;
}
else
{
lean_inc(v_a_7231_);
lean_dec(v___x_7230_);
v___x_7233_ = lean_box(0);
v_isShared_7234_ = v_isSharedCheck_7241_;
goto v_resetjp_7232_;
}
v_resetjp_7232_:
{
lean_object* v_fst_7235_; lean_object* v_snd_7236_; lean_object* v___x_7237_; lean_object* v___x_7239_; 
v_fst_7235_ = lean_ctor_get(v_a_7231_, 0);
lean_inc(v_fst_7235_);
v_snd_7236_ = lean_ctor_get(v_a_7231_, 1);
lean_inc(v_snd_7236_);
lean_dec(v_a_7231_);
v___x_7237_ = lean_st_ref_swap(v_moduleRef_7222_, v_snd_7236_);
lean_dec(v___x_7237_);
if (v_isShared_7234_ == 0)
{
lean_ctor_set(v___x_7233_, 0, v_fst_7235_);
v___x_7239_ = v___x_7233_;
goto v_reusejp_7238_;
}
else
{
lean_object* v_reuseFailAlloc_7240_; 
v_reuseFailAlloc_7240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7240_, 0, v_fst_7235_);
v___x_7239_ = v_reuseFailAlloc_7240_;
goto v_reusejp_7238_;
}
v_reusejp_7238_:
{
return v___x_7239_;
}
}
}
else
{
lean_object* v_a_7242_; lean_object* v___x_7244_; uint8_t v_isShared_7245_; uint8_t v_isSharedCheck_7249_; 
v_a_7242_ = lean_ctor_get(v___x_7230_, 0);
v_isSharedCheck_7249_ = !lean_is_exclusive(v___x_7230_);
if (v_isSharedCheck_7249_ == 0)
{
v___x_7244_ = v___x_7230_;
v_isShared_7245_ = v_isSharedCheck_7249_;
goto v_resetjp_7243_;
}
else
{
lean_inc(v_a_7242_);
lean_dec(v___x_7230_);
v___x_7244_ = lean_box(0);
v_isShared_7245_ = v_isSharedCheck_7249_;
goto v_resetjp_7243_;
}
v_resetjp_7243_:
{
lean_object* v___x_7247_; 
if (v_isShared_7245_ == 0)
{
v___x_7247_ = v___x_7244_;
goto v_reusejp_7246_;
}
else
{
lean_object* v_reuseFailAlloc_7248_; 
v_reuseFailAlloc_7248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7248_, 0, v_a_7242_);
v___x_7247_ = v_reuseFailAlloc_7248_;
goto v_reusejp_7246_;
}
v_reusejp_7246_:
{
return v___x_7247_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0___boxed(lean_object* v_moduleRef_7250_, lean_object* v_ty_7251_, lean_object* v___y_7252_, lean_object* v___y_7253_, lean_object* v___y_7254_, lean_object* v___y_7255_, lean_object* v___y_7256_){
_start:
{
lean_object* v_res_7257_; 
v_res_7257_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0(v_moduleRef_7250_, v_ty_7251_, v___y_7252_, v___y_7253_, v___y_7254_, v___y_7255_);
lean_dec(v___y_7255_);
lean_dec_ref(v___y_7254_);
lean_dec(v___y_7253_);
lean_dec_ref(v___y_7252_);
lean_dec(v_moduleRef_7250_);
return v_res_7257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(lean_object* v_moduleRef_7259_, lean_object* v_ty_7260_, lean_object* v_a_7261_, lean_object* v_a_7262_, lean_object* v_a_7263_, lean_object* v_a_7264_){
_start:
{
lean_object* v_toCold_7266_; lean_object* v_options_7267_; lean_object* v___f_7268_; lean_object* v___x_7269_; lean_object* v___x_7270_; lean_object* v___x_7271_; 
v_toCold_7266_ = lean_ctor_get(v_a_7263_, 0);
v_options_7267_ = lean_ctor_get(v_toCold_7266_, 2);
v___f_7268_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_7268_, 0, v_moduleRef_7259_);
lean_closure_set(v___f_7268_, 1, v_ty_7260_);
v___x_7269_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___closed__0));
v___x_7270_ = lean_box(0);
v___x_7271_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v___x_7269_, v_options_7267_, v___f_7268_, v___x_7270_, v_a_7261_, v_a_7262_, v_a_7263_, v_a_7264_);
return v___x_7271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___boxed(lean_object* v_moduleRef_7272_, lean_object* v_ty_7273_, lean_object* v_a_7274_, lean_object* v_a_7275_, lean_object* v_a_7276_, lean_object* v_a_7277_, lean_object* v_a_7278_){
_start:
{
lean_object* v_res_7279_; 
v_res_7279_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(v_moduleRef_7272_, v_ty_7273_, v_a_7274_, v_a_7275_, v_a_7276_, v_a_7277_);
lean_dec(v_a_7277_);
lean_dec_ref(v_a_7276_);
lean_dec(v_a_7275_);
lean_dec_ref(v_a_7274_);
return v_res_7279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches(lean_object* v_00_u03b1_7280_, lean_object* v_moduleRef_7281_, lean_object* v_ty_7282_, lean_object* v_a_7283_, lean_object* v_a_7284_, lean_object* v_a_7285_, lean_object* v_a_7286_){
_start:
{
lean_object* v___x_7288_; 
v___x_7288_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(v_moduleRef_7281_, v_ty_7282_, v_a_7283_, v_a_7284_, v_a_7285_, v_a_7286_);
return v___x_7288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___boxed(lean_object* v_00_u03b1_7289_, lean_object* v_moduleRef_7290_, lean_object* v_ty_7291_, lean_object* v_a_7292_, lean_object* v_a_7293_, lean_object* v_a_7294_, lean_object* v_a_7295_, lean_object* v_a_7296_){
_start:
{
lean_object* v_res_7297_; 
v_res_7297_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches(v_00_u03b1_7289_, v_moduleRef_7290_, v_ty_7291_, v_a_7292_, v_a_7293_, v_a_7294_, v_a_7295_);
lean_dec(v_a_7295_);
lean_dec_ref(v_a_7294_);
lean_dec(v_a_7293_);
lean_dec_ref(v_a_7292_);
return v_res_7297_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(lean_object* v_adjustResult_7298_, lean_object* v_j_7299_, size_t v_sz_7300_, size_t v_i_7301_, lean_object* v_bs_7302_){
_start:
{
uint8_t v___x_7303_; 
v___x_7303_ = lean_usize_dec_lt(v_i_7301_, v_sz_7300_);
if (v___x_7303_ == 0)
{
lean_dec(v_j_7299_);
lean_dec(v_adjustResult_7298_);
return v_bs_7302_;
}
else
{
lean_object* v_v_7304_; lean_object* v___x_7305_; lean_object* v_bs_x27_7306_; lean_object* v___x_7307_; size_t v___x_7308_; size_t v___x_7309_; lean_object* v___x_7310_; 
v_v_7304_ = lean_array_uget(v_bs_7302_, v_i_7301_);
v___x_7305_ = lean_unsigned_to_nat(0u);
v_bs_x27_7306_ = lean_array_uset(v_bs_7302_, v_i_7301_, v___x_7305_);
lean_inc(v_adjustResult_7298_);
lean_inc(v_j_7299_);
v___x_7307_ = lean_apply_2(v_adjustResult_7298_, v_j_7299_, v_v_7304_);
v___x_7308_ = ((size_t)1ULL);
v___x_7309_ = lean_usize_add(v_i_7301_, v___x_7308_);
v___x_7310_ = lean_array_uset(v_bs_x27_7306_, v_i_7301_, v___x_7307_);
v_i_7301_ = v___x_7309_;
v_bs_7302_ = v___x_7310_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg___boxed(lean_object* v_adjustResult_7312_, lean_object* v_j_7313_, lean_object* v_sz_7314_, lean_object* v_i_7315_, lean_object* v_bs_7316_){
_start:
{
size_t v_sz_boxed_7317_; size_t v_i_boxed_7318_; lean_object* v_res_7319_; 
v_sz_boxed_7317_ = lean_unbox_usize(v_sz_7314_);
lean_dec(v_sz_7314_);
v_i_boxed_7318_ = lean_unbox_usize(v_i_7315_);
lean_dec(v_i_7315_);
v_res_7319_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(v_adjustResult_7312_, v_j_7313_, v_sz_boxed_7317_, v_i_boxed_7318_, v_bs_7316_);
return v_res_7319_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(lean_object* v_adjustResult_7320_, lean_object* v_j_7321_, lean_object* v_as_7322_, size_t v_i_7323_, size_t v_stop_7324_, lean_object* v_b_7325_){
_start:
{
uint8_t v___x_7326_; 
v___x_7326_ = lean_usize_dec_eq(v_i_7323_, v_stop_7324_);
if (v___x_7326_ == 0)
{
lean_object* v___x_7327_; size_t v_sz_7328_; size_t v___x_7329_; lean_object* v___x_7330_; lean_object* v___x_7331_; size_t v___x_7332_; size_t v___x_7333_; 
v___x_7327_ = lean_array_uget_borrowed(v_as_7322_, v_i_7323_);
v_sz_7328_ = lean_array_size(v___x_7327_);
v___x_7329_ = ((size_t)0ULL);
lean_inc(v___x_7327_);
lean_inc(v_j_7321_);
lean_inc(v_adjustResult_7320_);
v___x_7330_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(v_adjustResult_7320_, v_j_7321_, v_sz_7328_, v___x_7329_, v___x_7327_);
v___x_7331_ = l_Array_append___redArg(v_b_7325_, v___x_7330_);
lean_dec_ref(v___x_7330_);
v___x_7332_ = ((size_t)1ULL);
v___x_7333_ = lean_usize_add(v_i_7323_, v___x_7332_);
v_i_7323_ = v___x_7333_;
v_b_7325_ = v___x_7331_;
goto _start;
}
else
{
lean_dec(v_j_7321_);
lean_dec(v_adjustResult_7320_);
return v_b_7325_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg___boxed(lean_object* v_adjustResult_7335_, lean_object* v_j_7336_, lean_object* v_as_7337_, lean_object* v_i_7338_, lean_object* v_stop_7339_, lean_object* v_b_7340_){
_start:
{
size_t v_i_boxed_7341_; size_t v_stop_boxed_7342_; lean_object* v_res_7343_; 
v_i_boxed_7341_ = lean_unbox_usize(v_i_7338_);
lean_dec(v_i_7338_);
v_stop_boxed_7342_ = lean_unbox_usize(v_stop_7339_);
lean_dec(v_stop_7339_);
v_res_7343_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7335_, v_j_7336_, v_as_7337_, v_i_boxed_7341_, v_stop_boxed_7342_, v_b_7340_);
lean_dec_ref(v_as_7337_);
return v_res_7343_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(lean_object* v_n_7344_, lean_object* v_aa_7345_, lean_object* v_adjustResult_7346_, lean_object* v_n_7347_, lean_object* v_j_7348_, lean_object* v_a_7349_){
_start:
{
lean_object* v_zero_7350_; uint8_t v_isZero_7351_; 
v_zero_7350_ = lean_unsigned_to_nat(0u);
v_isZero_7351_ = lean_nat_dec_eq(v_j_7348_, v_zero_7350_);
if (v_isZero_7351_ == 1)
{
lean_dec(v_j_7348_);
lean_dec(v_adjustResult_7346_);
return v_a_7349_;
}
else
{
lean_object* v_one_7352_; lean_object* v_n_7353_; lean_object* v___x_7354_; lean_object* v___x_7355_; lean_object* v_j_7356_; lean_object* v_b_7357_; lean_object* v___x_7358_; uint8_t v___x_7359_; 
v_one_7352_ = lean_unsigned_to_nat(1u);
v_n_7353_ = lean_nat_sub(v_j_7348_, v_one_7352_);
v___x_7354_ = lean_nat_sub(v_n_7347_, v_j_7348_);
lean_dec(v_j_7348_);
v___x_7355_ = lean_nat_sub(v_n_7344_, v_one_7352_);
v_j_7356_ = lean_nat_sub(v___x_7355_, v___x_7354_);
lean_dec(v___x_7354_);
lean_dec(v___x_7355_);
v_b_7357_ = lean_array_fget_borrowed(v_aa_7345_, v_j_7356_);
v___x_7358_ = lean_array_get_size(v_b_7357_);
v___x_7359_ = lean_nat_dec_lt(v_zero_7350_, v___x_7358_);
if (v___x_7359_ == 0)
{
lean_dec(v_j_7356_);
v_j_7348_ = v_n_7353_;
goto _start;
}
else
{
size_t v___x_7361_; size_t v___x_7362_; lean_object* v___x_7363_; 
v___x_7361_ = ((size_t)0ULL);
v___x_7362_ = lean_usize_of_nat(v___x_7358_);
lean_inc(v_adjustResult_7346_);
v___x_7363_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7346_, v_j_7356_, v_b_7357_, v___x_7361_, v___x_7362_, v_a_7349_);
v_j_7348_ = v_n_7353_;
v_a_7349_ = v___x_7363_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_n_7365_, lean_object* v_aa_7366_, lean_object* v_adjustResult_7367_, lean_object* v_n_7368_, lean_object* v_j_7369_, lean_object* v_a_7370_){
_start:
{
lean_object* v_res_7371_; 
v_res_7371_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7365_, v_aa_7366_, v_adjustResult_7367_, v_n_7368_, v_j_7369_, v_a_7370_);
lean_dec(v_n_7368_);
lean_dec_ref(v_aa_7366_);
lean_dec(v_n_7365_);
return v_res_7371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(lean_object* v_n_7372_, lean_object* v_adjustResult_7373_, lean_object* v_aa_7374_, lean_object* v_n_7375_, lean_object* v_j_7376_, lean_object* v_a_7377_){
_start:
{
lean_object* v_zero_7378_; uint8_t v_isZero_7379_; 
v_zero_7378_ = lean_unsigned_to_nat(0u);
v_isZero_7379_ = lean_nat_dec_eq(v_j_7376_, v_zero_7378_);
if (v_isZero_7379_ == 1)
{
lean_dec(v_adjustResult_7373_);
return v_a_7377_;
}
else
{
lean_object* v_one_7380_; lean_object* v_n_7381_; lean_object* v___x_7382_; lean_object* v___x_7383_; lean_object* v_j_7384_; lean_object* v_b_7385_; lean_object* v___x_7386_; uint8_t v___x_7387_; 
v_one_7380_ = lean_unsigned_to_nat(1u);
v_n_7381_ = lean_nat_sub(v_j_7376_, v_one_7380_);
v___x_7382_ = lean_nat_sub(v_n_7375_, v_j_7376_);
v___x_7383_ = lean_nat_sub(v_n_7372_, v_one_7380_);
v_j_7384_ = lean_nat_sub(v___x_7383_, v___x_7382_);
lean_dec(v___x_7382_);
lean_dec(v___x_7383_);
v_b_7385_ = lean_array_fget_borrowed(v_aa_7374_, v_j_7384_);
v___x_7386_ = lean_array_get_size(v_b_7385_);
v___x_7387_ = lean_nat_dec_lt(v_zero_7378_, v___x_7386_);
if (v___x_7387_ == 0)
{
lean_object* v___x_7388_; 
lean_dec(v_j_7384_);
v___x_7388_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7372_, v_aa_7374_, v_adjustResult_7373_, v_n_7375_, v_n_7381_, v_a_7377_);
return v___x_7388_;
}
else
{
size_t v___x_7389_; size_t v___x_7390_; lean_object* v___x_7391_; lean_object* v___x_7392_; 
v___x_7389_ = ((size_t)0ULL);
v___x_7390_ = lean_usize_of_nat(v___x_7386_);
lean_inc(v_adjustResult_7373_);
v___x_7391_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7373_, v_j_7384_, v_b_7385_, v___x_7389_, v___x_7390_, v_a_7377_);
v___x_7392_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7372_, v_aa_7374_, v_adjustResult_7373_, v_n_7375_, v_n_7381_, v___x_7391_);
return v___x_7392_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg___boxed(lean_object* v_n_7393_, lean_object* v_adjustResult_7394_, lean_object* v_aa_7395_, lean_object* v_n_7396_, lean_object* v_j_7397_, lean_object* v_a_7398_){
_start:
{
lean_object* v_res_7399_; 
v_res_7399_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(v_n_7393_, v_adjustResult_7394_, v_aa_7395_, v_n_7396_, v_j_7397_, v_a_7398_);
lean_dec(v_j_7397_);
lean_dec(v_n_7396_);
lean_dec_ref(v_aa_7395_);
lean_dec(v_n_7393_);
return v_res_7399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(lean_object* v_adjustResult_7400_, lean_object* v_mr_7401_, lean_object* v_a_7402_){
_start:
{
lean_object* v_n_7403_; lean_object* v___x_7404_; 
v_n_7403_ = lean_array_get_size(v_mr_7401_);
v___x_7404_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(v_n_7403_, v_adjustResult_7400_, v_mr_7401_, v_n_7403_, v_n_7403_, v_a_7402_);
return v___x_7404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg___boxed(lean_object* v_adjustResult_7405_, lean_object* v_mr_7406_, lean_object* v_a_7407_){
_start:
{
lean_object* v_res_7408_; 
v_res_7408_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7405_, v_mr_7406_, v_a_7407_);
lean_dec_ref(v_mr_7406_);
return v_res_7408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(lean_object* v_moduleTreeRef_7409_, lean_object* v_ref_7410_, lean_object* v_addEntry_7411_, lean_object* v_droppedKeys_7412_, lean_object* v_constantsPerTask_7413_, lean_object* v_droppedEntriesRef_7414_, lean_object* v_adjustResult_7415_, lean_object* v_ty_7416_, lean_object* v_a_7417_, lean_object* v_a_7418_, lean_object* v_a_7419_, lean_object* v_a_7420_){
_start:
{
lean_object* v___x_7422_; 
lean_inc_ref(v_ty_7416_);
v___x_7422_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(v_moduleTreeRef_7409_, v_ty_7416_, v_a_7417_, v_a_7418_, v_a_7419_, v_a_7420_);
if (lean_obj_tag(v___x_7422_) == 0)
{
lean_object* v_a_7423_; lean_object* v___x_7424_; 
v_a_7423_ = lean_ctor_get(v___x_7422_, 0);
lean_inc(v_a_7423_);
lean_dec_ref_known(v___x_7422_, 1);
v___x_7424_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(v_ref_7410_, v_addEntry_7411_, v_droppedKeys_7412_, v_constantsPerTask_7413_, v_droppedEntriesRef_7414_, v_ty_7416_, v_a_7417_, v_a_7418_, v_a_7419_, v_a_7420_);
if (lean_obj_tag(v___x_7424_) == 0)
{
lean_object* v_a_7425_; lean_object* v___x_7427_; uint8_t v_isShared_7428_; uint8_t v_isSharedCheck_7438_; 
v_a_7425_ = lean_ctor_get(v___x_7424_, 0);
v_isSharedCheck_7438_ = !lean_is_exclusive(v___x_7424_);
if (v_isSharedCheck_7438_ == 0)
{
v___x_7427_ = v___x_7424_;
v_isShared_7428_ = v_isSharedCheck_7438_;
goto v_resetjp_7426_;
}
else
{
lean_inc(v_a_7425_);
lean_dec(v___x_7424_);
v___x_7427_ = lean_box(0);
v_isShared_7428_ = v_isSharedCheck_7438_;
goto v_resetjp_7426_;
}
v_resetjp_7426_:
{
lean_object* v___x_7429_; lean_object* v___x_7430_; lean_object* v___x_7431_; lean_object* v___x_7432_; lean_object* v___x_7433_; lean_object* v___x_7434_; lean_object* v___x_7436_; 
v___x_7429_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_a_7423_);
v___x_7430_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_a_7425_);
v___x_7431_ = lean_nat_add(v___x_7429_, v___x_7430_);
lean_dec(v___x_7430_);
lean_dec(v___x_7429_);
v___x_7432_ = lean_mk_empty_array_with_capacity(v___x_7431_);
lean_dec(v___x_7431_);
lean_inc(v_adjustResult_7415_);
v___x_7433_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7415_, v_a_7423_, v___x_7432_);
lean_dec(v_a_7423_);
v___x_7434_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7415_, v_a_7425_, v___x_7433_);
lean_dec(v_a_7425_);
if (v_isShared_7428_ == 0)
{
lean_ctor_set(v___x_7427_, 0, v___x_7434_);
v___x_7436_ = v___x_7427_;
goto v_reusejp_7435_;
}
else
{
lean_object* v_reuseFailAlloc_7437_; 
v_reuseFailAlloc_7437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7437_, 0, v___x_7434_);
v___x_7436_ = v_reuseFailAlloc_7437_;
goto v_reusejp_7435_;
}
v_reusejp_7435_:
{
return v___x_7436_;
}
}
}
else
{
lean_object* v_a_7439_; lean_object* v___x_7441_; uint8_t v_isShared_7442_; uint8_t v_isSharedCheck_7446_; 
lean_dec(v_a_7423_);
lean_dec(v_adjustResult_7415_);
v_a_7439_ = lean_ctor_get(v___x_7424_, 0);
v_isSharedCheck_7446_ = !lean_is_exclusive(v___x_7424_);
if (v_isSharedCheck_7446_ == 0)
{
v___x_7441_ = v___x_7424_;
v_isShared_7442_ = v_isSharedCheck_7446_;
goto v_resetjp_7440_;
}
else
{
lean_inc(v_a_7439_);
lean_dec(v___x_7424_);
v___x_7441_ = lean_box(0);
v_isShared_7442_ = v_isSharedCheck_7446_;
goto v_resetjp_7440_;
}
v_resetjp_7440_:
{
lean_object* v___x_7444_; 
if (v_isShared_7442_ == 0)
{
v___x_7444_ = v___x_7441_;
goto v_reusejp_7443_;
}
else
{
lean_object* v_reuseFailAlloc_7445_; 
v_reuseFailAlloc_7445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7445_, 0, v_a_7439_);
v___x_7444_ = v_reuseFailAlloc_7445_;
goto v_reusejp_7443_;
}
v_reusejp_7443_:
{
return v___x_7444_;
}
}
}
}
else
{
lean_object* v_a_7447_; lean_object* v___x_7449_; uint8_t v_isShared_7450_; uint8_t v_isSharedCheck_7454_; 
lean_dec_ref(v_ty_7416_);
lean_dec(v_adjustResult_7415_);
lean_dec(v_droppedEntriesRef_7414_);
lean_dec(v_constantsPerTask_7413_);
lean_dec(v_droppedKeys_7412_);
lean_dec_ref(v_addEntry_7411_);
v_a_7447_ = lean_ctor_get(v___x_7422_, 0);
v_isSharedCheck_7454_ = !lean_is_exclusive(v___x_7422_);
if (v_isSharedCheck_7454_ == 0)
{
v___x_7449_ = v___x_7422_;
v_isShared_7450_ = v_isSharedCheck_7454_;
goto v_resetjp_7448_;
}
else
{
lean_inc(v_a_7447_);
lean_dec(v___x_7422_);
v___x_7449_ = lean_box(0);
v_isShared_7450_ = v_isSharedCheck_7454_;
goto v_resetjp_7448_;
}
v_resetjp_7448_:
{
lean_object* v___x_7452_; 
if (v_isShared_7450_ == 0)
{
v___x_7452_ = v___x_7449_;
goto v_reusejp_7451_;
}
else
{
lean_object* v_reuseFailAlloc_7453_; 
v_reuseFailAlloc_7453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7453_, 0, v_a_7447_);
v___x_7452_ = v_reuseFailAlloc_7453_;
goto v_reusejp_7451_;
}
v_reusejp_7451_:
{
return v___x_7452_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg___boxed(lean_object* v_moduleTreeRef_7455_, lean_object* v_ref_7456_, lean_object* v_addEntry_7457_, lean_object* v_droppedKeys_7458_, lean_object* v_constantsPerTask_7459_, lean_object* v_droppedEntriesRef_7460_, lean_object* v_adjustResult_7461_, lean_object* v_ty_7462_, lean_object* v_a_7463_, lean_object* v_a_7464_, lean_object* v_a_7465_, lean_object* v_a_7466_, lean_object* v_a_7467_){
_start:
{
lean_object* v_res_7468_; 
v_res_7468_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_moduleTreeRef_7455_, v_ref_7456_, v_addEntry_7457_, v_droppedKeys_7458_, v_constantsPerTask_7459_, v_droppedEntriesRef_7460_, v_adjustResult_7461_, v_ty_7462_, v_a_7463_, v_a_7464_, v_a_7465_, v_a_7466_);
lean_dec(v_a_7466_);
lean_dec_ref(v_a_7465_);
lean_dec(v_a_7464_);
lean_dec_ref(v_a_7463_);
lean_dec(v_ref_7456_);
return v_res_7468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt(lean_object* v_00_u03b1_7469_, lean_object* v_00_u03b2_7470_, lean_object* v_moduleTreeRef_7471_, lean_object* v_ref_7472_, lean_object* v_addEntry_7473_, lean_object* v_droppedKeys_7474_, lean_object* v_constantsPerTask_7475_, lean_object* v_droppedEntriesRef_7476_, lean_object* v_adjustResult_7477_, lean_object* v_ty_7478_, lean_object* v_a_7479_, lean_object* v_a_7480_, lean_object* v_a_7481_, lean_object* v_a_7482_){
_start:
{
lean_object* v___x_7484_; 
v___x_7484_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_moduleTreeRef_7471_, v_ref_7472_, v_addEntry_7473_, v_droppedKeys_7474_, v_constantsPerTask_7475_, v_droppedEntriesRef_7476_, v_adjustResult_7477_, v_ty_7478_, v_a_7479_, v_a_7480_, v_a_7481_, v_a_7482_);
return v___x_7484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___boxed(lean_object* v_00_u03b1_7485_, lean_object* v_00_u03b2_7486_, lean_object* v_moduleTreeRef_7487_, lean_object* v_ref_7488_, lean_object* v_addEntry_7489_, lean_object* v_droppedKeys_7490_, lean_object* v_constantsPerTask_7491_, lean_object* v_droppedEntriesRef_7492_, lean_object* v_adjustResult_7493_, lean_object* v_ty_7494_, lean_object* v_a_7495_, lean_object* v_a_7496_, lean_object* v_a_7497_, lean_object* v_a_7498_, lean_object* v_a_7499_){
_start:
{
lean_object* v_res_7500_; 
v_res_7500_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt(v_00_u03b1_7485_, v_00_u03b2_7486_, v_moduleTreeRef_7487_, v_ref_7488_, v_addEntry_7489_, v_droppedKeys_7490_, v_constantsPerTask_7491_, v_droppedEntriesRef_7492_, v_adjustResult_7493_, v_ty_7494_, v_a_7495_, v_a_7496_, v_a_7497_, v_a_7498_);
lean_dec(v_a_7498_);
lean_dec_ref(v_a_7497_);
lean_dec(v_a_7496_);
lean_dec_ref(v_a_7495_);
lean_dec(v_ref_7488_);
return v_res_7500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0(lean_object* v_00_u03b1_7501_, lean_object* v_00_u03b2_7502_, lean_object* v_adjustResult_7503_, lean_object* v_mr_7504_, lean_object* v_a_7505_){
_start:
{
lean_object* v___x_7506_; 
v___x_7506_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7503_, v_mr_7504_, v_a_7505_);
return v___x_7506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___boxed(lean_object* v_00_u03b1_7507_, lean_object* v_00_u03b2_7508_, lean_object* v_adjustResult_7509_, lean_object* v_mr_7510_, lean_object* v_a_7511_){
_start:
{
lean_object* v_res_7512_; 
v_res_7512_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0(v_00_u03b1_7507_, v_00_u03b2_7508_, v_adjustResult_7509_, v_mr_7510_, v_a_7511_);
lean_dec_ref(v_mr_7510_);
return v_res_7512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0(lean_object* v_00_u03b1_7513_, lean_object* v_00_u03b2_7514_, lean_object* v_adjustResult_7515_, lean_object* v_j_7516_, size_t v_sz_7517_, size_t v_i_7518_, lean_object* v_bs_7519_){
_start:
{
lean_object* v___x_7520_; 
v___x_7520_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(v_adjustResult_7515_, v_j_7516_, v_sz_7517_, v_i_7518_, v_bs_7519_);
return v___x_7520_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___boxed(lean_object* v_00_u03b1_7521_, lean_object* v_00_u03b2_7522_, lean_object* v_adjustResult_7523_, lean_object* v_j_7524_, lean_object* v_sz_7525_, lean_object* v_i_7526_, lean_object* v_bs_7527_){
_start:
{
size_t v_sz_boxed_7528_; size_t v_i_boxed_7529_; lean_object* v_res_7530_; 
v_sz_boxed_7528_ = lean_unbox_usize(v_sz_7525_);
lean_dec(v_sz_7525_);
v_i_boxed_7529_ = lean_unbox_usize(v_i_7526_);
lean_dec(v_i_7526_);
v_res_7530_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0(v_00_u03b1_7521_, v_00_u03b2_7522_, v_adjustResult_7523_, v_j_7524_, v_sz_boxed_7528_, v_i_boxed_7529_, v_bs_7527_);
return v_res_7530_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1(lean_object* v_00_u03b1_7531_, lean_object* v_00_u03b2_7532_, lean_object* v_adjustResult_7533_, lean_object* v_j_7534_, lean_object* v_as_7535_, size_t v_i_7536_, size_t v_stop_7537_, lean_object* v_b_7538_){
_start:
{
lean_object* v___x_7539_; 
v___x_7539_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7533_, v_j_7534_, v_as_7535_, v_i_7536_, v_stop_7537_, v_b_7538_);
return v___x_7539_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___boxed(lean_object* v_00_u03b1_7540_, lean_object* v_00_u03b2_7541_, lean_object* v_adjustResult_7542_, lean_object* v_j_7543_, lean_object* v_as_7544_, lean_object* v_i_7545_, lean_object* v_stop_7546_, lean_object* v_b_7547_){
_start:
{
size_t v_i_boxed_7548_; size_t v_stop_boxed_7549_; lean_object* v_res_7550_; 
v_i_boxed_7548_ = lean_unbox_usize(v_i_7545_);
lean_dec(v_i_7545_);
v_stop_boxed_7549_ = lean_unbox_usize(v_stop_7546_);
lean_dec(v_stop_7546_);
v_res_7550_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1(v_00_u03b1_7540_, v_00_u03b2_7541_, v_adjustResult_7542_, v_j_7543_, v_as_7544_, v_i_boxed_7548_, v_stop_boxed_7549_, v_b_7547_);
lean_dec_ref(v_as_7544_);
return v_res_7550_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2(lean_object* v_00_u03b2_7551_, lean_object* v_n_7552_, lean_object* v_00_u03b1_7553_, lean_object* v_adjustResult_7554_, lean_object* v_aa_7555_, lean_object* v_n_7556_, lean_object* v_j_7557_, lean_object* v_a_7558_, lean_object* v_a_7559_){
_start:
{
lean_object* v___x_7560_; 
v___x_7560_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(v_n_7552_, v_adjustResult_7554_, v_aa_7555_, v_n_7556_, v_j_7557_, v_a_7559_);
return v___x_7560_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___boxed(lean_object* v_00_u03b2_7561_, lean_object* v_n_7562_, lean_object* v_00_u03b1_7563_, lean_object* v_adjustResult_7564_, lean_object* v_aa_7565_, lean_object* v_n_7566_, lean_object* v_j_7567_, lean_object* v_a_7568_, lean_object* v_a_7569_){
_start:
{
lean_object* v_res_7570_; 
v_res_7570_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2(v_00_u03b2_7561_, v_n_7562_, v_00_u03b1_7563_, v_adjustResult_7564_, v_aa_7565_, v_n_7566_, v_j_7567_, v_a_7568_, v_a_7569_);
lean_dec(v_j_7567_);
lean_dec(v_n_7566_);
lean_dec_ref(v_aa_7565_);
lean_dec(v_n_7562_);
return v_res_7570_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_7571_, lean_object* v_n_7572_, lean_object* v_00_u03b1_7573_, lean_object* v_aa_7574_, lean_object* v_adjustResult_7575_, lean_object* v_n_7576_, lean_object* v_j_7577_, lean_object* v_a_7578_, lean_object* v_a_7579_){
_start:
{
lean_object* v___x_7580_; 
v___x_7580_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7572_, v_aa_7574_, v_adjustResult_7575_, v_n_7576_, v_j_7577_, v_a_7579_);
return v___x_7580_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b2_7581_, lean_object* v_n_7582_, lean_object* v_00_u03b1_7583_, lean_object* v_aa_7584_, lean_object* v_adjustResult_7585_, lean_object* v_n_7586_, lean_object* v_j_7587_, lean_object* v_a_7588_, lean_object* v_a_7589_){
_start:
{
lean_object* v_res_7590_; 
v_res_7590_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3(v_00_u03b2_7581_, v_n_7582_, v_00_u03b1_7583_, v_aa_7584_, v_adjustResult_7585_, v_n_7586_, v_j_7587_, v_a_7588_, v_a_7589_);
lean_dec(v_n_7586_);
lean_dec_ref(v_aa_7584_);
lean_dec(v_n_7582_);
return v_res_7590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg___lam__0(lean_object* v_x_7591_, lean_object* v_v_7592_){
_start:
{
lean_inc(v_v_7592_);
return v_v_7592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg___lam__0___boxed(lean_object* v_x_7593_, lean_object* v_v_7594_){
_start:
{
lean_object* v_res_7595_; 
v_res_7595_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg___lam__0(v_x_7593_, v_v_7594_);
lean_dec(v_v_7594_);
lean_dec(v_x_7593_);
return v_res_7595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg(lean_object* v_ref_7597_, lean_object* v_addEntry_7598_, lean_object* v_droppedKeys_7599_, lean_object* v_constantsPerTask_7600_, lean_object* v_droppedEntriesRef_7601_, lean_object* v_ty_7602_, lean_object* v_a_7603_, lean_object* v_a_7604_, lean_object* v_a_7605_, lean_object* v_a_7606_){
_start:
{
lean_object* v___f_7608_; lean_object* v___x_7609_; 
v___f_7608_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_findMatches___redArg___closed__0));
lean_inc(v_droppedEntriesRef_7601_);
lean_inc(v_droppedKeys_7599_);
lean_inc_ref(v_addEntry_7598_);
v___x_7609_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v_addEntry_7598_, v_droppedKeys_7599_, v_droppedEntriesRef_7601_, v_a_7603_, v_a_7604_, v_a_7605_, v_a_7606_);
if (lean_obj_tag(v___x_7609_) == 0)
{
lean_object* v_a_7610_; lean_object* v___x_7611_; 
v_a_7610_ = lean_ctor_get(v___x_7609_, 0);
lean_inc(v_a_7610_);
lean_dec_ref_known(v___x_7609_, 1);
v___x_7611_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_a_7610_, v_ref_7597_, v_addEntry_7598_, v_droppedKeys_7599_, v_constantsPerTask_7600_, v_droppedEntriesRef_7601_, v___f_7608_, v_ty_7602_, v_a_7603_, v_a_7604_, v_a_7605_, v_a_7606_);
return v___x_7611_;
}
else
{
lean_object* v_a_7612_; lean_object* v___x_7614_; uint8_t v_isShared_7615_; uint8_t v_isSharedCheck_7619_; 
lean_dec_ref(v_ty_7602_);
lean_dec(v_droppedEntriesRef_7601_);
lean_dec(v_constantsPerTask_7600_);
lean_dec(v_droppedKeys_7599_);
lean_dec_ref(v_addEntry_7598_);
v_a_7612_ = lean_ctor_get(v___x_7609_, 0);
v_isSharedCheck_7619_ = !lean_is_exclusive(v___x_7609_);
if (v_isSharedCheck_7619_ == 0)
{
v___x_7614_ = v___x_7609_;
v_isShared_7615_ = v_isSharedCheck_7619_;
goto v_resetjp_7613_;
}
else
{
lean_inc(v_a_7612_);
lean_dec(v___x_7609_);
v___x_7614_ = lean_box(0);
v_isShared_7615_ = v_isSharedCheck_7619_;
goto v_resetjp_7613_;
}
v_resetjp_7613_:
{
lean_object* v___x_7617_; 
if (v_isShared_7615_ == 0)
{
v___x_7617_ = v___x_7614_;
goto v_reusejp_7616_;
}
else
{
lean_object* v_reuseFailAlloc_7618_; 
v_reuseFailAlloc_7618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7618_, 0, v_a_7612_);
v___x_7617_ = v_reuseFailAlloc_7618_;
goto v_reusejp_7616_;
}
v_reusejp_7616_:
{
return v___x_7617_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg___boxed(lean_object* v_ref_7620_, lean_object* v_addEntry_7621_, lean_object* v_droppedKeys_7622_, lean_object* v_constantsPerTask_7623_, lean_object* v_droppedEntriesRef_7624_, lean_object* v_ty_7625_, lean_object* v_a_7626_, lean_object* v_a_7627_, lean_object* v_a_7628_, lean_object* v_a_7629_, lean_object* v_a_7630_){
_start:
{
lean_object* v_res_7631_; 
v_res_7631_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg(v_ref_7620_, v_addEntry_7621_, v_droppedKeys_7622_, v_constantsPerTask_7623_, v_droppedEntriesRef_7624_, v_ty_7625_, v_a_7626_, v_a_7627_, v_a_7628_, v_a_7629_);
lean_dec(v_a_7629_);
lean_dec_ref(v_a_7628_);
lean_dec(v_a_7627_);
lean_dec_ref(v_a_7626_);
lean_dec(v_ref_7620_);
return v_res_7631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches(lean_object* v_00_u03b1_7632_, lean_object* v_ref_7633_, lean_object* v_addEntry_7634_, lean_object* v_droppedKeys_7635_, lean_object* v_constantsPerTask_7636_, lean_object* v_droppedEntriesRef_7637_, lean_object* v_ty_7638_, lean_object* v_a_7639_, lean_object* v_a_7640_, lean_object* v_a_7641_, lean_object* v_a_7642_){
_start:
{
lean_object* v___x_7644_; 
v___x_7644_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg(v_ref_7633_, v_addEntry_7634_, v_droppedKeys_7635_, v_constantsPerTask_7636_, v_droppedEntriesRef_7637_, v_ty_7638_, v_a_7639_, v_a_7640_, v_a_7641_, v_a_7642_);
return v___x_7644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___boxed(lean_object* v_00_u03b1_7645_, lean_object* v_ref_7646_, lean_object* v_addEntry_7647_, lean_object* v_droppedKeys_7648_, lean_object* v_constantsPerTask_7649_, lean_object* v_droppedEntriesRef_7650_, lean_object* v_ty_7651_, lean_object* v_a_7652_, lean_object* v_a_7653_, lean_object* v_a_7654_, lean_object* v_a_7655_, lean_object* v_a_7656_){
_start:
{
lean_object* v_res_7657_; 
v_res_7657_ = l_Lean_Meta_LazyDiscrTree_findMatches(v_00_u03b1_7645_, v_ref_7646_, v_addEntry_7647_, v_droppedKeys_7648_, v_constantsPerTask_7649_, v_droppedEntriesRef_7650_, v_ty_7651_, v_a_7652_, v_a_7653_, v_a_7654_, v_a_7655_);
lean_dec(v_a_7655_);
lean_dec_ref(v_a_7654_);
lean_dec(v_a_7653_);
lean_dec_ref(v_a_7652_);
lean_dec(v_ref_7646_);
return v_res_7657_;
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
