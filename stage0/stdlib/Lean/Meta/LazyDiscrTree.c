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
v___x_992_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6___redArg(v___x_991_, v_e_988_, v_a_989_);
v___x_993_ = lean_st_ref_put(v_a_987_, v___x_992_);
v___x_994_ = lean_box(0);
return v___x_994_;
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
lean_object* v_v_1027_; lean_object* v___x_1028_; 
v_v_1027_ = lean_array_uget_borrowed(v_bs_1020_, v_i_1019_);
lean_inc(v_v_1027_);
lean_inc_ref(v_post_1017_);
lean_inc_ref(v_pre_1016_);
v___x_1028_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1016_, v_post_1017_, v_v_1027_, v___y_1021_, v___y_1022_, v___y_1023_);
if (lean_obj_tag(v___x_1028_) == 0)
{
lean_object* v_a_1029_; lean_object* v___x_1030_; lean_object* v_bs_x27_1031_; size_t v___x_1032_; size_t v___x_1033_; lean_object* v___x_1034_; 
v_a_1029_ = lean_ctor_get(v___x_1028_, 0);
lean_inc(v_a_1029_);
lean_dec_ref_known(v___x_1028_, 1);
v___x_1030_ = lean_unsigned_to_nat(0u);
v_bs_x27_1031_ = lean_array_uset(v_bs_1020_, v_i_1019_, v___x_1030_);
v___x_1032_ = ((size_t)1ULL);
v___x_1033_ = lean_usize_add(v_i_1019_, v___x_1032_);
v___x_1034_ = lean_array_uset(v_bs_x27_1031_, v_i_1019_, v_a_1029_);
v_i_1019_ = v___x_1033_;
v_bs_1020_ = v___x_1034_;
goto _start;
}
else
{
lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1043_; 
lean_dec_ref(v_bs_1020_);
lean_dec_ref(v_post_1017_);
lean_dec_ref(v_pre_1016_);
v_a_1036_ = lean_ctor_get(v___x_1028_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1038_ = v___x_1028_;
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_dec(v___x_1028_);
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
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1(void){
_start:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; 
v___x_1857_ = lean_box(0);
v___x_1858_ = lean_unsigned_to_nat(16u);
v___x_1859_ = lean_mk_array(v___x_1858_, v___x_1857_);
return v___x_1859_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2(void){
_start:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___x_1860_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1);
v___x_1861_ = lean_unsigned_to_nat(0u);
v___x_1862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1861_);
lean_ctor_set(v___x_1862_, 1, v___x_1860_);
return v___x_1862_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__4(void){
_start:
{
lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1865_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__3));
v___x_1866_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_1867_ = lean_unsigned_to_nat(0u);
v___x_1868_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0));
v___x_1869_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1868_);
lean_ctor_set(v___x_1869_, 1, v___x_1867_);
lean_ctor_set(v___x_1869_, 2, v___x_1866_);
lean_ctor_set(v___x_1869_, 3, v___x_1865_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default(lean_object* v_00_u03b1_1870_){
_start:
{
lean_object* v___x_1871_; 
v___x_1871_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__4, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__4);
return v___x_1871_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0(void){
_start:
{
lean_object* v___x_1872_; 
v___x_1872_ = l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default(lean_box(0));
return v___x_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie(lean_object* v_a_1873_){
_start:
{
lean_object* v___x_1874_; 
v___x_1874_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0);
return v___x_1874_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__1(void){
_start:
{
lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; 
v___x_1877_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_1878_ = lean_unsigned_to_nat(0u);
v___x_1879_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_1880_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1880_, 0, v___x_1879_);
lean_ctor_set(v___x_1880_, 1, v___x_1878_);
lean_ctor_set(v___x_1880_, 2, v___x_1877_);
lean_ctor_set(v___x_1880_, 3, v___x_1879_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie(lean_object* v_00_u03b1_1881_){
_start:
{
lean_object* v___x_1882_; 
v___x_1882_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__1, &l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__1);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Trie_pushPending___redArg(lean_object* v_x_1883_, lean_object* v_x_1884_){
_start:
{
lean_object* v_values_1885_; lean_object* v_star_1886_; lean_object* v_children_1887_; lean_object* v_pending_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1896_; 
v_values_1885_ = lean_ctor_get(v_x_1883_, 0);
v_star_1886_ = lean_ctor_get(v_x_1883_, 1);
v_children_1887_ = lean_ctor_get(v_x_1883_, 2);
v_pending_1888_ = lean_ctor_get(v_x_1883_, 3);
v_isSharedCheck_1896_ = !lean_is_exclusive(v_x_1883_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1890_ = v_x_1883_;
v_isShared_1891_ = v_isSharedCheck_1896_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_pending_1888_);
lean_inc(v_children_1887_);
lean_inc(v_star_1886_);
lean_inc(v_values_1885_);
lean_dec(v_x_1883_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1896_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1892_; lean_object* v___x_1894_; 
v___x_1892_ = lean_array_push(v_pending_1888_, v_x_1884_);
if (v_isShared_1891_ == 0)
{
lean_ctor_set(v___x_1890_, 3, v___x_1892_);
v___x_1894_ = v___x_1890_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_values_1885_);
lean_ctor_set(v_reuseFailAlloc_1895_, 1, v_star_1886_);
lean_ctor_set(v_reuseFailAlloc_1895_, 2, v_children_1887_);
lean_ctor_set(v_reuseFailAlloc_1895_, 3, v___x_1892_);
v___x_1894_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
return v___x_1894_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Trie_pushPending(lean_object* v_00_u03b1_1897_, lean_object* v_x_1898_, lean_object* v_x_1899_){
_start:
{
lean_object* v___x_1900_; 
v___x_1900_ = l_Lean_Meta_LazyDiscrTree_Trie_pushPending___redArg(v_x_1898_, v_x_1899_);
return v___x_1900_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1901_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0);
v___x_1902_ = lean_unsigned_to_nat(1u);
v___x_1903_ = lean_mk_empty_array_with_capacity(v___x_1902_);
v___x_1904_ = lean_array_push(v___x_1903_, v___x_1901_);
return v___x_1904_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__1(void){
_start:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1905_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_1906_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0);
v___x_1907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1906_);
lean_ctor_set(v___x_1907_, 1, v___x_1905_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabited(lean_object* v_00_u03b1_1908_){
_start:
{
lean_object* v___x_1909_; 
v___x_1909_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabited___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabited___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__1);
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(lean_object* v_msgData_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_){
_start:
{
lean_object* v___x_1916_; lean_object* v_env_1917_; lean_object* v___x_1918_; lean_object* v_toCold_1919_; lean_object* v_mctx_1920_; lean_object* v_lctx_1921_; lean_object* v_options_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1916_ = lean_st_ref_get(v___y_1914_);
v_env_1917_ = lean_ctor_get(v___x_1916_, 0);
lean_inc_ref(v_env_1917_);
lean_dec(v___x_1916_);
v___x_1918_ = lean_st_ref_get(v___y_1912_);
v_toCold_1919_ = lean_ctor_get(v___y_1913_, 0);
v_mctx_1920_ = lean_ctor_get(v___x_1918_, 0);
lean_inc_ref(v_mctx_1920_);
lean_dec(v___x_1918_);
v_lctx_1921_ = lean_ctor_get(v___y_1911_, 2);
v_options_1922_ = lean_ctor_get(v_toCold_1919_, 2);
lean_inc_ref(v_options_1922_);
lean_inc_ref(v_lctx_1921_);
v___x_1923_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1923_, 0, v_env_1917_);
lean_ctor_set(v___x_1923_, 1, v_mctx_1920_);
lean_ctor_set(v___x_1923_, 2, v_lctx_1921_);
lean_ctor_set(v___x_1923_, 3, v_options_1922_);
v___x_1924_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1923_);
lean_ctor_set(v___x_1924_, 1, v_msgData_1910_);
v___x_1925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1924_);
return v___x_1925_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0___boxed(lean_object* v_msgData_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_){
_start:
{
lean_object* v_res_1932_; 
v_res_1932_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(v_msgData_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_);
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1929_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
return v_res_1932_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(lean_object* v_msg_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_){
_start:
{
lean_object* v_ref_1939_; lean_object* v___x_1940_; lean_object* v_a_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1949_; 
v_ref_1939_ = lean_ctor_get(v___y_1936_, 2);
v___x_1940_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(v_msg_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_);
v_a_1941_ = lean_ctor_get(v___x_1940_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1940_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1943_ = v___x_1940_;
v_isShared_1944_ = v_isSharedCheck_1949_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_a_1941_);
lean_dec(v___x_1940_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1949_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1945_; lean_object* v___x_1947_; 
lean_inc(v_ref_1939_);
v___x_1945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1945_, 0, v_ref_1939_);
lean_ctor_set(v___x_1945_, 1, v_a_1941_);
if (v_isShared_1944_ == 0)
{
lean_ctor_set_tag(v___x_1943_, 1);
lean_ctor_set(v___x_1943_, 0, v___x_1945_);
v___x_1947_ = v___x_1943_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(1, 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg___boxed(lean_object* v_msg_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(v_msg_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
return v_res_1956_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1(void){
_start:
{
lean_object* v___x_1958_; lean_object* v___x_1959_; 
v___x_1958_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_pushArgs___closed__0));
v___x_1959_ = l_Lean_stringToMessageData(v___x_1958_);
return v___x_1959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushArgs(uint8_t v_root_1960_, lean_object* v_todo_1961_, lean_object* v_e_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_){
_start:
{
uint8_t v___x_1968_; 
v___x_1968_ = l_Lean_Meta_DiscrTree_hasNoindexAnnotation(v_e_1962_);
if (v___x_1968_ == 0)
{
lean_object* v___x_1969_; 
v___x_1969_ = l_Lean_Meta_DiscrTree_reduceDT(v_e_1962_, v_root_1960_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_);
if (lean_obj_tag(v___x_1969_) == 0)
{
lean_object* v_a_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_2109_; 
v_a_1970_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_1972_ = v___x_1969_;
v_isShared_1973_ = v_isSharedCheck_2109_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_a_1970_);
lean_dec(v___x_1969_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_2109_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v_v_1975_; lean_object* v___x_1981_; lean_object* v_k_1983_; lean_object* v_nargs_1984_; lean_object* v_todo_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; 
v___x_1981_ = l_Lean_Expr_getAppFn(v_a_1970_);
switch(lean_obj_tag(v___x_1981_))
{
case 9:
{
lean_object* v_a_2028_; 
lean_dec(v_a_1970_);
v_a_2028_ = lean_ctor_get(v___x_1981_, 0);
lean_inc_ref(v_a_2028_);
lean_dec_ref_known(v___x_1981_, 1);
v_v_1975_ = v_a_2028_;
goto v___jp_1974_;
}
case 4:
{
lean_object* v_declName_2029_; lean_object* v___y_2031_; lean_object* v___y_2032_; lean_object* v___y_2033_; lean_object* v___y_2034_; 
v_declName_2029_ = lean_ctor_get(v___x_1981_, 0);
lean_inc(v_declName_2029_);
if (v_root_1960_ == 0)
{
lean_object* v___x_2037_; 
lean_inc(v_a_1970_);
v___x_2037_ = l_Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f(v_a_1970_);
if (lean_obj_tag(v___x_2037_) == 1)
{
lean_object* v_val_2038_; 
lean_dec_ref_known(v___x_1981_, 2);
lean_dec(v_declName_2029_);
lean_dec(v_a_1970_);
v_val_2038_ = lean_ctor_get(v___x_2037_, 0);
lean_inc(v_val_2038_);
lean_dec_ref_known(v___x_2037_, 1);
v_v_1975_ = v_val_2038_;
goto v___jp_1974_;
}
else
{
lean_object* v___x_2039_; 
lean_dec(v___x_2037_);
lean_del_object(v___x_1972_);
v___x_2039_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset(v_declName_2029_, v_a_1970_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v_a_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2050_; 
v_a_2040_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2042_ = v___x_2039_;
v_isShared_2043_ = v_isSharedCheck_2050_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_a_2040_);
lean_dec(v___x_2039_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2050_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
uint8_t v___x_2044_; 
v___x_2044_ = lean_unbox(v_a_2040_);
lean_dec(v_a_2040_);
if (v___x_2044_ == 0)
{
lean_del_object(v___x_2042_);
v___y_2031_ = v_a_1963_;
v___y_2032_ = v_a_1964_;
v___y_2033_ = v_a_1965_;
v___y_2034_ = v_a_1966_;
goto v___jp_2030_;
}
else
{
lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2048_; 
lean_dec_ref_known(v___x_1981_, 2);
lean_dec(v_declName_2029_);
lean_dec(v_a_1970_);
v___x_2045_ = lean_box(3);
v___x_2046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2045_);
lean_ctor_set(v___x_2046_, 1, v_todo_1961_);
if (v_isShared_2043_ == 0)
{
lean_ctor_set(v___x_2042_, 0, v___x_2046_);
v___x_2048_ = v___x_2042_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2046_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
}
else
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2058_; 
lean_dec(v_declName_2029_);
lean_dec_ref_known(v___x_1981_, 2);
lean_dec(v_a_1970_);
lean_dec_ref(v_todo_1961_);
v_a_2051_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2053_ = v___x_2039_;
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_2039_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2056_; 
if (v_isShared_2054_ == 0)
{
v___x_2056_ = v___x_2053_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
}
else
{
lean_del_object(v___x_1972_);
v___y_2031_ = v_a_1963_;
v___y_2032_ = v_a_1964_;
v___y_2033_ = v_a_1965_;
v___y_2034_ = v_a_1966_;
goto v___jp_2030_;
}
v___jp_2030_:
{
lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___x_2035_ = l_Lean_Expr_getAppNumArgs(v_a_1970_);
lean_inc(v___x_2035_);
v___x_2036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2036_, 0, v_declName_2029_);
lean_ctor_set(v___x_2036_, 1, v___x_2035_);
v_k_1983_ = v___x_2036_;
v_nargs_1984_ = v___x_2035_;
v_todo_1985_ = v_todo_1961_;
v___y_1986_ = v___y_2031_;
v___y_1987_ = v___y_2032_;
v___y_1988_ = v___y_2033_;
v___y_1989_ = v___y_2034_;
goto v___jp_1982_;
}
}
case 11:
{
lean_object* v_typeName_2059_; lean_object* v_idx_2060_; lean_object* v_struct_2061_; lean_object* v___x_2062_; lean_object* v___y_2064_; lean_object* v_env_2068_; uint8_t v___x_2069_; 
lean_del_object(v___x_1972_);
v_typeName_2059_ = lean_ctor_get(v___x_1981_, 0);
lean_inc(v_typeName_2059_);
v_idx_2060_ = lean_ctor_get(v___x_1981_, 1);
lean_inc(v_idx_2060_);
v_struct_2061_ = lean_ctor_get(v___x_1981_, 2);
lean_inc_ref(v_struct_2061_);
v___x_2062_ = lean_st_ref_get(v_a_1966_);
v_env_2068_ = lean_ctor_get(v___x_2062_, 0);
lean_inc_ref(v_env_2068_);
lean_dec(v___x_2062_);
v___x_2069_ = l_Lean_isClass(v_env_2068_, v_typeName_2059_);
if (v___x_2069_ == 0)
{
v___y_2064_ = v_struct_2061_;
goto v___jp_2063_;
}
else
{
lean_object* v___x_2070_; 
v___x_2070_ = l_Lean_Meta_DiscrTree_mkNoindexAnnotation(v_struct_2061_);
v___y_2064_ = v___x_2070_;
goto v___jp_2063_;
}
v___jp_2063_:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; 
v___x_2065_ = l_Lean_Expr_getAppNumArgs(v_a_1970_);
lean_inc(v___x_2065_);
v___x_2066_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_2066_, 0, v_typeName_2059_);
lean_ctor_set(v___x_2066_, 1, v_idx_2060_);
lean_ctor_set(v___x_2066_, 2, v___x_2065_);
v___x_2067_ = lean_array_push(v_todo_1961_, v___y_2064_);
v_k_1983_ = v___x_2066_;
v_nargs_1984_ = v___x_2065_;
v_todo_1985_ = v___x_2067_;
v___y_1986_ = v_a_1963_;
v___y_1987_ = v_a_1964_;
v___y_1988_ = v_a_1965_;
v___y_1989_ = v_a_1966_;
goto v___jp_1982_;
}
}
case 1:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; 
lean_dec_ref_known(v___x_1981_, 1);
lean_del_object(v___x_1972_);
lean_dec(v_a_1970_);
v___x_2071_ = lean_box(3);
v___x_2072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2071_);
lean_ctor_set(v___x_2072_, 1, v_todo_1961_);
v___x_2073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2073_, 0, v___x_2072_);
return v___x_2073_;
}
case 2:
{
lean_object* v_mvarId_2074_; lean_object* v___x_2075_; uint8_t v___x_2076_; 
lean_del_object(v___x_1972_);
lean_dec(v_a_1970_);
v_mvarId_2074_ = lean_ctor_get(v___x_1981_, 0);
lean_inc(v_mvarId_2074_);
lean_dec_ref_known(v___x_1981_, 1);
v___x_2075_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_tmpMVarId));
v___x_2076_ = l_Lean_instBEqMVarId_beq(v_mvarId_2074_, v___x_2075_);
lean_dec(v_mvarId_2074_);
if (v___x_2076_ == 0)
{
lean_object* v___x_2077_; lean_object* v___x_2078_; 
lean_dec_ref(v_todo_1961_);
v___x_2077_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1, &l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1);
v___x_2078_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(v___x_2077_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_);
return v___x_2078_;
}
else
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2079_ = lean_box(3);
v___x_2080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2079_);
lean_ctor_set(v___x_2080_, 1, v_todo_1961_);
v___x_2081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2080_);
return v___x_2081_;
}
}
case 7:
{
lean_object* v_binderType_2082_; lean_object* v_body_2083_; lean_object* v_b_2085_; uint8_t v___x_2095_; 
lean_del_object(v___x_1972_);
lean_dec(v_a_1970_);
v_binderType_2082_ = lean_ctor_get(v___x_1981_, 1);
lean_inc_ref(v_binderType_2082_);
v_body_2083_ = lean_ctor_get(v___x_1981_, 2);
lean_inc_ref(v_body_2083_);
lean_dec_ref_known(v___x_1981_, 3);
v___x_2095_ = l_Lean_Expr_hasLooseBVars(v_body_2083_);
if (v___x_2095_ == 0)
{
v_b_2085_ = v_body_2083_;
goto v___jp_2084_;
}
else
{
lean_object* v___x_2096_; 
v___x_2096_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(v_body_2083_, v_a_1965_, v_a_1966_);
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_object* v_a_2097_; 
v_a_2097_ = lean_ctor_get(v___x_2096_, 0);
lean_inc(v_a_2097_);
lean_dec_ref_known(v___x_2096_, 1);
v_b_2085_ = v_a_2097_;
goto v___jp_2084_;
}
else
{
lean_object* v_a_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2105_; 
lean_dec_ref(v_binderType_2082_);
lean_dec_ref(v_todo_1961_);
v_a_2098_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2100_ = v___x_2096_;
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_a_2098_);
lean_dec(v___x_2096_);
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
v___jp_2084_:
{
uint8_t v___x_2086_; 
v___x_2086_ = l_Lean_Expr_hasLooseBVars(v_b_2085_);
if (v___x_2086_ == 0)
{
lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; 
v___x_2087_ = lean_box(5);
v___x_2088_ = lean_array_push(v_todo_1961_, v_binderType_2082_);
v___x_2089_ = lean_array_push(v___x_2088_, v_b_2085_);
v___x_2090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2087_);
lean_ctor_set(v___x_2090_, 1, v___x_2089_);
v___x_2091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2090_);
return v___x_2091_;
}
else
{
lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
lean_dec_ref(v_b_2085_);
lean_dec_ref(v_binderType_2082_);
v___x_2092_ = lean_box(4);
v___x_2093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2092_);
lean_ctor_set(v___x_2093_, 1, v_todo_1961_);
v___x_2094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2093_);
return v___x_2094_;
}
}
}
default: 
{
lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; 
lean_dec_ref(v___x_1981_);
lean_del_object(v___x_1972_);
lean_dec(v_a_1970_);
v___x_2106_ = lean_box(4);
v___x_2107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2106_);
lean_ctor_set(v___x_2107_, 1, v_todo_1961_);
v___x_2108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2107_);
return v___x_2108_;
}
}
v___jp_1974_:
{
lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1979_; 
v___x_1976_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1976_, 0, v_v_1975_);
v___x_1977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1977_, 0, v___x_1976_);
lean_ctor_set(v___x_1977_, 1, v_todo_1961_);
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 0, v___x_1977_);
v___x_1979_ = v___x_1972_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v___x_1977_);
v___x_1979_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
return v___x_1979_;
}
}
v___jp_1982_:
{
lean_object* v___x_1990_; 
lean_inc(v_nargs_1984_);
v___x_1990_ = l_Lean_Meta_getFunInfoNArgs(v___x_1981_, v_nargs_1984_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_);
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_object* v_a_1991_; lean_object* v_paramInfo_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_2018_; 
v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
lean_inc(v_a_1991_);
lean_dec_ref_known(v___x_1990_, 1);
v_paramInfo_1992_ = lean_ctor_get(v_a_1991_, 0);
v_isSharedCheck_2018_ = !lean_is_exclusive(v_a_1991_);
if (v_isSharedCheck_2018_ == 0)
{
lean_object* v_unused_2019_; 
v_unused_2019_ = lean_ctor_get(v_a_1991_, 1);
lean_dec(v_unused_2019_);
v___x_1994_ = v_a_1991_;
v_isShared_1995_ = v_isSharedCheck_2018_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_paramInfo_1992_);
lean_dec(v_a_1991_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_2018_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1996_ = lean_unsigned_to_nat(1u);
v___x_1997_ = lean_nat_sub(v_nargs_1984_, v___x_1996_);
lean_dec(v_nargs_1984_);
v___x_1998_ = l_Lean_Meta_LazyDiscrTree_MatchClone_pushArgsAux(v_paramInfo_1992_, v___x_1997_, v_a_1970_, v_todo_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_);
lean_dec_ref(v_paramInfo_1992_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v_a_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2009_; 
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_2001_ = v___x_1998_;
v_isShared_2002_ = v_isSharedCheck_2009_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_a_1999_);
lean_dec(v___x_1998_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2009_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2004_; 
if (v_isShared_1995_ == 0)
{
lean_ctor_set(v___x_1994_, 1, v_a_1999_);
lean_ctor_set(v___x_1994_, 0, v_k_1983_);
v___x_2004_ = v___x_1994_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_k_1983_);
lean_ctor_set(v_reuseFailAlloc_2008_, 1, v_a_1999_);
v___x_2004_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
lean_object* v___x_2006_; 
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 0, v___x_2004_);
v___x_2006_ = v___x_2001_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v___x_2004_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
}
else
{
lean_object* v_a_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2017_; 
lean_del_object(v___x_1994_);
lean_dec(v_k_1983_);
v_a_2010_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2017_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_2012_ = v___x_1998_;
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_a_2010_);
lean_dec(v___x_1998_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2015_; 
if (v_isShared_2013_ == 0)
{
v___x_2015_ = v___x_2012_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_a_2010_);
v___x_2015_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
return v___x_2015_;
}
}
}
}
}
else
{
lean_object* v_a_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2027_; 
lean_dec_ref(v_todo_1985_);
lean_dec(v_nargs_1984_);
lean_dec(v_k_1983_);
lean_dec(v_a_1970_);
v_a_2020_ = lean_ctor_get(v___x_1990_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2022_ = v___x_1990_;
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_a_2020_);
lean_dec(v___x_1990_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2025_; 
if (v_isShared_2023_ == 0)
{
v___x_2025_ = v___x_2022_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_a_2020_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
return v___x_2025_;
}
}
}
}
}
}
else
{
lean_object* v_a_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2117_; 
lean_dec_ref(v_todo_1961_);
v_a_2110_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_2117_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2112_ = v___x_1969_;
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_a_2110_);
lean_dec(v___x_1969_);
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
else
{
lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
lean_dec_ref(v_e_1962_);
v___x_2118_ = lean_box(3);
v___x_2119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2118_);
lean_ctor_set(v___x_2119_, 1, v_todo_1961_);
v___x_2120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2119_);
return v___x_2120_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushArgs___boxed(lean_object* v_root_2121_, lean_object* v_todo_2122_, lean_object* v_e_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_){
_start:
{
uint8_t v_root_boxed_2129_; lean_object* v_res_2130_; 
v_root_boxed_2129_ = lean_unbox(v_root_2121_);
v_res_2130_ = l_Lean_Meta_LazyDiscrTree_pushArgs(v_root_boxed_2129_, v_todo_2122_, v_e_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_);
lean_dec(v_a_2127_);
lean_dec_ref(v_a_2126_);
lean_dec(v_a_2125_);
lean_dec_ref(v_a_2124_);
return v_res_2130_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0(lean_object* v_00_u03b1_2131_, lean_object* v_msg_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
lean_object* v___x_2138_; 
v___x_2138_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(v_msg_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
return v___x_2138_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___boxed(lean_object* v_00_u03b1_2139_, lean_object* v_msg_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_){
_start:
{
lean_object* v_res_2146_; 
v_res_2146_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0(v_00_u03b1_2139_, v_msg_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_);
lean_dec(v___y_2144_);
lean_dec_ref(v___y_2143_);
lean_dec(v___y_2142_);
lean_dec_ref(v___y_2141_);
return v_res_2146_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_initCapacity(void){
_start:
{
lean_object* v___x_2147_; 
v___x_2147_ = lean_unsigned_to_nat(8u);
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_rootKey(lean_object* v_e_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_){
_start:
{
uint8_t v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2154_ = 1;
v___x_2155_ = lean_unsigned_to_nat(8u);
v___x_2156_ = lean_mk_empty_array_with_capacity(v___x_2155_);
v___x_2157_ = l_Lean_Meta_LazyDiscrTree_pushArgs(v___x_2154_, v___x_2156_, v_e_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_);
return v___x_2157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_rootKey___boxed(lean_object* v_e_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_){
_start:
{
lean_object* v_res_2164_; 
v_res_2164_ = l_Lean_Meta_LazyDiscrTree_rootKey(v_e_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_);
lean_dec(v_a_2162_);
lean_dec_ref(v_a_2161_);
lean_dec(v_a_2160_);
lean_dec_ref(v_a_2159_);
return v_res_2164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_buildPath(lean_object* v_op_2165_, uint8_t v_root_2166_, lean_object* v_todo_2167_, lean_object* v_keys_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_){
_start:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; uint8_t v___x_2176_; 
v___x_2174_ = lean_array_get_size(v_todo_2167_);
v___x_2175_ = lean_unsigned_to_nat(0u);
v___x_2176_ = lean_nat_dec_eq(v___x_2174_, v___x_2175_);
if (v___x_2176_ == 0)
{
lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v_e_2180_; lean_object* v_todo_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
v___x_2177_ = l_Lean_instInhabitedExpr;
v___x_2178_ = lean_unsigned_to_nat(1u);
v___x_2179_ = lean_nat_sub(v___x_2174_, v___x_2178_);
v_e_2180_ = lean_array_get(v___x_2177_, v_todo_2167_, v___x_2179_);
lean_dec(v___x_2179_);
v_todo_2181_ = lean_array_pop(v_todo_2167_);
v___x_2182_ = lean_box(v_root_2166_);
lean_inc_ref(v_op_2165_);
lean_inc(v_a_2172_);
lean_inc_ref(v_a_2171_);
lean_inc(v_a_2170_);
lean_inc_ref(v_a_2169_);
v___x_2183_ = lean_apply_8(v_op_2165_, v___x_2182_, v_todo_2181_, v_e_2180_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_, lean_box(0));
if (lean_obj_tag(v___x_2183_) == 0)
{
lean_object* v_a_2184_; lean_object* v_fst_2185_; lean_object* v_snd_2186_; lean_object* v___x_2187_; 
v_a_2184_ = lean_ctor_get(v___x_2183_, 0);
lean_inc(v_a_2184_);
lean_dec_ref_known(v___x_2183_, 1);
v_fst_2185_ = lean_ctor_get(v_a_2184_, 0);
lean_inc(v_fst_2185_);
v_snd_2186_ = lean_ctor_get(v_a_2184_, 1);
lean_inc(v_snd_2186_);
lean_dec(v_a_2184_);
v___x_2187_ = lean_array_push(v_keys_2168_, v_fst_2185_);
v_root_2166_ = v___x_2176_;
v_todo_2167_ = v_snd_2186_;
v_keys_2168_ = v___x_2187_;
goto _start;
}
else
{
lean_object* v_a_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2196_; 
lean_dec_ref(v_keys_2168_);
lean_dec_ref(v_op_2165_);
v_a_2189_ = lean_ctor_get(v___x_2183_, 0);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2191_ = v___x_2183_;
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_a_2189_);
lean_dec(v___x_2183_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2194_; 
if (v_isShared_2192_ == 0)
{
v___x_2194_ = v___x_2191_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_a_2189_);
v___x_2194_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
return v___x_2194_;
}
}
}
}
else
{
lean_object* v___x_2197_; 
lean_dec_ref(v_todo_2167_);
lean_dec_ref(v_op_2165_);
v___x_2197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2197_, 0, v_keys_2168_);
return v___x_2197_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_buildPath___boxed(lean_object* v_op_2198_, lean_object* v_root_2199_, lean_object* v_todo_2200_, lean_object* v_keys_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_){
_start:
{
uint8_t v_root_boxed_2207_; lean_object* v_res_2208_; 
v_root_boxed_2207_ = lean_unbox(v_root_2199_);
v_res_2208_ = l_Lean_Meta_LazyDiscrTree_buildPath(v_op_2198_, v_root_boxed_2207_, v_todo_2200_, v_keys_2201_, v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_);
lean_dec(v_a_2205_);
lean_dec_ref(v_a_2204_);
lean_dec(v_a_2203_);
lean_dec_ref(v_a_2202_);
return v_res_2208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_patternPath(lean_object* v_e_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_){
_start:
{
lean_object* v_op_2216_; lean_object* v___x_2217_; lean_object* v_todo_2218_; uint8_t v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
v_op_2216_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_patternPath___closed__0));
v___x_2217_ = lean_unsigned_to_nat(8u);
v_todo_2218_ = lean_mk_empty_array_with_capacity(v___x_2217_);
v___x_2219_ = 1;
lean_inc_ref(v_todo_2218_);
v___x_2220_ = lean_array_push(v_todo_2218_, v_e_2210_);
v___x_2221_ = l_Lean_Meta_LazyDiscrTree_buildPath(v_op_2216_, v___x_2219_, v___x_2220_, v_todo_2218_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_patternPath___boxed(lean_object* v_e_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_){
_start:
{
lean_object* v_res_2228_; 
v_res_2228_ = l_Lean_Meta_LazyDiscrTree_patternPath(v_e_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_);
lean_dec(v_a_2226_);
lean_dec_ref(v_a_2225_);
lean_dec(v_a_2224_);
lean_dec_ref(v_a_2223_);
return v_res_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath___lam__0(uint8_t v_root_2229_, lean_object* v_todo_2230_, lean_object* v_e_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_){
_start:
{
uint8_t v___x_2237_; lean_object* v___x_2238_; 
v___x_2237_ = 1;
v___x_2238_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_2231_, v___x_2237_, v_root_2229_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2256_; 
v_a_2239_ = lean_ctor_get(v___x_2238_, 0);
v_isSharedCheck_2256_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2241_ = v___x_2238_;
v_isShared_2242_ = v_isSharedCheck_2256_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_2238_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2256_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v_fst_2243_; lean_object* v_snd_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2255_; 
v_fst_2243_ = lean_ctor_get(v_a_2239_, 0);
v_snd_2244_ = lean_ctor_get(v_a_2239_, 1);
v_isSharedCheck_2255_ = !lean_is_exclusive(v_a_2239_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2246_ = v_a_2239_;
v_isShared_2247_ = v_isSharedCheck_2255_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_snd_2244_);
lean_inc(v_fst_2243_);
lean_dec(v_a_2239_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2255_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
lean_object* v___x_2248_; lean_object* v___x_2250_; 
v___x_2248_ = l_Array_append___redArg(v_todo_2230_, v_snd_2244_);
lean_dec(v_snd_2244_);
if (v_isShared_2247_ == 0)
{
lean_ctor_set(v___x_2246_, 1, v___x_2248_);
v___x_2250_ = v___x_2246_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_fst_2243_);
lean_ctor_set(v_reuseFailAlloc_2254_, 1, v___x_2248_);
v___x_2250_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
lean_object* v___x_2252_; 
if (v_isShared_2242_ == 0)
{
lean_ctor_set(v___x_2241_, 0, v___x_2250_);
v___x_2252_ = v___x_2241_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v___x_2250_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
}
}
}
else
{
lean_dec_ref(v_todo_2230_);
return v___x_2238_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath___lam__0___boxed(lean_object* v_root_2257_, lean_object* v_todo_2258_, lean_object* v_e_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_){
_start:
{
uint8_t v_root_boxed_2265_; lean_object* v_res_2266_; 
v_root_boxed_2265_ = lean_unbox(v_root_2257_);
v_res_2266_ = l_Lean_Meta_LazyDiscrTree_targetPath___lam__0(v_root_boxed_2265_, v_todo_2258_, v_e_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
return v_res_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath(lean_object* v_e_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_){
_start:
{
lean_object* v_op_2274_; lean_object* v___x_2275_; lean_object* v_todo_2276_; uint8_t v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; 
v_op_2274_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_targetPath___closed__0));
v___x_2275_ = lean_unsigned_to_nat(8u);
v_todo_2276_ = lean_mk_empty_array_with_capacity(v___x_2275_);
v___x_2277_ = 1;
lean_inc_ref(v_todo_2276_);
v___x_2278_ = lean_array_push(v_todo_2276_, v_e_2268_);
v___x_2279_ = l_Lean_Meta_LazyDiscrTree_buildPath(v_op_2274_, v___x_2277_, v___x_2278_, v_todo_2276_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_);
return v___x_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath___boxed(lean_object* v_e_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_){
_start:
{
lean_object* v_res_2286_; 
v_res_2286_ = l_Lean_Meta_LazyDiscrTree_targetPath(v_e_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_);
lean_dec(v_a_2284_);
lean_dec_ref(v_a_2283_);
lean_dec(v_a_2282_);
lean_dec_ref(v_a_2281_);
return v_res_2286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___redArg___lam__0(lean_object* v_tries_2287_, lean_object* v_m_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_){
_start:
{
lean_object* v___x_2294_; lean_object* v___x_2295_; 
v___x_2294_ = lean_st_mk_ref(v_tries_2287_);
lean_inc(v___x_2294_);
v___x_2295_ = lean_apply_6(v_m_2288_, v___x_2294_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_, lean_box(0));
if (lean_obj_tag(v___x_2295_) == 0)
{
lean_object* v_a_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2305_; 
v_a_2296_ = lean_ctor_get(v___x_2295_, 0);
v_isSharedCheck_2305_ = !lean_is_exclusive(v___x_2295_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2298_ = v___x_2295_;
v_isShared_2299_ = v_isSharedCheck_2305_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_a_2296_);
lean_dec(v___x_2295_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2305_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2303_; 
v___x_2300_ = lean_st_ref_get(v___x_2294_);
lean_dec(v___x_2294_);
v___x_2301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2301_, 0, v_a_2296_);
lean_ctor_set(v___x_2301_, 1, v___x_2300_);
if (v_isShared_2299_ == 0)
{
lean_ctor_set(v___x_2298_, 0, v___x_2301_);
v___x_2303_ = v___x_2298_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v___x_2301_);
v___x_2303_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
return v___x_2303_;
}
}
}
else
{
lean_object* v_a_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2313_; 
lean_dec(v___x_2294_);
v_a_2306_ = lean_ctor_get(v___x_2295_, 0);
v_isSharedCheck_2313_ = !lean_is_exclusive(v___x_2295_);
if (v_isSharedCheck_2313_ == 0)
{
v___x_2308_ = v___x_2295_;
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_a_2306_);
lean_dec(v___x_2295_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___redArg___lam__0___boxed(lean_object* v_tries_2314_, lean_object* v_m_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_){
_start:
{
lean_object* v_res_2321_; 
v_res_2321_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg___lam__0(v_tries_2314_, v_m_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
return v_res_2321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___redArg(lean_object* v_d_2322_, lean_object* v_m_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_){
_start:
{
lean_object* v_tries_2329_; lean_object* v_roots_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2383_; 
v_tries_2329_ = lean_ctor_get(v_d_2322_, 0);
v_roots_2330_ = lean_ctor_get(v_d_2322_, 1);
v_isSharedCheck_2383_ = !lean_is_exclusive(v_d_2322_);
if (v_isSharedCheck_2383_ == 0)
{
v___x_2332_ = v_d_2322_;
v_isShared_2333_ = v_isSharedCheck_2383_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_roots_2330_);
lean_inc(v_tries_2329_);
lean_dec(v_d_2322_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2383_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v___y_2335_; lean_object* v___x_2364_; uint8_t v_transparency_2365_; uint8_t v___x_2366_; uint8_t v___x_2367_; 
v___x_2364_ = l_Lean_Meta_Context_config(v_a_2324_);
v_transparency_2365_ = lean_ctor_get_uint8(v___x_2364_, 9);
lean_dec_ref(v___x_2364_);
v___x_2366_ = 2;
v___x_2367_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2365_, v___x_2366_);
if (v___x_2367_ == 0)
{
lean_object* v_keyedConfig_2368_; uint8_t v_trackZetaDelta_2369_; lean_object* v_zetaDeltaSet_2370_; lean_object* v_lctx_2371_; lean_object* v_localInstances_2372_; lean_object* v_defEqCtx_x3f_2373_; lean_object* v_synthPendingDepth_2374_; lean_object* v_customCanUnfoldPredicate_x3f_2375_; uint8_t v_univApprox_2376_; uint8_t v_inTypeClassResolution_2377_; uint8_t v_cacheInferType_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; 
v_keyedConfig_2368_ = lean_ctor_get(v_a_2324_, 0);
v_trackZetaDelta_2369_ = lean_ctor_get_uint8(v_a_2324_, sizeof(void*)*7);
v_zetaDeltaSet_2370_ = lean_ctor_get(v_a_2324_, 1);
v_lctx_2371_ = lean_ctor_get(v_a_2324_, 2);
v_localInstances_2372_ = lean_ctor_get(v_a_2324_, 3);
v_defEqCtx_x3f_2373_ = lean_ctor_get(v_a_2324_, 4);
v_synthPendingDepth_2374_ = lean_ctor_get(v_a_2324_, 5);
v_customCanUnfoldPredicate_x3f_2375_ = lean_ctor_get(v_a_2324_, 6);
v_univApprox_2376_ = lean_ctor_get_uint8(v_a_2324_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2377_ = lean_ctor_get_uint8(v_a_2324_, sizeof(void*)*7 + 2);
v_cacheInferType_2378_ = lean_ctor_get_uint8(v_a_2324_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2368_);
v___x_2379_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2366_, v_keyedConfig_2368_);
lean_inc(v_customCanUnfoldPredicate_x3f_2375_);
lean_inc(v_synthPendingDepth_2374_);
lean_inc(v_defEqCtx_x3f_2373_);
lean_inc_ref(v_localInstances_2372_);
lean_inc_ref(v_lctx_2371_);
lean_inc(v_zetaDeltaSet_2370_);
v___x_2380_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2380_, 0, v___x_2379_);
lean_ctor_set(v___x_2380_, 1, v_zetaDeltaSet_2370_);
lean_ctor_set(v___x_2380_, 2, v_lctx_2371_);
lean_ctor_set(v___x_2380_, 3, v_localInstances_2372_);
lean_ctor_set(v___x_2380_, 4, v_defEqCtx_x3f_2373_);
lean_ctor_set(v___x_2380_, 5, v_synthPendingDepth_2374_);
lean_ctor_set(v___x_2380_, 6, v_customCanUnfoldPredicate_x3f_2375_);
lean_ctor_set_uint8(v___x_2380_, sizeof(void*)*7, v_trackZetaDelta_2369_);
lean_ctor_set_uint8(v___x_2380_, sizeof(void*)*7 + 1, v_univApprox_2376_);
lean_ctor_set_uint8(v___x_2380_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2377_);
lean_ctor_set_uint8(v___x_2380_, sizeof(void*)*7 + 3, v_cacheInferType_2378_);
lean_inc(v_a_2327_);
lean_inc_ref(v_a_2326_);
lean_inc(v_a_2325_);
v___x_2381_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg___lam__0(v_tries_2329_, v_m_2323_, v___x_2380_, v_a_2325_, v_a_2326_, v_a_2327_);
v___y_2335_ = v___x_2381_;
goto v___jp_2334_;
}
else
{
lean_object* v___x_2382_; 
lean_inc(v_a_2327_);
lean_inc_ref(v_a_2326_);
lean_inc(v_a_2325_);
lean_inc_ref(v_a_2324_);
v___x_2382_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg___lam__0(v_tries_2329_, v_m_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_);
v___y_2335_ = v___x_2382_;
goto v___jp_2334_;
}
v___jp_2334_:
{
if (lean_obj_tag(v___y_2335_) == 0)
{
lean_object* v_a_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2355_; 
v_a_2336_ = lean_ctor_get(v___y_2335_, 0);
v_isSharedCheck_2355_ = !lean_is_exclusive(v___y_2335_);
if (v_isSharedCheck_2355_ == 0)
{
v___x_2338_ = v___y_2335_;
v_isShared_2339_ = v_isSharedCheck_2355_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_a_2336_);
lean_dec(v___y_2335_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2355_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v_fst_2340_; lean_object* v_snd_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2354_; 
v_fst_2340_ = lean_ctor_get(v_a_2336_, 0);
v_snd_2341_ = lean_ctor_get(v_a_2336_, 1);
v_isSharedCheck_2354_ = !lean_is_exclusive(v_a_2336_);
if (v_isSharedCheck_2354_ == 0)
{
v___x_2343_ = v_a_2336_;
v_isShared_2344_ = v_isSharedCheck_2354_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_snd_2341_);
lean_inc(v_fst_2340_);
lean_dec(v_a_2336_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2354_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v___x_2346_; 
if (v_isShared_2333_ == 0)
{
lean_ctor_set(v___x_2332_, 0, v_snd_2341_);
v___x_2346_ = v___x_2332_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v_snd_2341_);
lean_ctor_set(v_reuseFailAlloc_2353_, 1, v_roots_2330_);
v___x_2346_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
lean_object* v___x_2348_; 
if (v_isShared_2344_ == 0)
{
lean_ctor_set(v___x_2343_, 1, v___x_2346_);
v___x_2348_ = v___x_2343_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v_fst_2340_);
lean_ctor_set(v_reuseFailAlloc_2352_, 1, v___x_2346_);
v___x_2348_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
lean_object* v___x_2350_; 
if (v_isShared_2339_ == 0)
{
lean_ctor_set(v___x_2338_, 0, v___x_2348_);
v___x_2350_ = v___x_2338_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v___x_2348_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
}
}
}
}
else
{
lean_object* v_a_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2363_; 
lean_del_object(v___x_2332_);
lean_dec_ref(v_roots_2330_);
v_a_2356_ = lean_ctor_get(v___y_2335_, 0);
v_isSharedCheck_2363_ = !lean_is_exclusive(v___y_2335_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2358_ = v___y_2335_;
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_a_2356_);
lean_dec(v___y_2335_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v___x_2361_; 
if (v_isShared_2359_ == 0)
{
v___x_2361_ = v___x_2358_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_a_2356_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___redArg___boxed(lean_object* v_d_2384_, lean_object* v_m_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_){
_start:
{
lean_object* v_res_2391_; 
v_res_2391_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_d_2384_, v_m_2385_, v_a_2386_, v_a_2387_, v_a_2388_, v_a_2389_);
lean_dec(v_a_2389_);
lean_dec_ref(v_a_2388_);
lean_dec(v_a_2387_);
lean_dec_ref(v_a_2386_);
return v_res_2391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch(lean_object* v_00_u03b1_2392_, lean_object* v_00_u03b2_2393_, lean_object* v_d_2394_, lean_object* v_m_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_){
_start:
{
lean_object* v___x_2401_; 
v___x_2401_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_d_2394_, v_m_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_);
return v___x_2401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___boxed(lean_object* v_00_u03b1_2402_, lean_object* v_00_u03b2_2403_, lean_object* v_d_2404_, lean_object* v_m_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_){
_start:
{
lean_object* v_res_2411_; 
v_res_2411_ = l_Lean_Meta_LazyDiscrTree_runMatch(v_00_u03b1_2402_, v_00_u03b2_2403_, v_d_2404_, v_m_2405_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_);
lean_dec(v_a_2409_);
lean_dec_ref(v_a_2408_);
lean_dec(v_a_2407_);
lean_dec_ref(v_a_2406_);
return v_res_2411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie___redArg(lean_object* v_i_2412_, lean_object* v_v_2413_, lean_object* v_a_2414_){
_start:
{
lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2416_ = lean_st_ref_take(v_a_2414_);
v___x_2417_ = lean_array_set(v___x_2416_, v_i_2412_, v_v_2413_);
v___x_2418_ = lean_st_ref_put(v_a_2414_, v___x_2417_);
v___x_2419_ = lean_box(0);
v___x_2420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2420_, 0, v___x_2419_);
return v___x_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie___redArg___boxed(lean_object* v_i_2421_, lean_object* v_v_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_){
_start:
{
lean_object* v_res_2425_; 
v_res_2425_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_i_2421_, v_v_2422_, v_a_2423_);
lean_dec(v_a_2423_);
lean_dec(v_i_2421_);
return v_res_2425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie(lean_object* v_00_u03b1_2426_, lean_object* v_i_2427_, lean_object* v_v_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_){
_start:
{
lean_object* v___x_2435_; 
v___x_2435_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_i_2427_, v_v_2428_, v_a_2429_);
return v___x_2435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie___boxed(lean_object* v_00_u03b1_2436_, lean_object* v_i_2437_, lean_object* v_v_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_){
_start:
{
lean_object* v_res_2445_; 
v_res_2445_ = l_Lean_Meta_LazyDiscrTree_setTrie(v_00_u03b1_2436_, v_i_2437_, v_v_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_);
lean_dec(v_a_2443_);
lean_dec_ref(v_a_2442_);
lean_dec(v_a_2441_);
lean_dec_ref(v_a_2440_);
lean_dec(v_a_2439_);
lean_dec(v_i_2437_);
return v_res_2445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___redArg___lam__0(lean_object* v_e_2446_, lean_object* v_a_2447_){
_start:
{
lean_object* v_sz_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; 
v_sz_2448_ = lean_array_get_size(v_a_2447_);
v___x_2449_ = lean_unsigned_to_nat(0u);
v___x_2450_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_2451_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_2452_ = lean_unsigned_to_nat(1u);
v___x_2453_ = lean_mk_empty_array_with_capacity(v___x_2452_);
v___x_2454_ = lean_array_push(v___x_2453_, v_e_2446_);
v___x_2455_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2455_, 0, v___x_2450_);
lean_ctor_set(v___x_2455_, 1, v___x_2449_);
lean_ctor_set(v___x_2455_, 2, v___x_2451_);
lean_ctor_set(v___x_2455_, 3, v___x_2454_);
v___x_2456_ = lean_array_push(v_a_2447_, v___x_2455_);
v___x_2457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2457_, 0, v_sz_2448_);
lean_ctor_set(v___x_2457_, 1, v___x_2456_);
return v___x_2457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___redArg(lean_object* v_inst_2458_, lean_object* v_e_2459_){
_start:
{
lean_object* v_modifyGet_2460_; lean_object* v___f_2461_; lean_object* v___x_2462_; 
v_modifyGet_2460_ = lean_ctor_get(v_inst_2458_, 2);
lean_inc(v_modifyGet_2460_);
lean_dec_ref(v_inst_2458_);
v___f_2461_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_newTrie___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2461_, 0, v_e_2459_);
v___x_2462_ = lean_apply_2(v_modifyGet_2460_, lean_box(0), v___f_2461_);
return v___x_2462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie(lean_object* v_m_2463_, lean_object* v_00_u03b1_2464_, lean_object* v_inst_2465_, lean_object* v_inst_2466_, lean_object* v_e_2467_){
_start:
{
lean_object* v___x_2468_; 
v___x_2468_ = l_Lean_Meta_LazyDiscrTree_newTrie___redArg(v_inst_2466_, v_e_2467_);
return v___x_2468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___boxed(lean_object* v_m_2469_, lean_object* v_00_u03b1_2470_, lean_object* v_inst_2471_, lean_object* v_inst_2472_, lean_object* v_e_2473_){
_start:
{
lean_object* v_res_2474_; 
v_res_2474_ = l_Lean_Meta_LazyDiscrTree_newTrie(v_m_2469_, v_00_u03b1_2470_, v_inst_2471_, v_inst_2472_, v_e_2473_);
lean_dec_ref(v_inst_2471_);
return v_res_2474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(lean_object* v_i_2475_, lean_object* v_e_2476_, lean_object* v_a_2477_){
_start:
{
lean_object* v___x_2479_; lean_object* v_fst_2481_; lean_object* v_snd_2482_; lean_object* v___x_2485_; lean_object* v___x_2486_; uint8_t v___x_2487_; 
v___x_2479_ = lean_st_ref_take(v_a_2477_);
v___x_2485_ = lean_box(0);
v___x_2486_ = lean_array_get_size(v___x_2479_);
v___x_2487_ = lean_nat_dec_lt(v_i_2475_, v___x_2486_);
if (v___x_2487_ == 0)
{
lean_dec_ref(v_e_2476_);
v_fst_2481_ = v___x_2485_;
v_snd_2482_ = v___x_2479_;
goto v___jp_2480_;
}
else
{
lean_object* v_v_2488_; lean_object* v_xs_x27_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; 
v_v_2488_ = lean_array_fget(v___x_2479_, v_i_2475_);
v_xs_x27_2489_ = lean_array_fset(v___x_2479_, v_i_2475_, v___x_2485_);
v___x_2490_ = l_Lean_Meta_LazyDiscrTree_Trie_pushPending___redArg(v_v_2488_, v_e_2476_);
v___x_2491_ = lean_array_fset(v_xs_x27_2489_, v_i_2475_, v___x_2490_);
v_fst_2481_ = v___x_2485_;
v_snd_2482_ = v___x_2491_;
goto v___jp_2480_;
}
v___jp_2480_:
{
lean_object* v___x_2483_; lean_object* v___x_2484_; 
v___x_2483_ = lean_st_ref_put(v_a_2477_, v_snd_2482_);
v___x_2484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2484_, 0, v_fst_2481_);
return v___x_2484_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg___boxed(lean_object* v_i_2492_, lean_object* v_e_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_){
_start:
{
lean_object* v_res_2496_; 
v_res_2496_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_i_2492_, v_e_2493_, v_a_2494_);
lean_dec(v_a_2494_);
lean_dec(v_i_2492_);
return v_res_2496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie(lean_object* v_00_u03b1_2497_, lean_object* v_i_2498_, lean_object* v_e_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_){
_start:
{
lean_object* v___x_2506_; 
v___x_2506_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_i_2498_, v_e_2499_, v_a_2500_);
return v___x_2506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___boxed(lean_object* v_00_u03b1_2507_, lean_object* v_i_2508_, lean_object* v_e_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_){
_start:
{
lean_object* v_res_2516_; 
v_res_2516_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie(v_00_u03b1_2507_, v_i_2508_, v_e_2509_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_);
lean_dec(v_a_2514_);
lean_dec_ref(v_a_2513_);
lean_dec(v_a_2512_);
lean_dec_ref(v_a_2511_);
lean_dec(v_a_2510_);
lean_dec(v_i_2508_);
return v_res_2516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0(lean_object* v_x_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_){
_start:
{
lean_object* v___x_2524_; 
lean_inc(v___y_2518_);
v___x_2524_ = lean_apply_6(v_x_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, lean_box(0));
return v___x_2524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0___boxed(lean_object* v_x_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_){
_start:
{
lean_object* v_res_2532_; 
v_res_2532_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0(v_x_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_);
lean_dec(v___y_2526_);
return v_res_2532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(lean_object* v_lctx_2533_, lean_object* v_localInsts_2534_, lean_object* v_x_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_){
_start:
{
lean_object* v___f_2542_; lean_object* v___x_2543_; 
lean_inc(v___y_2536_);
v___f_2542_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2542_, 0, v_x_2535_);
lean_closure_set(v___f_2542_, 1, v___y_2536_);
v___x_2543_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_2533_, v_localInsts_2534_, v___f_2542_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_);
if (lean_obj_tag(v___x_2543_) == 0)
{
return v___x_2543_;
}
else
{
lean_object* v_a_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2551_; 
v_a_2544_ = lean_ctor_get(v___x_2543_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2543_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2546_ = v___x_2543_;
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_a_2544_);
lean_dec(v___x_2543_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v___x_2549_; 
if (v_isShared_2547_ == 0)
{
v___x_2549_ = v___x_2546_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_a_2544_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___boxed(lean_object* v_lctx_2552_, lean_object* v_localInsts_2553_, lean_object* v_x_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_){
_start:
{
lean_object* v_res_2561_; 
v_res_2561_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(v_lctx_2552_, v_localInsts_2553_, v_x_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_);
lean_dec(v___y_2559_);
lean_dec_ref(v___y_2558_);
lean_dec(v___y_2557_);
lean_dec_ref(v___y_2556_);
lean_dec(v___y_2555_);
return v_res_2561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0(lean_object* v_00_u03b1_2562_, lean_object* v_00_u03b1_2563_, lean_object* v_lctx_2564_, lean_object* v_localInsts_2565_, lean_object* v_x_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_){
_start:
{
lean_object* v___x_2573_; 
v___x_2573_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(v_lctx_2564_, v_localInsts_2565_, v_x_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_);
return v___x_2573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___boxed(lean_object* v_00_u03b1_2574_, lean_object* v_00_u03b1_2575_, lean_object* v_lctx_2576_, lean_object* v_localInsts_2577_, lean_object* v_x_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_){
_start:
{
lean_object* v_res_2585_; 
v_res_2585_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0(v_00_u03b1_2574_, v_00_u03b1_2575_, v_lctx_2576_, v_localInsts_2577_, v_x_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_);
lean_dec(v___y_2583_);
lean_dec_ref(v___y_2582_);
lean_dec(v___y_2581_);
lean_dec_ref(v___y_2580_);
lean_dec(v___y_2579_);
return v_res_2585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(lean_object* v_e_2586_, lean_object* v___y_2587_){
_start:
{
lean_object* v___x_2589_; lean_object* v_sz_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; 
v___x_2589_ = lean_st_ref_take(v___y_2587_);
v_sz_2590_ = lean_array_get_size(v___x_2589_);
v___x_2591_ = lean_unsigned_to_nat(0u);
v___x_2592_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_2593_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_2594_ = lean_unsigned_to_nat(1u);
v___x_2595_ = lean_mk_empty_array_with_capacity(v___x_2594_);
v___x_2596_ = lean_array_push(v___x_2595_, v_e_2586_);
v___x_2597_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2597_, 0, v___x_2592_);
lean_ctor_set(v___x_2597_, 1, v___x_2591_);
lean_ctor_set(v___x_2597_, 2, v___x_2593_);
lean_ctor_set(v___x_2597_, 3, v___x_2596_);
v___x_2598_ = lean_array_push(v___x_2589_, v___x_2597_);
v___x_2599_ = lean_st_ref_put(v___y_2587_, v___x_2598_);
v___x_2600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2600_, 0, v_sz_2590_);
return v___x_2600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg___boxed(lean_object* v_e_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_){
_start:
{
lean_object* v_res_2604_; 
v_res_2604_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v_e_2601_, v___y_2602_);
lean_dec(v___y_2602_);
return v_res_2604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2(lean_object* v_00_u03b1_2605_, lean_object* v_e_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_){
_start:
{
lean_object* v___x_2613_; 
v___x_2613_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v_e_2606_, v___y_2607_);
return v___x_2613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___boxed(lean_object* v_00_u03b1_2614_, lean_object* v_e_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_){
_start:
{
lean_object* v_res_2622_; 
v_res_2622_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2(v_00_u03b1_2614_, v_e_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_);
lean_dec(v___y_2620_);
lean_dec_ref(v___y_2619_);
lean_dec(v___y_2618_);
lean_dec_ref(v___y_2617_);
lean_dec(v___y_2616_);
return v_res_2622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0(uint8_t v___x_2623_, lean_object* v_todo_2624_, lean_object* v_e_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_){
_start:
{
lean_object* v___x_2632_; 
v___x_2632_ = l_Lean_Meta_LazyDiscrTree_pushArgs(v___x_2623_, v_todo_2624_, v_e_2625_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_);
return v___x_2632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0___boxed(lean_object* v___x_2633_, lean_object* v_todo_2634_, lean_object* v_e_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_){
_start:
{
uint8_t v___x_3412__boxed_2642_; lean_object* v_res_2643_; 
v___x_3412__boxed_2642_ = lean_unbox(v___x_2633_);
v_res_2643_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0(v___x_3412__boxed_2642_, v_todo_2634_, v_e_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_);
lean_dec(v___y_2640_);
lean_dec_ref(v___y_2639_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2637_);
lean_dec(v___y_2636_);
return v_res_2643_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(lean_object* v_a_2644_, lean_object* v_b_2645_, lean_object* v_x_2646_){
_start:
{
if (lean_obj_tag(v_x_2646_) == 0)
{
lean_dec(v_b_2645_);
lean_dec(v_a_2644_);
return v_x_2646_;
}
else
{
lean_object* v_key_2647_; lean_object* v_value_2648_; lean_object* v_tail_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2661_; 
v_key_2647_ = lean_ctor_get(v_x_2646_, 0);
v_value_2648_ = lean_ctor_get(v_x_2646_, 1);
v_tail_2649_ = lean_ctor_get(v_x_2646_, 2);
v_isSharedCheck_2661_ = !lean_is_exclusive(v_x_2646_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2651_ = v_x_2646_;
v_isShared_2652_ = v_isSharedCheck_2661_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_tail_2649_);
lean_inc(v_value_2648_);
lean_inc(v_key_2647_);
lean_dec(v_x_2646_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2661_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
uint8_t v___x_2653_; 
v___x_2653_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_2647_, v_a_2644_);
if (v___x_2653_ == 0)
{
lean_object* v___x_2654_; lean_object* v___x_2656_; 
v___x_2654_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(v_a_2644_, v_b_2645_, v_tail_2649_);
if (v_isShared_2652_ == 0)
{
lean_ctor_set(v___x_2651_, 2, v___x_2654_);
v___x_2656_ = v___x_2651_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v_key_2647_);
lean_ctor_set(v_reuseFailAlloc_2657_, 1, v_value_2648_);
lean_ctor_set(v_reuseFailAlloc_2657_, 2, v___x_2654_);
v___x_2656_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
return v___x_2656_;
}
}
else
{
lean_object* v___x_2659_; 
lean_dec(v_value_2648_);
lean_dec(v_key_2647_);
if (v_isShared_2652_ == 0)
{
lean_ctor_set(v___x_2651_, 1, v_b_2645_);
lean_ctor_set(v___x_2651_, 0, v_a_2644_);
v___x_2659_ = v___x_2651_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_a_2644_);
lean_ctor_set(v_reuseFailAlloc_2660_, 1, v_b_2645_);
lean_ctor_set(v_reuseFailAlloc_2660_, 2, v_tail_2649_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(lean_object* v_a_2662_, lean_object* v_x_2663_){
_start:
{
if (lean_obj_tag(v_x_2663_) == 0)
{
uint8_t v___x_2664_; 
v___x_2664_ = 0;
return v___x_2664_;
}
else
{
lean_object* v_key_2665_; lean_object* v_tail_2666_; uint8_t v___x_2667_; 
v_key_2665_ = lean_ctor_get(v_x_2663_, 0);
v_tail_2666_ = lean_ctor_get(v_x_2663_, 2);
v___x_2667_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_2665_, v_a_2662_);
if (v___x_2667_ == 0)
{
v_x_2663_ = v_tail_2666_;
goto _start;
}
else
{
return v___x_2667_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg___boxed(lean_object* v_a_2669_, lean_object* v_x_2670_){
_start:
{
uint8_t v_res_2671_; lean_object* v_r_2672_; 
v_res_2671_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(v_a_2669_, v_x_2670_);
lean_dec(v_x_2670_);
lean_dec(v_a_2669_);
v_r_2672_ = lean_box(v_res_2671_);
return v_r_2672_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7___redArg(lean_object* v_x_2673_, lean_object* v_x_2674_){
_start:
{
if (lean_obj_tag(v_x_2674_) == 0)
{
return v_x_2673_;
}
else
{
lean_object* v_key_2675_; lean_object* v_value_2676_; lean_object* v_tail_2677_; lean_object* v___x_2679_; uint8_t v_isShared_2680_; uint8_t v_isSharedCheck_2700_; 
v_key_2675_ = lean_ctor_get(v_x_2674_, 0);
v_value_2676_ = lean_ctor_get(v_x_2674_, 1);
v_tail_2677_ = lean_ctor_get(v_x_2674_, 2);
v_isSharedCheck_2700_ = !lean_is_exclusive(v_x_2674_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2679_ = v_x_2674_;
v_isShared_2680_ = v_isSharedCheck_2700_;
goto v_resetjp_2678_;
}
else
{
lean_inc(v_tail_2677_);
lean_inc(v_value_2676_);
lean_inc(v_key_2675_);
lean_dec(v_x_2674_);
v___x_2679_ = lean_box(0);
v_isShared_2680_ = v_isSharedCheck_2700_;
goto v_resetjp_2678_;
}
v_resetjp_2678_:
{
lean_object* v___x_2681_; uint64_t v___x_2682_; uint64_t v___x_2683_; uint64_t v___x_2684_; uint64_t v_fold_2685_; uint64_t v___x_2686_; uint64_t v___x_2687_; uint64_t v___x_2688_; size_t v___x_2689_; size_t v___x_2690_; size_t v___x_2691_; size_t v___x_2692_; size_t v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2696_; 
v___x_2681_ = lean_array_get_size(v_x_2673_);
v___x_2682_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_key_2675_);
v___x_2683_ = 32ULL;
v___x_2684_ = lean_uint64_shift_right(v___x_2682_, v___x_2683_);
v_fold_2685_ = lean_uint64_xor(v___x_2682_, v___x_2684_);
v___x_2686_ = 16ULL;
v___x_2687_ = lean_uint64_shift_right(v_fold_2685_, v___x_2686_);
v___x_2688_ = lean_uint64_xor(v_fold_2685_, v___x_2687_);
v___x_2689_ = lean_uint64_to_usize(v___x_2688_);
v___x_2690_ = lean_usize_of_nat(v___x_2681_);
v___x_2691_ = ((size_t)1ULL);
v___x_2692_ = lean_usize_sub(v___x_2690_, v___x_2691_);
v___x_2693_ = lean_usize_land(v___x_2689_, v___x_2692_);
v___x_2694_ = lean_array_uget_borrowed(v_x_2673_, v___x_2693_);
lean_inc(v___x_2694_);
if (v_isShared_2680_ == 0)
{
lean_ctor_set(v___x_2679_, 2, v___x_2694_);
v___x_2696_ = v___x_2679_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v_key_2675_);
lean_ctor_set(v_reuseFailAlloc_2699_, 1, v_value_2676_);
lean_ctor_set(v_reuseFailAlloc_2699_, 2, v___x_2694_);
v___x_2696_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
lean_object* v___x_2697_; 
v___x_2697_ = lean_array_uset(v_x_2673_, v___x_2693_, v___x_2696_);
v_x_2673_ = v___x_2697_;
v_x_2674_ = v_tail_2677_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6___redArg(lean_object* v_i_2701_, lean_object* v_source_2702_, lean_object* v_target_2703_){
_start:
{
lean_object* v___x_2704_; uint8_t v___x_2705_; 
v___x_2704_ = lean_array_get_size(v_source_2702_);
v___x_2705_ = lean_nat_dec_lt(v_i_2701_, v___x_2704_);
if (v___x_2705_ == 0)
{
lean_dec_ref(v_source_2702_);
lean_dec(v_i_2701_);
return v_target_2703_;
}
else
{
lean_object* v_es_2706_; lean_object* v___x_2707_; lean_object* v_source_2708_; lean_object* v_target_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; 
v_es_2706_ = lean_array_fget(v_source_2702_, v_i_2701_);
v___x_2707_ = lean_box(0);
v_source_2708_ = lean_array_fset(v_source_2702_, v_i_2701_, v___x_2707_);
v_target_2709_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7___redArg(v_target_2703_, v_es_2706_);
v___x_2710_ = lean_unsigned_to_nat(1u);
v___x_2711_ = lean_nat_add(v_i_2701_, v___x_2710_);
lean_dec(v_i_2701_);
v_i_2701_ = v___x_2711_;
v_source_2702_ = v_source_2708_;
v_target_2703_ = v_target_2709_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5___redArg(lean_object* v_data_2713_){
_start:
{
lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v_nbuckets_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; 
v___x_2714_ = lean_array_get_size(v_data_2713_);
v___x_2715_ = lean_unsigned_to_nat(2u);
v_nbuckets_2716_ = lean_nat_mul(v___x_2714_, v___x_2715_);
v___x_2717_ = lean_unsigned_to_nat(0u);
v___x_2718_ = lean_box(0);
v___x_2719_ = lean_mk_array(v_nbuckets_2716_, v___x_2718_);
v___x_2720_ = lean_array_propagate_mark(v_data_2713_, v___x_2719_);
v___x_2721_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6___redArg(v___x_2717_, v_data_2713_, v___x_2720_);
return v___x_2721_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(lean_object* v_m_2722_, lean_object* v_a_2723_, lean_object* v_b_2724_){
_start:
{
lean_object* v_size_2725_; lean_object* v_buckets_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2769_; 
v_size_2725_ = lean_ctor_get(v_m_2722_, 0);
v_buckets_2726_ = lean_ctor_get(v_m_2722_, 1);
v_isSharedCheck_2769_ = !lean_is_exclusive(v_m_2722_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2728_ = v_m_2722_;
v_isShared_2729_ = v_isSharedCheck_2769_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_buckets_2726_);
lean_inc(v_size_2725_);
lean_dec(v_m_2722_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2769_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
lean_object* v___x_2730_; uint64_t v___x_2731_; uint64_t v___x_2732_; uint64_t v___x_2733_; uint64_t v_fold_2734_; uint64_t v___x_2735_; uint64_t v___x_2736_; uint64_t v___x_2737_; size_t v___x_2738_; size_t v___x_2739_; size_t v___x_2740_; size_t v___x_2741_; size_t v___x_2742_; lean_object* v_bkt_2743_; uint8_t v___x_2744_; 
v___x_2730_ = lean_array_get_size(v_buckets_2726_);
v___x_2731_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_a_2723_);
v___x_2732_ = 32ULL;
v___x_2733_ = lean_uint64_shift_right(v___x_2731_, v___x_2732_);
v_fold_2734_ = lean_uint64_xor(v___x_2731_, v___x_2733_);
v___x_2735_ = 16ULL;
v___x_2736_ = lean_uint64_shift_right(v_fold_2734_, v___x_2735_);
v___x_2737_ = lean_uint64_xor(v_fold_2734_, v___x_2736_);
v___x_2738_ = lean_uint64_to_usize(v___x_2737_);
v___x_2739_ = lean_usize_of_nat(v___x_2730_);
v___x_2740_ = ((size_t)1ULL);
v___x_2741_ = lean_usize_sub(v___x_2739_, v___x_2740_);
v___x_2742_ = lean_usize_land(v___x_2738_, v___x_2741_);
v_bkt_2743_ = lean_array_uget_borrowed(v_buckets_2726_, v___x_2742_);
v___x_2744_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(v_a_2723_, v_bkt_2743_);
if (v___x_2744_ == 0)
{
lean_object* v___x_2745_; lean_object* v_size_x27_2746_; lean_object* v___x_2747_; lean_object* v_buckets_x27_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; uint8_t v___x_2754_; 
v___x_2745_ = lean_unsigned_to_nat(1u);
v_size_x27_2746_ = lean_nat_add(v_size_2725_, v___x_2745_);
lean_dec(v_size_2725_);
lean_inc(v_bkt_2743_);
v___x_2747_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2747_, 0, v_a_2723_);
lean_ctor_set(v___x_2747_, 1, v_b_2724_);
lean_ctor_set(v___x_2747_, 2, v_bkt_2743_);
v_buckets_x27_2748_ = lean_array_uset(v_buckets_2726_, v___x_2742_, v___x_2747_);
v___x_2749_ = lean_unsigned_to_nat(4u);
v___x_2750_ = lean_nat_mul(v_size_x27_2746_, v___x_2749_);
v___x_2751_ = lean_unsigned_to_nat(3u);
v___x_2752_ = lean_nat_div(v___x_2750_, v___x_2751_);
lean_dec(v___x_2750_);
v___x_2753_ = lean_array_get_size(v_buckets_x27_2748_);
v___x_2754_ = lean_nat_dec_le(v___x_2752_, v___x_2753_);
lean_dec(v___x_2752_);
if (v___x_2754_ == 0)
{
lean_object* v_val_2755_; lean_object* v___x_2757_; 
v_val_2755_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5___redArg(v_buckets_x27_2748_);
if (v_isShared_2729_ == 0)
{
lean_ctor_set(v___x_2728_, 1, v_val_2755_);
lean_ctor_set(v___x_2728_, 0, v_size_x27_2746_);
v___x_2757_ = v___x_2728_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v_size_x27_2746_);
lean_ctor_set(v_reuseFailAlloc_2758_, 1, v_val_2755_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
return v___x_2757_;
}
}
else
{
lean_object* v___x_2760_; 
if (v_isShared_2729_ == 0)
{
lean_ctor_set(v___x_2728_, 1, v_buckets_x27_2748_);
lean_ctor_set(v___x_2728_, 0, v_size_x27_2746_);
v___x_2760_ = v___x_2728_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_size_x27_2746_);
lean_ctor_set(v_reuseFailAlloc_2761_, 1, v_buckets_x27_2748_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
return v___x_2760_;
}
}
}
else
{
lean_object* v___x_2762_; lean_object* v_buckets_x27_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2767_; 
lean_inc(v_bkt_2743_);
v___x_2762_ = lean_box(0);
v_buckets_x27_2763_ = lean_array_uset(v_buckets_2726_, v___x_2742_, v___x_2762_);
v___x_2764_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(v_a_2723_, v_b_2724_, v_bkt_2743_);
v___x_2765_ = lean_array_uset(v_buckets_x27_2763_, v___x_2742_, v___x_2764_);
if (v_isShared_2729_ == 0)
{
lean_ctor_set(v___x_2728_, 1, v___x_2765_);
v___x_2767_ = v___x_2728_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_size_2725_);
lean_ctor_set(v_reuseFailAlloc_2768_, 1, v___x_2765_);
v___x_2767_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
return v___x_2767_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(lean_object* v_a_2770_, lean_object* v_x_2771_){
_start:
{
if (lean_obj_tag(v_x_2771_) == 0)
{
lean_object* v___x_2772_; 
v___x_2772_ = lean_box(0);
return v___x_2772_;
}
else
{
lean_object* v_key_2773_; lean_object* v_value_2774_; lean_object* v_tail_2775_; uint8_t v___x_2776_; 
v_key_2773_ = lean_ctor_get(v_x_2771_, 0);
v_value_2774_ = lean_ctor_get(v_x_2771_, 1);
v_tail_2775_ = lean_ctor_get(v_x_2771_, 2);
v___x_2776_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_2773_, v_a_2770_);
if (v___x_2776_ == 0)
{
v_x_2771_ = v_tail_2775_;
goto _start;
}
else
{
lean_object* v___x_2778_; 
lean_inc(v_value_2774_);
v___x_2778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2778_, 0, v_value_2774_);
return v___x_2778_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg___boxed(lean_object* v_a_2779_, lean_object* v_x_2780_){
_start:
{
lean_object* v_res_2781_; 
v_res_2781_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(v_a_2779_, v_x_2780_);
lean_dec(v_x_2780_);
lean_dec(v_a_2779_);
return v_res_2781_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(lean_object* v_m_2782_, lean_object* v_a_2783_){
_start:
{
lean_object* v_buckets_2784_; lean_object* v___x_2785_; uint64_t v___x_2786_; uint64_t v___x_2787_; uint64_t v___x_2788_; uint64_t v_fold_2789_; uint64_t v___x_2790_; uint64_t v___x_2791_; uint64_t v___x_2792_; size_t v___x_2793_; size_t v___x_2794_; size_t v___x_2795_; size_t v___x_2796_; size_t v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; 
v_buckets_2784_ = lean_ctor_get(v_m_2782_, 1);
v___x_2785_ = lean_array_get_size(v_buckets_2784_);
v___x_2786_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_a_2783_);
v___x_2787_ = 32ULL;
v___x_2788_ = lean_uint64_shift_right(v___x_2786_, v___x_2787_);
v_fold_2789_ = lean_uint64_xor(v___x_2786_, v___x_2788_);
v___x_2790_ = 16ULL;
v___x_2791_ = lean_uint64_shift_right(v_fold_2789_, v___x_2790_);
v___x_2792_ = lean_uint64_xor(v_fold_2789_, v___x_2791_);
v___x_2793_ = lean_uint64_to_usize(v___x_2792_);
v___x_2794_ = lean_usize_of_nat(v___x_2785_);
v___x_2795_ = ((size_t)1ULL);
v___x_2796_ = lean_usize_sub(v___x_2794_, v___x_2795_);
v___x_2797_ = lean_usize_land(v___x_2793_, v___x_2796_);
v___x_2798_ = lean_array_uget_borrowed(v_buckets_2784_, v___x_2797_);
v___x_2799_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(v_a_2783_, v___x_2798_);
return v___x_2799_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg___boxed(lean_object* v_m_2800_, lean_object* v_a_2801_){
_start:
{
lean_object* v_res_2802_; 
v_res_2802_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_m_2800_, v_a_2801_);
lean_dec(v_a_2801_);
lean_dec_ref(v_m_2800_);
return v_res_2802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(lean_object* v_p_2803_, lean_object* v_entry_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_){
_start:
{
lean_object* v_snd_2811_; lean_object* v_snd_2812_; lean_object* v_fst_2813_; lean_object* v_fst_2814_; lean_object* v_snd_2815_; lean_object* v_fst_2816_; lean_object* v_fst_2817_; lean_object* v_snd_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; uint8_t v___x_2821_; 
v_snd_2811_ = lean_ctor_get(v_p_2803_, 1);
v_snd_2812_ = lean_ctor_get(v_entry_2804_, 1);
lean_inc(v_snd_2812_);
v_fst_2813_ = lean_ctor_get(v_p_2803_, 0);
v_fst_2814_ = lean_ctor_get(v_snd_2811_, 0);
v_snd_2815_ = lean_ctor_get(v_snd_2811_, 1);
v_fst_2816_ = lean_ctor_get(v_entry_2804_, 0);
lean_inc(v_fst_2816_);
lean_dec_ref(v_entry_2804_);
v_fst_2817_ = lean_ctor_get(v_snd_2812_, 0);
lean_inc(v_fst_2817_);
v_snd_2818_ = lean_ctor_get(v_snd_2812_, 1);
v___x_2819_ = lean_array_get_size(v_fst_2816_);
v___x_2820_ = lean_unsigned_to_nat(0u);
v___x_2821_ = lean_nat_dec_eq(v___x_2819_, v___x_2820_);
if (v___x_2821_ == 0)
{
lean_object* v_fst_2822_; lean_object* v_snd_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2928_; 
v_fst_2822_ = lean_ctor_get(v_fst_2817_, 0);
v_snd_2823_ = lean_ctor_get(v_fst_2817_, 1);
v_isSharedCheck_2928_ = !lean_is_exclusive(v_fst_2817_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2825_ = v_fst_2817_;
v_isShared_2826_ = v_isSharedCheck_2928_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_snd_2823_);
lean_inc(v_fst_2822_);
lean_dec(v_fst_2817_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2928_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v_e_2830_; lean_object* v_todo_2831_; lean_object* v___x_2832_; lean_object* v___f_2833_; lean_object* v___x_2834_; 
v___x_2827_ = l_Lean_instInhabitedExpr;
v___x_2828_ = lean_unsigned_to_nat(1u);
v___x_2829_ = lean_nat_sub(v___x_2819_, v___x_2828_);
v_e_2830_ = lean_array_get(v___x_2827_, v_fst_2816_, v___x_2829_);
lean_dec(v___x_2829_);
v_todo_2831_ = lean_array_pop(v_fst_2816_);
v___x_2832_ = lean_box(v___x_2821_);
v___f_2833_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2833_, 0, v___x_2832_);
lean_closure_set(v___f_2833_, 1, v_todo_2831_);
lean_closure_set(v___f_2833_, 2, v_e_2830_);
v___x_2834_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(v_fst_2822_, v_snd_2823_, v___f_2833_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_, v_a_2809_);
if (lean_obj_tag(v___x_2834_) == 0)
{
lean_object* v_a_2835_; lean_object* v_fst_2836_; lean_object* v_snd_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2919_; 
v_a_2835_ = lean_ctor_get(v___x_2834_, 0);
lean_inc(v_a_2835_);
lean_dec_ref_known(v___x_2834_, 1);
v_fst_2836_ = lean_ctor_get(v_a_2835_, 0);
v_snd_2837_ = lean_ctor_get(v_a_2835_, 1);
v_isSharedCheck_2919_ = !lean_is_exclusive(v_a_2835_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2839_ = v_a_2835_;
v_isShared_2840_ = v_isSharedCheck_2919_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_snd_2837_);
lean_inc(v_fst_2836_);
lean_dec(v_a_2835_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2919_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
lean_object* v___x_2841_; uint8_t v___x_2842_; 
v___x_2841_ = lean_box(3);
v___x_2842_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_fst_2836_, v___x_2841_);
if (v___x_2842_ == 0)
{
lean_object* v___x_2843_; 
v___x_2843_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_snd_2815_, v_fst_2836_);
if (lean_obj_tag(v___x_2843_) == 0)
{
lean_object* v___x_2845_; 
lean_inc(v_snd_2815_);
lean_inc(v_fst_2814_);
lean_inc(v_fst_2813_);
lean_dec_ref(v_p_2803_);
lean_inc(v_snd_2812_);
if (v_isShared_2840_ == 0)
{
lean_ctor_set(v___x_2839_, 1, v_snd_2812_);
lean_ctor_set(v___x_2839_, 0, v_snd_2837_);
v___x_2845_ = v___x_2839_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v_snd_2837_);
lean_ctor_set(v_reuseFailAlloc_2868_, 1, v_snd_2812_);
v___x_2845_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2865_; 
v_isSharedCheck_2865_ = !lean_is_exclusive(v_snd_2812_);
if (v_isSharedCheck_2865_ == 0)
{
lean_object* v_unused_2866_; lean_object* v_unused_2867_; 
v_unused_2866_ = lean_ctor_get(v_snd_2812_, 1);
lean_dec(v_unused_2866_);
v_unused_2867_ = lean_ctor_get(v_snd_2812_, 0);
lean_dec(v_unused_2867_);
v___x_2847_ = v_snd_2812_;
v_isShared_2848_ = v_isSharedCheck_2865_;
goto v_resetjp_2846_;
}
else
{
lean_dec(v_snd_2812_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2865_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
lean_object* v___x_2849_; lean_object* v_a_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2864_; 
v___x_2849_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v___x_2845_, v_a_2805_);
v_a_2850_ = lean_ctor_get(v___x_2849_, 0);
v_isSharedCheck_2864_ = !lean_is_exclusive(v___x_2849_);
if (v_isSharedCheck_2864_ == 0)
{
v___x_2852_ = v___x_2849_;
v_isShared_2853_ = v_isSharedCheck_2864_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_a_2850_);
lean_dec(v___x_2849_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2864_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
lean_object* v___x_2854_; lean_object* v___x_2856_; 
v___x_2854_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_snd_2815_, v_fst_2836_, v_a_2850_);
if (v_isShared_2826_ == 0)
{
lean_ctor_set(v___x_2825_, 1, v___x_2854_);
lean_ctor_set(v___x_2825_, 0, v_fst_2814_);
v___x_2856_ = v___x_2825_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v_fst_2814_);
lean_ctor_set(v_reuseFailAlloc_2863_, 1, v___x_2854_);
v___x_2856_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
lean_object* v___x_2858_; 
if (v_isShared_2848_ == 0)
{
lean_ctor_set(v___x_2847_, 1, v___x_2856_);
lean_ctor_set(v___x_2847_, 0, v_fst_2813_);
v___x_2858_ = v___x_2847_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v_fst_2813_);
lean_ctor_set(v_reuseFailAlloc_2862_, 1, v___x_2856_);
v___x_2858_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
lean_object* v___x_2860_; 
if (v_isShared_2853_ == 0)
{
lean_ctor_set(v___x_2852_, 0, v___x_2858_);
v___x_2860_ = v___x_2852_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v___x_2858_);
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
}
}
}
else
{
lean_object* v_val_2869_; lean_object* v___x_2871_; 
lean_dec(v_fst_2836_);
lean_del_object(v___x_2825_);
v_val_2869_ = lean_ctor_get(v___x_2843_, 0);
lean_inc(v_val_2869_);
lean_dec_ref_known(v___x_2843_, 1);
if (v_isShared_2840_ == 0)
{
lean_ctor_set(v___x_2839_, 1, v_snd_2812_);
lean_ctor_set(v___x_2839_, 0, v_snd_2837_);
v___x_2871_ = v___x_2839_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v_snd_2837_);
lean_ctor_set(v_reuseFailAlloc_2881_, 1, v_snd_2812_);
v___x_2871_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
lean_object* v___x_2872_; lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2879_; 
v___x_2872_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_val_2869_, v___x_2871_, v_a_2805_);
lean_dec(v_val_2869_);
v_isSharedCheck_2879_ = !lean_is_exclusive(v___x_2872_);
if (v_isSharedCheck_2879_ == 0)
{
lean_object* v_unused_2880_; 
v_unused_2880_ = lean_ctor_get(v___x_2872_, 0);
lean_dec(v_unused_2880_);
v___x_2874_ = v___x_2872_;
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
else
{
lean_dec(v___x_2872_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
lean_object* v___x_2877_; 
if (v_isShared_2875_ == 0)
{
lean_ctor_set(v___x_2874_, 0, v_p_2803_);
v___x_2877_ = v___x_2874_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v_p_2803_);
v___x_2877_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
return v___x_2877_;
}
}
}
}
}
else
{
uint8_t v___x_2882_; 
lean_dec(v_fst_2836_);
v___x_2882_ = lean_nat_dec_eq(v_fst_2814_, v___x_2820_);
if (v___x_2882_ == 0)
{
lean_object* v___x_2884_; 
lean_del_object(v___x_2825_);
if (v_isShared_2840_ == 0)
{
lean_ctor_set(v___x_2839_, 1, v_snd_2812_);
lean_ctor_set(v___x_2839_, 0, v_snd_2837_);
v___x_2884_ = v___x_2839_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v_snd_2837_);
lean_ctor_set(v_reuseFailAlloc_2894_, 1, v_snd_2812_);
v___x_2884_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
lean_object* v___x_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2892_; 
v___x_2885_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_fst_2814_, v___x_2884_, v_a_2805_);
v_isSharedCheck_2892_ = !lean_is_exclusive(v___x_2885_);
if (v_isSharedCheck_2892_ == 0)
{
lean_object* v_unused_2893_; 
v_unused_2893_ = lean_ctor_get(v___x_2885_, 0);
lean_dec(v_unused_2893_);
v___x_2887_ = v___x_2885_;
v_isShared_2888_ = v_isSharedCheck_2892_;
goto v_resetjp_2886_;
}
else
{
lean_dec(v___x_2885_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2892_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v___x_2890_; 
if (v_isShared_2888_ == 0)
{
lean_ctor_set(v___x_2887_, 0, v_p_2803_);
v___x_2890_ = v___x_2887_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v_p_2803_);
v___x_2890_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
return v___x_2890_;
}
}
}
}
else
{
lean_object* v___x_2896_; 
lean_inc(v_snd_2815_);
lean_inc(v_fst_2813_);
lean_dec_ref(v_p_2803_);
lean_inc(v_snd_2812_);
if (v_isShared_2840_ == 0)
{
lean_ctor_set(v___x_2839_, 1, v_snd_2812_);
lean_ctor_set(v___x_2839_, 0, v_snd_2837_);
v___x_2896_ = v___x_2839_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_snd_2837_);
lean_ctor_set(v_reuseFailAlloc_2918_, 1, v_snd_2812_);
v___x_2896_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2915_; 
v_isSharedCheck_2915_ = !lean_is_exclusive(v_snd_2812_);
if (v_isSharedCheck_2915_ == 0)
{
lean_object* v_unused_2916_; lean_object* v_unused_2917_; 
v_unused_2916_ = lean_ctor_get(v_snd_2812_, 1);
lean_dec(v_unused_2916_);
v_unused_2917_ = lean_ctor_get(v_snd_2812_, 0);
lean_dec(v_unused_2917_);
v___x_2898_ = v_snd_2812_;
v_isShared_2899_ = v_isSharedCheck_2915_;
goto v_resetjp_2897_;
}
else
{
lean_dec(v_snd_2812_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2915_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2900_; lean_object* v_a_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2914_; 
v___x_2900_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v___x_2896_, v_a_2805_);
v_a_2901_ = lean_ctor_get(v___x_2900_, 0);
v_isSharedCheck_2914_ = !lean_is_exclusive(v___x_2900_);
if (v_isSharedCheck_2914_ == 0)
{
v___x_2903_ = v___x_2900_;
v_isShared_2904_ = v_isSharedCheck_2914_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_a_2901_);
lean_dec(v___x_2900_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2914_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v___x_2906_; 
if (v_isShared_2826_ == 0)
{
lean_ctor_set(v___x_2825_, 1, v_snd_2815_);
lean_ctor_set(v___x_2825_, 0, v_a_2901_);
v___x_2906_ = v___x_2825_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v_a_2901_);
lean_ctor_set(v_reuseFailAlloc_2913_, 1, v_snd_2815_);
v___x_2906_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
lean_object* v___x_2908_; 
if (v_isShared_2899_ == 0)
{
lean_ctor_set(v___x_2898_, 1, v___x_2906_);
lean_ctor_set(v___x_2898_, 0, v_fst_2813_);
v___x_2908_ = v___x_2898_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_fst_2813_);
lean_ctor_set(v_reuseFailAlloc_2912_, 1, v___x_2906_);
v___x_2908_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
lean_object* v___x_2910_; 
if (v_isShared_2904_ == 0)
{
lean_ctor_set(v___x_2903_, 0, v___x_2908_);
v___x_2910_ = v___x_2903_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v___x_2908_);
v___x_2910_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
return v___x_2910_;
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
lean_object* v_a_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2927_; 
lean_del_object(v___x_2825_);
lean_dec(v_snd_2812_);
lean_dec_ref(v_p_2803_);
v_a_2920_ = lean_ctor_get(v___x_2834_, 0);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2834_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2922_ = v___x_2834_;
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_a_2920_);
lean_dec(v___x_2834_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v___x_2925_; 
if (v_isShared_2923_ == 0)
{
v___x_2925_ = v___x_2922_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2926_, 0, v_a_2920_);
v___x_2925_ = v_reuseFailAlloc_2926_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
return v___x_2925_;
}
}
}
}
}
else
{
lean_object* v___x_2930_; uint8_t v_isShared_2931_; uint8_t v_isSharedCheck_2937_; 
lean_inc(v_snd_2818_);
lean_inc(v_fst_2813_);
lean_inc(v_snd_2811_);
lean_dec(v_fst_2817_);
lean_dec(v_fst_2816_);
lean_dec_ref(v_p_2803_);
v_isSharedCheck_2937_ = !lean_is_exclusive(v_snd_2812_);
if (v_isSharedCheck_2937_ == 0)
{
lean_object* v_unused_2938_; lean_object* v_unused_2939_; 
v_unused_2938_ = lean_ctor_get(v_snd_2812_, 1);
lean_dec(v_unused_2938_);
v_unused_2939_ = lean_ctor_get(v_snd_2812_, 0);
lean_dec(v_unused_2939_);
v___x_2930_ = v_snd_2812_;
v_isShared_2931_ = v_isSharedCheck_2937_;
goto v_resetjp_2929_;
}
else
{
lean_dec(v_snd_2812_);
v___x_2930_ = lean_box(0);
v_isShared_2931_ = v_isSharedCheck_2937_;
goto v_resetjp_2929_;
}
v_resetjp_2929_:
{
lean_object* v_values_2932_; lean_object* v___x_2934_; 
v_values_2932_ = lean_array_push(v_fst_2813_, v_snd_2818_);
if (v_isShared_2931_ == 0)
{
lean_ctor_set(v___x_2930_, 1, v_snd_2811_);
lean_ctor_set(v___x_2930_, 0, v_values_2932_);
v___x_2934_ = v___x_2930_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v_values_2932_);
lean_ctor_set(v_reuseFailAlloc_2936_, 1, v_snd_2811_);
v___x_2934_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
lean_object* v___x_2935_; 
v___x_2935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2935_, 0, v___x_2934_);
return v___x_2935_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___boxed(lean_object* v_p_2940_, lean_object* v_entry_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_){
_start:
{
lean_object* v_res_2948_; 
v_res_2948_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(v_p_2940_, v_entry_2941_, v_a_2942_, v_a_2943_, v_a_2944_, v_a_2945_, v_a_2946_);
lean_dec(v_a_2946_);
lean_dec_ref(v_a_2945_);
lean_dec(v_a_2944_);
lean_dec_ref(v_a_2943_);
lean_dec(v_a_2942_);
return v_res_2948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry(lean_object* v_00_u03b1_2949_, lean_object* v_p_2950_, lean_object* v_entry_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_){
_start:
{
lean_object* v___x_2958_; 
v___x_2958_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(v_p_2950_, v_entry_2951_, v_a_2952_, v_a_2953_, v_a_2954_, v_a_2955_, v_a_2956_);
return v___x_2958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___boxed(lean_object* v_00_u03b1_2959_, lean_object* v_p_2960_, lean_object* v_entry_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_){
_start:
{
lean_object* v_res_2968_; 
v_res_2968_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry(v_00_u03b1_2959_, v_p_2960_, v_entry_2961_, v_a_2962_, v_a_2963_, v_a_2964_, v_a_2965_, v_a_2966_);
lean_dec(v_a_2966_);
lean_dec_ref(v_a_2965_);
lean_dec(v_a_2964_);
lean_dec_ref(v_a_2963_);
lean_dec(v_a_2962_);
return v_res_2968_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1(lean_object* v_00_u03b2_2969_, lean_object* v_m_2970_, lean_object* v_a_2971_){
_start:
{
lean_object* v___x_2972_; 
v___x_2972_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_m_2970_, v_a_2971_);
return v___x_2972_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___boxed(lean_object* v_00_u03b2_2973_, lean_object* v_m_2974_, lean_object* v_a_2975_){
_start:
{
lean_object* v_res_2976_; 
v_res_2976_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1(v_00_u03b2_2973_, v_m_2974_, v_a_2975_);
lean_dec(v_a_2975_);
lean_dec_ref(v_m_2974_);
return v_res_2976_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3(lean_object* v_00_u03b2_2977_, lean_object* v_m_2978_, lean_object* v_a_2979_, lean_object* v_b_2980_){
_start:
{
lean_object* v___x_2981_; 
v___x_2981_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_m_2978_, v_a_2979_, v_b_2980_);
return v___x_2981_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1(lean_object* v_00_u03b2_2982_, lean_object* v_a_2983_, lean_object* v_x_2984_){
_start:
{
lean_object* v___x_2985_; 
v___x_2985_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(v_a_2983_, v_x_2984_);
return v___x_2985_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2986_, lean_object* v_a_2987_, lean_object* v_x_2988_){
_start:
{
lean_object* v_res_2989_; 
v_res_2989_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1(v_00_u03b2_2986_, v_a_2987_, v_x_2988_);
lean_dec(v_x_2988_);
lean_dec(v_a_2987_);
return v_res_2989_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4(lean_object* v_00_u03b2_2990_, lean_object* v_a_2991_, lean_object* v_x_2992_){
_start:
{
uint8_t v___x_2993_; 
v___x_2993_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(v_a_2991_, v_x_2992_);
return v___x_2993_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___boxed(lean_object* v_00_u03b2_2994_, lean_object* v_a_2995_, lean_object* v_x_2996_){
_start:
{
uint8_t v_res_2997_; lean_object* v_r_2998_; 
v_res_2997_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4(v_00_u03b2_2994_, v_a_2995_, v_x_2996_);
lean_dec(v_x_2996_);
lean_dec(v_a_2995_);
v_r_2998_ = lean_box(v_res_2997_);
return v_r_2998_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5(lean_object* v_00_u03b2_2999_, lean_object* v_data_3000_){
_start:
{
lean_object* v___x_3001_; 
v___x_3001_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5___redArg(v_data_3000_);
return v___x_3001_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6(lean_object* v_00_u03b2_3002_, lean_object* v_a_3003_, lean_object* v_b_3004_, lean_object* v_x_3005_){
_start:
{
lean_object* v___x_3006_; 
v___x_3006_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(v_a_3003_, v_b_3004_, v_x_3005_);
return v___x_3006_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_3007_, lean_object* v_i_3008_, lean_object* v_source_3009_, lean_object* v_target_3010_){
_start:
{
lean_object* v___x_3011_; 
v___x_3011_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6___redArg(v_i_3008_, v_source_3009_, v_target_3010_);
return v___x_3011_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_3012_, lean_object* v_x_3013_, lean_object* v_x_3014_){
_start:
{
lean_object* v___x_3015_; 
v___x_3015_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7___redArg(v_x_3013_, v_x_3014_);
return v___x_3015_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(lean_object* v_as_3016_, size_t v_i_3017_, size_t v_stop_3018_, lean_object* v_b_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_){
_start:
{
uint8_t v___x_3026_; 
v___x_3026_ = lean_usize_dec_eq(v_i_3017_, v_stop_3018_);
if (v___x_3026_ == 0)
{
lean_object* v___x_3027_; lean_object* v___x_3028_; 
v___x_3027_ = lean_array_uget_borrowed(v_as_3016_, v_i_3017_);
lean_inc(v___x_3027_);
v___x_3028_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(v_b_3019_, v___x_3027_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_);
if (lean_obj_tag(v___x_3028_) == 0)
{
lean_object* v_a_3029_; size_t v___x_3030_; size_t v___x_3031_; 
v_a_3029_ = lean_ctor_get(v___x_3028_, 0);
lean_inc(v_a_3029_);
lean_dec_ref_known(v___x_3028_, 1);
v___x_3030_ = ((size_t)1ULL);
v___x_3031_ = lean_usize_add(v_i_3017_, v___x_3030_);
v_i_3017_ = v___x_3031_;
v_b_3019_ = v_a_3029_;
goto _start;
}
else
{
return v___x_3028_;
}
}
else
{
lean_object* v___x_3033_; 
v___x_3033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3033_, 0, v_b_3019_);
return v___x_3033_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg___boxed(lean_object* v_as_3034_, lean_object* v_i_3035_, lean_object* v_stop_3036_, lean_object* v_b_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_){
_start:
{
size_t v_i_boxed_3044_; size_t v_stop_boxed_3045_; lean_object* v_res_3046_; 
v_i_boxed_3044_ = lean_unbox_usize(v_i_3035_);
lean_dec(v_i_3035_);
v_stop_boxed_3045_ = lean_unbox_usize(v_stop_3036_);
lean_dec(v_stop_3036_);
v_res_3046_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_as_3034_, v_i_boxed_3044_, v_stop_boxed_3045_, v_b_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_);
lean_dec(v___y_3042_);
lean_dec_ref(v___y_3041_);
lean_dec(v___y_3040_);
lean_dec_ref(v___y_3039_);
lean_dec(v___y_3038_);
lean_dec_ref(v_as_3034_);
return v_res_3046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(lean_object* v_values_3047_, lean_object* v_starIdx_3048_, lean_object* v_children_3049_, lean_object* v_entries_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_){
_start:
{
lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; uint8_t v___x_3061_; 
v___x_3057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3057_, 0, v_starIdx_3048_);
lean_ctor_set(v___x_3057_, 1, v_children_3049_);
v___x_3058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3058_, 0, v_values_3047_);
lean_ctor_set(v___x_3058_, 1, v___x_3057_);
v___x_3059_ = lean_unsigned_to_nat(0u);
v___x_3060_ = lean_array_get_size(v_entries_3050_);
v___x_3061_ = lean_nat_dec_lt(v___x_3059_, v___x_3060_);
if (v___x_3061_ == 0)
{
lean_object* v___x_3062_; 
v___x_3062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3062_, 0, v___x_3058_);
return v___x_3062_;
}
else
{
uint8_t v___x_3063_; 
v___x_3063_ = lean_nat_dec_le(v___x_3060_, v___x_3060_);
if (v___x_3063_ == 0)
{
if (v___x_3061_ == 0)
{
lean_object* v___x_3064_; 
v___x_3064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3064_, 0, v___x_3058_);
return v___x_3064_;
}
else
{
size_t v___x_3065_; size_t v___x_3066_; lean_object* v___x_3067_; 
v___x_3065_ = ((size_t)0ULL);
v___x_3066_ = lean_usize_of_nat(v___x_3060_);
v___x_3067_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_entries_3050_, v___x_3065_, v___x_3066_, v___x_3058_, v_a_3051_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3055_);
return v___x_3067_;
}
}
else
{
size_t v___x_3068_; size_t v___x_3069_; lean_object* v___x_3070_; 
v___x_3068_ = ((size_t)0ULL);
v___x_3069_ = lean_usize_of_nat(v___x_3060_);
v___x_3070_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_entries_3050_, v___x_3068_, v___x_3069_, v___x_3058_, v_a_3051_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3055_);
return v___x_3070_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg___boxed(lean_object* v_values_3071_, lean_object* v_starIdx_3072_, lean_object* v_children_3073_, lean_object* v_entries_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_){
_start:
{
lean_object* v_res_3081_; 
v_res_3081_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(v_values_3071_, v_starIdx_3072_, v_children_3073_, v_entries_3074_, v_a_3075_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
lean_dec(v_a_3079_);
lean_dec_ref(v_a_3078_);
lean_dec(v_a_3077_);
lean_dec_ref(v_a_3076_);
lean_dec(v_a_3075_);
lean_dec_ref(v_entries_3074_);
return v_res_3081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries(lean_object* v_00_u03b1_3082_, lean_object* v_values_3083_, lean_object* v_starIdx_3084_, lean_object* v_children_3085_, lean_object* v_entries_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_){
_start:
{
lean_object* v___x_3093_; 
v___x_3093_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(v_values_3083_, v_starIdx_3084_, v_children_3085_, v_entries_3086_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_);
return v___x_3093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries___boxed(lean_object* v_00_u03b1_3094_, lean_object* v_values_3095_, lean_object* v_starIdx_3096_, lean_object* v_children_3097_, lean_object* v_entries_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_, lean_object* v_a_3102_, lean_object* v_a_3103_, lean_object* v_a_3104_){
_start:
{
lean_object* v_res_3105_; 
v_res_3105_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries(v_00_u03b1_3094_, v_values_3095_, v_starIdx_3096_, v_children_3097_, v_entries_3098_, v_a_3099_, v_a_3100_, v_a_3101_, v_a_3102_, v_a_3103_);
lean_dec(v_a_3103_);
lean_dec_ref(v_a_3102_);
lean_dec(v_a_3101_);
lean_dec_ref(v_a_3100_);
lean_dec(v_a_3099_);
lean_dec_ref(v_entries_3098_);
return v_res_3105_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0(lean_object* v_00_u03b1_3106_, lean_object* v_as_3107_, size_t v_i_3108_, size_t v_stop_3109_, lean_object* v_b_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_){
_start:
{
lean_object* v___x_3117_; 
v___x_3117_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_as_3107_, v_i_3108_, v_stop_3109_, v_b_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_);
return v___x_3117_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___boxed(lean_object* v_00_u03b1_3118_, lean_object* v_as_3119_, lean_object* v_i_3120_, lean_object* v_stop_3121_, lean_object* v_b_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_){
_start:
{
size_t v_i_boxed_3129_; size_t v_stop_boxed_3130_; lean_object* v_res_3131_; 
v_i_boxed_3129_ = lean_unbox_usize(v_i_3120_);
lean_dec(v_i_3120_);
v_stop_boxed_3130_ = lean_unbox_usize(v_stop_3121_);
lean_dec(v_stop_3121_);
v_res_3131_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0(v_00_u03b1_3118_, v_as_3119_, v_i_boxed_3129_, v_stop_boxed_3130_, v_b_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_);
lean_dec(v___y_3127_);
lean_dec_ref(v___y_3126_);
lean_dec(v___y_3125_);
lean_dec_ref(v___y_3124_);
lean_dec(v___y_3123_);
lean_dec_ref(v_as_3119_);
return v_res_3131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode___redArg(lean_object* v_c_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_){
_start:
{
lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v_values_3142_; lean_object* v_star_3143_; lean_object* v_children_3144_; lean_object* v_pending_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3175_; 
v___x_3139_ = lean_st_ref_get(v_a_3133_);
v___x_3140_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0);
v___x_3141_ = lean_array_get(v___x_3140_, v___x_3139_, v_c_3132_);
lean_dec(v___x_3139_);
v_values_3142_ = lean_ctor_get(v___x_3141_, 0);
v_star_3143_ = lean_ctor_get(v___x_3141_, 1);
v_children_3144_ = lean_ctor_get(v___x_3141_, 2);
v_pending_3145_ = lean_ctor_get(v___x_3141_, 3);
v_isSharedCheck_3175_ = !lean_is_exclusive(v___x_3141_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_3147_ = v___x_3141_;
v_isShared_3148_ = v_isSharedCheck_3175_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_pending_3145_);
lean_inc(v_children_3144_);
lean_inc(v_star_3143_);
lean_inc(v_values_3142_);
lean_dec(v___x_3141_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3175_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
lean_object* v___x_3149_; lean_object* v___x_3150_; uint8_t v___x_3151_; 
v___x_3149_ = lean_array_get_size(v_pending_3145_);
v___x_3150_ = lean_unsigned_to_nat(0u);
v___x_3151_ = lean_nat_dec_eq(v___x_3149_, v___x_3150_);
if (v___x_3151_ == 0)
{
lean_object* v___x_3152_; lean_object* v___x_3153_; 
v___x_3152_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_c_3132_, v___x_3140_, v_a_3133_);
lean_dec_ref(v___x_3152_);
v___x_3153_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(v_values_3142_, v_star_3143_, v_children_3144_, v_pending_3145_, v_a_3133_, v_a_3134_, v_a_3135_, v_a_3136_, v_a_3137_);
lean_dec_ref(v_pending_3145_);
if (lean_obj_tag(v___x_3153_) == 0)
{
lean_object* v_a_3154_; lean_object* v_snd_3155_; lean_object* v_fst_3156_; lean_object* v_fst_3157_; lean_object* v_snd_3158_; lean_object* v___x_3159_; lean_object* v___x_3161_; 
v_a_3154_ = lean_ctor_get(v___x_3153_, 0);
lean_inc(v_a_3154_);
lean_dec_ref_known(v___x_3153_, 1);
v_snd_3155_ = lean_ctor_get(v_a_3154_, 1);
v_fst_3156_ = lean_ctor_get(v_a_3154_, 0);
v_fst_3157_ = lean_ctor_get(v_snd_3155_, 0);
v_snd_3158_ = lean_ctor_get(v_snd_3155_, 1);
v___x_3159_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__3));
lean_inc(v_snd_3158_);
lean_inc(v_fst_3157_);
lean_inc(v_fst_3156_);
if (v_isShared_3148_ == 0)
{
lean_ctor_set(v___x_3147_, 3, v___x_3159_);
lean_ctor_set(v___x_3147_, 2, v_snd_3158_);
lean_ctor_set(v___x_3147_, 1, v_fst_3157_);
lean_ctor_set(v___x_3147_, 0, v_fst_3156_);
v___x_3161_ = v___x_3147_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v_fst_3156_);
lean_ctor_set(v_reuseFailAlloc_3171_, 1, v_fst_3157_);
lean_ctor_set(v_reuseFailAlloc_3171_, 2, v_snd_3158_);
lean_ctor_set(v_reuseFailAlloc_3171_, 3, v___x_3159_);
v___x_3161_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
lean_object* v___x_3162_; lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3169_; 
v___x_3162_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_c_3132_, v___x_3161_, v_a_3133_);
v_isSharedCheck_3169_ = !lean_is_exclusive(v___x_3162_);
if (v_isSharedCheck_3169_ == 0)
{
lean_object* v_unused_3170_; 
v_unused_3170_ = lean_ctor_get(v___x_3162_, 0);
lean_dec(v_unused_3170_);
v___x_3164_ = v___x_3162_;
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
else
{
lean_dec(v___x_3162_);
v___x_3164_ = lean_box(0);
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
v_resetjp_3163_:
{
lean_object* v___x_3167_; 
if (v_isShared_3165_ == 0)
{
lean_ctor_set(v___x_3164_, 0, v_a_3154_);
v___x_3167_ = v___x_3164_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v_a_3154_);
v___x_3167_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
return v___x_3167_;
}
}
}
}
else
{
lean_del_object(v___x_3147_);
return v___x_3153_;
}
}
else
{
lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; 
lean_del_object(v___x_3147_);
lean_dec_ref(v_pending_3145_);
v___x_3172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3172_, 0, v_star_3143_);
lean_ctor_set(v___x_3172_, 1, v_children_3144_);
v___x_3173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3173_, 0, v_values_3142_);
lean_ctor_set(v___x_3173_, 1, v___x_3172_);
v___x_3174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3174_, 0, v___x_3173_);
return v___x_3174_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode___redArg___boxed(lean_object* v_c_3176_, lean_object* v_a_3177_, lean_object* v_a_3178_, lean_object* v_a_3179_, lean_object* v_a_3180_, lean_object* v_a_3181_, lean_object* v_a_3182_){
_start:
{
lean_object* v_res_3183_; 
v_res_3183_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_c_3176_, v_a_3177_, v_a_3178_, v_a_3179_, v_a_3180_, v_a_3181_);
lean_dec(v_a_3181_);
lean_dec_ref(v_a_3180_);
lean_dec(v_a_3179_);
lean_dec_ref(v_a_3178_);
lean_dec(v_a_3177_);
lean_dec(v_c_3176_);
return v_res_3183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode(lean_object* v_00_u03b1_3184_, lean_object* v_c_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_){
_start:
{
lean_object* v___x_3192_; 
v___x_3192_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_c_3185_, v_a_3186_, v_a_3187_, v_a_3188_, v_a_3189_, v_a_3190_);
return v___x_3192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode___boxed(lean_object* v_00_u03b1_3193_, lean_object* v_c_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_, lean_object* v_a_3200_){
_start:
{
lean_object* v_res_3201_; 
v_res_3201_ = l_Lean_Meta_LazyDiscrTree_evalNode(v_00_u03b1_3193_, v_c_3194_, v_a_3195_, v_a_3196_, v_a_3197_, v_a_3198_, v_a_3199_);
lean_dec(v_a_3199_);
lean_dec_ref(v_a_3198_);
lean_dec(v_a_3197_);
lean_dec_ref(v_a_3196_);
lean_dec(v_a_3195_);
lean_dec(v_c_3194_);
return v_res_3201_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(lean_object* v_a_3202_, lean_object* v_fallback_3203_, lean_object* v_x_3204_){
_start:
{
if (lean_obj_tag(v_x_3204_) == 0)
{
lean_inc(v_fallback_3203_);
return v_fallback_3203_;
}
else
{
lean_object* v_key_3205_; lean_object* v_value_3206_; lean_object* v_tail_3207_; uint8_t v___x_3208_; 
v_key_3205_ = lean_ctor_get(v_x_3204_, 0);
v_value_3206_ = lean_ctor_get(v_x_3204_, 1);
v_tail_3207_ = lean_ctor_get(v_x_3204_, 2);
v___x_3208_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_3205_, v_a_3202_);
if (v___x_3208_ == 0)
{
v_x_3204_ = v_tail_3207_;
goto _start;
}
else
{
lean_inc(v_value_3206_);
return v_value_3206_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg___boxed(lean_object* v_a_3210_, lean_object* v_fallback_3211_, lean_object* v_x_3212_){
_start:
{
lean_object* v_res_3213_; 
v_res_3213_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(v_a_3210_, v_fallback_3211_, v_x_3212_);
lean_dec(v_x_3212_);
lean_dec(v_fallback_3211_);
lean_dec(v_a_3210_);
return v_res_3213_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(lean_object* v_m_3214_, lean_object* v_a_3215_, lean_object* v_fallback_3216_){
_start:
{
lean_object* v_buckets_3217_; lean_object* v___x_3218_; uint64_t v___x_3219_; uint64_t v___x_3220_; uint64_t v___x_3221_; uint64_t v_fold_3222_; uint64_t v___x_3223_; uint64_t v___x_3224_; uint64_t v___x_3225_; size_t v___x_3226_; size_t v___x_3227_; size_t v___x_3228_; size_t v___x_3229_; size_t v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; 
v_buckets_3217_ = lean_ctor_get(v_m_3214_, 1);
v___x_3218_ = lean_array_get_size(v_buckets_3217_);
v___x_3219_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_a_3215_);
v___x_3220_ = 32ULL;
v___x_3221_ = lean_uint64_shift_right(v___x_3219_, v___x_3220_);
v_fold_3222_ = lean_uint64_xor(v___x_3219_, v___x_3221_);
v___x_3223_ = 16ULL;
v___x_3224_ = lean_uint64_shift_right(v_fold_3222_, v___x_3223_);
v___x_3225_ = lean_uint64_xor(v_fold_3222_, v___x_3224_);
v___x_3226_ = lean_uint64_to_usize(v___x_3225_);
v___x_3227_ = lean_usize_of_nat(v___x_3218_);
v___x_3228_ = ((size_t)1ULL);
v___x_3229_ = lean_usize_sub(v___x_3227_, v___x_3228_);
v___x_3230_ = lean_usize_land(v___x_3226_, v___x_3229_);
v___x_3231_ = lean_array_uget_borrowed(v_buckets_3217_, v___x_3230_);
v___x_3232_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(v_a_3215_, v_fallback_3216_, v___x_3231_);
return v___x_3232_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg___boxed(lean_object* v_m_3233_, lean_object* v_a_3234_, lean_object* v_fallback_3235_){
_start:
{
lean_object* v_res_3236_; 
v_res_3236_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_m_3233_, v_a_3234_, v_fallback_3235_);
lean_dec(v_fallback_3235_);
lean_dec(v_a_3234_);
lean_dec_ref(v_m_3233_);
return v_res_3236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg(lean_object* v_next_3237_, lean_object* v_rest_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_, lean_object* v_a_3241_, lean_object* v_a_3242_, lean_object* v_a_3243_){
_start:
{
lean_object* v___x_3245_; uint8_t v___x_3246_; 
v___x_3245_ = lean_unsigned_to_nat(0u);
v___x_3246_ = lean_nat_dec_eq(v_next_3237_, v___x_3245_);
if (v___x_3246_ == 0)
{
lean_object* v___x_3247_; 
v___x_3247_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_next_3237_, v_a_3239_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_);
if (lean_obj_tag(v___x_3247_) == 0)
{
lean_object* v_a_3248_; lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3273_; 
v_a_3248_ = lean_ctor_get(v___x_3247_, 0);
v_isSharedCheck_3273_ = !lean_is_exclusive(v___x_3247_);
if (v_isSharedCheck_3273_ == 0)
{
v___x_3250_ = v___x_3247_;
v_isShared_3251_ = v_isSharedCheck_3273_;
goto v_resetjp_3249_;
}
else
{
lean_inc(v_a_3248_);
lean_dec(v___x_3247_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3273_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
lean_object* v_snd_3252_; 
v_snd_3252_ = lean_ctor_get(v_a_3248_, 1);
lean_inc(v_snd_3252_);
lean_dec(v_a_3248_);
if (lean_obj_tag(v_rest_3238_) == 0)
{
lean_object* v_fst_3253_; lean_object* v_snd_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3262_; 
v_fst_3253_ = lean_ctor_get(v_snd_3252_, 0);
lean_inc(v_fst_3253_);
v_snd_3254_ = lean_ctor_get(v_snd_3252_, 1);
lean_inc(v_snd_3254_);
lean_dec(v_snd_3252_);
v___x_3255_ = lean_st_ref_take(v_a_3239_);
v___x_3256_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_3257_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3257_, 0, v___x_3256_);
lean_ctor_set(v___x_3257_, 1, v_fst_3253_);
lean_ctor_set(v___x_3257_, 2, v_snd_3254_);
lean_ctor_set(v___x_3257_, 3, v___x_3256_);
v___x_3258_ = lean_array_set(v___x_3255_, v_next_3237_, v___x_3257_);
lean_dec(v_next_3237_);
v___x_3259_ = lean_st_ref_put(v_a_3239_, v___x_3258_);
v___x_3260_ = lean_box(0);
if (v_isShared_3251_ == 0)
{
lean_ctor_set(v___x_3250_, 0, v___x_3260_);
v___x_3262_ = v___x_3250_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v___x_3260_);
v___x_3262_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
return v___x_3262_;
}
}
else
{
lean_object* v_fst_3264_; lean_object* v_snd_3265_; lean_object* v_head_3266_; lean_object* v_tail_3267_; lean_object* v___x_3268_; uint8_t v___x_3269_; 
lean_del_object(v___x_3250_);
lean_dec(v_next_3237_);
v_fst_3264_ = lean_ctor_get(v_snd_3252_, 0);
lean_inc(v_fst_3264_);
v_snd_3265_ = lean_ctor_get(v_snd_3252_, 1);
lean_inc(v_snd_3265_);
lean_dec(v_snd_3252_);
v_head_3266_ = lean_ctor_get(v_rest_3238_, 0);
v_tail_3267_ = lean_ctor_get(v_rest_3238_, 1);
v___x_3268_ = lean_box(3);
v___x_3269_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_head_3266_, v___x_3268_);
if (v___x_3269_ == 0)
{
lean_object* v___x_3270_; 
lean_dec(v_fst_3264_);
v___x_3270_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_snd_3265_, v_head_3266_, v___x_3245_);
lean_dec(v_snd_3265_);
v_next_3237_ = v___x_3270_;
v_rest_3238_ = v_tail_3267_;
goto _start;
}
else
{
lean_dec(v_snd_3265_);
v_next_3237_ = v_fst_3264_;
v_rest_3238_ = v_tail_3267_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3274_; lean_object* v___x_3276_; uint8_t v_isShared_3277_; uint8_t v_isSharedCheck_3281_; 
lean_dec(v_next_3237_);
v_a_3274_ = lean_ctor_get(v___x_3247_, 0);
v_isSharedCheck_3281_ = !lean_is_exclusive(v___x_3247_);
if (v_isSharedCheck_3281_ == 0)
{
v___x_3276_ = v___x_3247_;
v_isShared_3277_ = v_isSharedCheck_3281_;
goto v_resetjp_3275_;
}
else
{
lean_inc(v_a_3274_);
lean_dec(v___x_3247_);
v___x_3276_ = lean_box(0);
v_isShared_3277_ = v_isSharedCheck_3281_;
goto v_resetjp_3275_;
}
v_resetjp_3275_:
{
lean_object* v___x_3279_; 
if (v_isShared_3277_ == 0)
{
v___x_3279_ = v___x_3276_;
goto v_reusejp_3278_;
}
else
{
lean_object* v_reuseFailAlloc_3280_; 
v_reuseFailAlloc_3280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3280_, 0, v_a_3274_);
v___x_3279_ = v_reuseFailAlloc_3280_;
goto v_reusejp_3278_;
}
v_reusejp_3278_:
{
return v___x_3279_;
}
}
}
}
else
{
lean_object* v___x_3282_; lean_object* v___x_3283_; 
lean_dec(v_next_3237_);
v___x_3282_ = lean_box(0);
v___x_3283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3283_, 0, v___x_3282_);
return v___x_3283_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg___boxed(lean_object* v_next_3284_, lean_object* v_rest_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_, lean_object* v_a_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_){
_start:
{
lean_object* v_res_3292_; 
v_res_3292_ = l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg(v_next_3284_, v_rest_3285_, v_a_3286_, v_a_3287_, v_a_3288_, v_a_3289_, v_a_3290_);
lean_dec(v_a_3290_);
lean_dec_ref(v_a_3289_);
lean_dec(v_a_3288_);
lean_dec_ref(v_a_3287_);
lean_dec(v_a_3286_);
lean_dec(v_rest_3285_);
return v_res_3292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux(lean_object* v_00_u03b1_3293_, lean_object* v_next_3294_, lean_object* v_rest_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_){
_start:
{
lean_object* v___x_3302_; 
v___x_3302_ = l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg(v_next_3294_, v_rest_3295_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_, v_a_3300_);
return v___x_3302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux___boxed(lean_object* v_00_u03b1_3303_, lean_object* v_next_3304_, lean_object* v_rest_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_, lean_object* v_a_3311_){
_start:
{
lean_object* v_res_3312_; 
v_res_3312_ = l_Lean_Meta_LazyDiscrTree_dropKeyAux(v_00_u03b1_3303_, v_next_3304_, v_rest_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_);
lean_dec(v_a_3310_);
lean_dec_ref(v_a_3309_);
lean_dec(v_a_3308_);
lean_dec_ref(v_a_3307_);
lean_dec(v_a_3306_);
lean_dec(v_rest_3305_);
return v_res_3312_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0(lean_object* v_00_u03b2_3313_, lean_object* v_m_3314_, lean_object* v_a_3315_, lean_object* v_fallback_3316_){
_start:
{
lean_object* v___x_3317_; 
v___x_3317_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_m_3314_, v_a_3315_, v_fallback_3316_);
return v___x_3317_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___boxed(lean_object* v_00_u03b2_3318_, lean_object* v_m_3319_, lean_object* v_a_3320_, lean_object* v_fallback_3321_){
_start:
{
lean_object* v_res_3322_; 
v_res_3322_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0(v_00_u03b2_3318_, v_m_3319_, v_a_3320_, v_fallback_3321_);
lean_dec(v_fallback_3321_);
lean_dec(v_a_3320_);
lean_dec_ref(v_m_3319_);
return v_res_3322_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0(lean_object* v_00_u03b2_3323_, lean_object* v_a_3324_, lean_object* v_fallback_3325_, lean_object* v_x_3326_){
_start:
{
lean_object* v___x_3327_; 
v___x_3327_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(v_a_3324_, v_fallback_3325_, v_x_3326_);
return v___x_3327_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3328_, lean_object* v_a_3329_, lean_object* v_fallback_3330_, lean_object* v_x_3331_){
_start:
{
lean_object* v_res_3332_; 
v_res_3332_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0(v_00_u03b2_3328_, v_a_3329_, v_fallback_3330_, v_x_3331_);
lean_dec(v_x_3331_);
lean_dec(v_fallback_3330_);
lean_dec(v_a_3329_);
return v_res_3332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey___redArg(lean_object* v_t_3333_, lean_object* v_path_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_){
_start:
{
if (lean_obj_tag(v_path_3334_) == 0)
{
lean_object* v___x_3340_; 
v___x_3340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3340_, 0, v_t_3333_);
return v___x_3340_;
}
else
{
lean_object* v_head_3341_; lean_object* v_tail_3342_; lean_object* v_roots_3343_; lean_object* v___x_3344_; lean_object* v_idx_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; 
v_head_3341_ = lean_ctor_get(v_path_3334_, 0);
lean_inc(v_head_3341_);
v_tail_3342_ = lean_ctor_get(v_path_3334_, 1);
lean_inc(v_tail_3342_);
lean_dec_ref_known(v_path_3334_, 2);
v_roots_3343_ = lean_ctor_get(v_t_3333_, 1);
v___x_3344_ = lean_unsigned_to_nat(0u);
v_idx_3345_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_roots_3343_, v_head_3341_, v___x_3344_);
lean_dec(v_head_3341_);
v___x_3346_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_dropKeyAux___boxed), 9, 3);
lean_closure_set(v___x_3346_, 0, lean_box(0));
lean_closure_set(v___x_3346_, 1, v_idx_3345_);
lean_closure_set(v___x_3346_, 2, v_tail_3342_);
v___x_3347_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_t_3333_, v___x_3346_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_);
if (lean_obj_tag(v___x_3347_) == 0)
{
lean_object* v_a_3348_; lean_object* v___x_3350_; uint8_t v_isShared_3351_; uint8_t v_isSharedCheck_3356_; 
v_a_3348_ = lean_ctor_get(v___x_3347_, 0);
v_isSharedCheck_3356_ = !lean_is_exclusive(v___x_3347_);
if (v_isSharedCheck_3356_ == 0)
{
v___x_3350_ = v___x_3347_;
v_isShared_3351_ = v_isSharedCheck_3356_;
goto v_resetjp_3349_;
}
else
{
lean_inc(v_a_3348_);
lean_dec(v___x_3347_);
v___x_3350_ = lean_box(0);
v_isShared_3351_ = v_isSharedCheck_3356_;
goto v_resetjp_3349_;
}
v_resetjp_3349_:
{
lean_object* v_snd_3352_; lean_object* v___x_3354_; 
v_snd_3352_ = lean_ctor_get(v_a_3348_, 1);
lean_inc(v_snd_3352_);
lean_dec(v_a_3348_);
if (v_isShared_3351_ == 0)
{
lean_ctor_set(v___x_3350_, 0, v_snd_3352_);
v___x_3354_ = v___x_3350_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v_snd_3352_);
v___x_3354_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
return v___x_3354_;
}
}
}
else
{
lean_object* v_a_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3364_; 
v_a_3357_ = lean_ctor_get(v___x_3347_, 0);
v_isSharedCheck_3364_ = !lean_is_exclusive(v___x_3347_);
if (v_isSharedCheck_3364_ == 0)
{
v___x_3359_ = v___x_3347_;
v_isShared_3360_ = v_isSharedCheck_3364_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_a_3357_);
lean_dec(v___x_3347_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3364_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
lean_object* v___x_3362_; 
if (v_isShared_3360_ == 0)
{
v___x_3362_ = v___x_3359_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v_a_3357_);
v___x_3362_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
return v___x_3362_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey___redArg___boxed(lean_object* v_t_3365_, lean_object* v_path_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_){
_start:
{
lean_object* v_res_3372_; 
v_res_3372_ = l_Lean_Meta_LazyDiscrTree_dropKey___redArg(v_t_3365_, v_path_3366_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_);
lean_dec(v_a_3370_);
lean_dec_ref(v_a_3369_);
lean_dec(v_a_3368_);
lean_dec_ref(v_a_3367_);
return v_res_3372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey(lean_object* v_00_u03b1_3373_, lean_object* v_t_3374_, lean_object* v_path_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_){
_start:
{
lean_object* v___x_3381_; 
v___x_3381_ = l_Lean_Meta_LazyDiscrTree_dropKey___redArg(v_t_3374_, v_path_3375_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_);
return v___x_3381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey___boxed(lean_object* v_00_u03b1_3382_, lean_object* v_t_3383_, lean_object* v_path_3384_, lean_object* v_a_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_){
_start:
{
lean_object* v_res_3390_; 
v_res_3390_ = l_Lean_Meta_LazyDiscrTree_dropKey(v_00_u03b1_3382_, v_t_3383_, v_path_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
lean_dec(v_a_3388_);
lean_dec_ref(v_a_3387_);
lean_dec(v_a_3386_);
lean_dec_ref(v_a_3385_);
return v_res_3390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(lean_object* v_score_3393_, lean_object* v_e_3394_, lean_object* v_a_3395_){
_start:
{
lean_object* v___x_3396_; uint8_t v___x_3397_; 
v___x_3396_ = lean_array_get_size(v_a_3395_);
v___x_3397_ = lean_nat_dec_lt(v___x_3396_, v_score_3393_);
if (v___x_3397_ == 0)
{
lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; 
v___x_3398_ = lean_unsigned_to_nat(1u);
v___x_3399_ = lean_mk_empty_array_with_capacity(v___x_3398_);
v___x_3400_ = lean_array_push(v___x_3399_, v_e_3394_);
v___x_3401_ = lean_array_push(v_a_3395_, v___x_3400_);
return v___x_3401_;
}
else
{
lean_object* v___x_3402_; lean_object* v___x_3403_; 
v___x_3402_ = ((lean_object*)(l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg___closed__0));
v___x_3403_ = lean_array_push(v_a_3395_, v___x_3402_);
v_a_3395_ = v___x_3403_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg___boxed(lean_object* v_score_3405_, lean_object* v_e_3406_, lean_object* v_a_3407_){
_start:
{
lean_object* v_res_3408_; 
v_res_3408_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(v_score_3405_, v_e_3406_, v_a_3407_);
lean_dec(v_score_3405_);
return v_res_3408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop(lean_object* v_00_u03b1_3409_, lean_object* v_score_3410_, lean_object* v_e_3411_, lean_object* v_a_3412_){
_start:
{
lean_object* v___x_3413_; 
v___x_3413_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(v_score_3410_, v_e_3411_, v_a_3412_);
return v___x_3413_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___boxed(lean_object* v_00_u03b1_3414_, lean_object* v_score_3415_, lean_object* v_e_3416_, lean_object* v_a_3417_){
_start:
{
lean_object* v_res_3418_; 
v_res_3418_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop(v_00_u03b1_3414_, v_score_3415_, v_e_3416_, v_a_3417_);
lean_dec(v_score_3415_);
return v_res_3418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(lean_object* v_r_3419_, lean_object* v_score_3420_, lean_object* v_e_3421_){
_start:
{
lean_object* v___x_3422_; lean_object* v___x_3423_; uint8_t v___x_3424_; 
v___x_3422_ = lean_array_get_size(v_e_3421_);
v___x_3423_ = lean_unsigned_to_nat(0u);
v___x_3424_ = lean_nat_dec_eq(v___x_3422_, v___x_3423_);
if (v___x_3424_ == 0)
{
lean_object* v___x_3425_; uint8_t v___x_3426_; 
v___x_3425_ = lean_array_get_size(v_r_3419_);
v___x_3426_ = lean_nat_dec_lt(v_score_3420_, v___x_3425_);
if (v___x_3426_ == 0)
{
lean_object* v___x_3427_; 
v___x_3427_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(v_score_3420_, v_e_3421_, v_r_3419_);
return v___x_3427_;
}
else
{
if (v___x_3426_ == 0)
{
lean_dec_ref(v_e_3421_);
return v_r_3419_;
}
else
{
lean_object* v_v_3428_; lean_object* v___x_3429_; lean_object* v_xs_x27_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; 
v_v_3428_ = lean_array_fget(v_r_3419_, v_score_3420_);
v___x_3429_ = lean_box(0);
v_xs_x27_3430_ = lean_array_fset(v_r_3419_, v_score_3420_, v___x_3429_);
v___x_3431_ = lean_array_push(v_v_3428_, v_e_3421_);
v___x_3432_ = lean_array_fset(v_xs_x27_3430_, v_score_3420_, v___x_3431_);
return v___x_3432_;
}
}
}
else
{
lean_dec_ref(v_e_3421_);
return v_r_3419_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg___boxed(lean_object* v_r_3433_, lean_object* v_score_3434_, lean_object* v_e_3435_){
_start:
{
lean_object* v_res_3436_; 
v_res_3436_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v_r_3433_, v_score_3434_, v_e_3435_);
lean_dec(v_score_3434_);
return v_res_3436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push(lean_object* v_00_u03b1_3437_, lean_object* v_r_3438_, lean_object* v_score_3439_, lean_object* v_e_3440_){
_start:
{
lean_object* v___x_3441_; 
v___x_3441_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v_r_3438_, v_score_3439_, v_e_3440_);
return v___x_3441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push___boxed(lean_object* v_00_u03b1_3442_, lean_object* v_r_3443_, lean_object* v_score_3444_, lean_object* v_e_3445_){
_start:
{
lean_object* v_res_3446_; 
v_res_3446_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push(v_00_u03b1_3442_, v_r_3443_, v_score_3444_, v_e_3445_);
lean_dec(v_score_3444_);
return v_res_3446_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(lean_object* v_as_3447_, size_t v_i_3448_, size_t v_stop_3449_, lean_object* v_b_3450_){
_start:
{
uint8_t v___x_3451_; 
v___x_3451_ = lean_usize_dec_eq(v_i_3448_, v_stop_3449_);
if (v___x_3451_ == 0)
{
lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; size_t v___x_3455_; size_t v___x_3456_; 
v___x_3452_ = lean_array_uget_borrowed(v_as_3447_, v_i_3448_);
v___x_3453_ = lean_array_get_size(v___x_3452_);
v___x_3454_ = lean_nat_add(v_b_3450_, v___x_3453_);
lean_dec(v_b_3450_);
v___x_3455_ = ((size_t)1ULL);
v___x_3456_ = lean_usize_add(v_i_3448_, v___x_3455_);
v_i_3448_ = v___x_3456_;
v_b_3450_ = v___x_3454_;
goto _start;
}
else
{
return v_b_3450_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg___boxed(lean_object* v_as_3458_, lean_object* v_i_3459_, lean_object* v_stop_3460_, lean_object* v_b_3461_){
_start:
{
size_t v_i_boxed_3462_; size_t v_stop_boxed_3463_; lean_object* v_res_3464_; 
v_i_boxed_3462_ = lean_unbox_usize(v_i_3459_);
lean_dec(v_i_3459_);
v_stop_boxed_3463_ = lean_unbox_usize(v_stop_3460_);
lean_dec(v_stop_3460_);
v_res_3464_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v_as_3458_, v_i_boxed_3462_, v_stop_boxed_3463_, v_b_3461_);
lean_dec_ref(v_as_3458_);
return v_res_3464_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(lean_object* v_as_3465_, size_t v_i_3466_, size_t v_stop_3467_, lean_object* v_b_3468_){
_start:
{
lean_object* v___y_3470_; uint8_t v___x_3474_; 
v___x_3474_ = lean_usize_dec_eq(v_i_3466_, v_stop_3467_);
if (v___x_3474_ == 0)
{
lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; uint8_t v___x_3478_; 
v___x_3475_ = lean_array_uget_borrowed(v_as_3465_, v_i_3466_);
v___x_3476_ = lean_unsigned_to_nat(0u);
v___x_3477_ = lean_array_get_size(v___x_3475_);
v___x_3478_ = lean_nat_dec_lt(v___x_3476_, v___x_3477_);
if (v___x_3478_ == 0)
{
v___y_3470_ = v_b_3468_;
goto v___jp_3469_;
}
else
{
uint8_t v___x_3479_; 
v___x_3479_ = lean_nat_dec_le(v___x_3477_, v___x_3477_);
if (v___x_3479_ == 0)
{
if (v___x_3478_ == 0)
{
v___y_3470_ = v_b_3468_;
goto v___jp_3469_;
}
else
{
size_t v___x_3480_; size_t v___x_3481_; lean_object* v___x_3482_; 
v___x_3480_ = ((size_t)0ULL);
v___x_3481_ = lean_usize_of_nat(v___x_3477_);
v___x_3482_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v___x_3475_, v___x_3480_, v___x_3481_, v_b_3468_);
v___y_3470_ = v___x_3482_;
goto v___jp_3469_;
}
}
else
{
size_t v___x_3483_; size_t v___x_3484_; lean_object* v___x_3485_; 
v___x_3483_ = ((size_t)0ULL);
v___x_3484_ = lean_usize_of_nat(v___x_3477_);
v___x_3485_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v___x_3475_, v___x_3483_, v___x_3484_, v_b_3468_);
v___y_3470_ = v___x_3485_;
goto v___jp_3469_;
}
}
}
else
{
return v_b_3468_;
}
v___jp_3469_:
{
size_t v___x_3471_; size_t v___x_3472_; 
v___x_3471_ = ((size_t)1ULL);
v___x_3472_ = lean_usize_add(v_i_3466_, v___x_3471_);
v_i_3466_ = v___x_3472_;
v_b_3468_ = v___y_3470_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg___boxed(lean_object* v_as_3486_, lean_object* v_i_3487_, lean_object* v_stop_3488_, lean_object* v_b_3489_){
_start:
{
size_t v_i_boxed_3490_; size_t v_stop_boxed_3491_; lean_object* v_res_3492_; 
v_i_boxed_3490_ = lean_unbox_usize(v_i_3487_);
lean_dec(v_i_3487_);
v_stop_boxed_3491_ = lean_unbox_usize(v_stop_3488_);
lean_dec(v_stop_3488_);
v_res_3492_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_as_3486_, v_i_boxed_3490_, v_stop_boxed_3491_, v_b_3489_);
lean_dec_ref(v_as_3486_);
return v_res_3492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(lean_object* v_mr_3493_){
_start:
{
lean_object* v___x_3494_; lean_object* v___x_3495_; uint8_t v___x_3496_; 
v___x_3494_ = lean_unsigned_to_nat(0u);
v___x_3495_ = lean_array_get_size(v_mr_3493_);
v___x_3496_ = lean_nat_dec_lt(v___x_3494_, v___x_3495_);
if (v___x_3496_ == 0)
{
return v___x_3494_;
}
else
{
uint8_t v___x_3497_; 
v___x_3497_ = lean_nat_dec_le(v___x_3495_, v___x_3495_);
if (v___x_3497_ == 0)
{
if (v___x_3496_ == 0)
{
return v___x_3494_;
}
else
{
size_t v___x_3498_; size_t v___x_3499_; lean_object* v___x_3500_; 
v___x_3498_ = ((size_t)0ULL);
v___x_3499_ = lean_usize_of_nat(v___x_3495_);
v___x_3500_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_mr_3493_, v___x_3498_, v___x_3499_, v___x_3494_);
return v___x_3500_;
}
}
else
{
size_t v___x_3501_; size_t v___x_3502_; lean_object* v___x_3503_; 
v___x_3501_ = ((size_t)0ULL);
v___x_3502_ = lean_usize_of_nat(v___x_3495_);
v___x_3503_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_mr_3493_, v___x_3501_, v___x_3502_, v___x_3494_);
return v___x_3503_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg___boxed(lean_object* v_mr_3504_){
_start:
{
lean_object* v_res_3505_; 
v_res_3505_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_mr_3504_);
lean_dec_ref(v_mr_3504_);
return v_res_3505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size(lean_object* v_00_u03b1_3506_, lean_object* v_mr_3507_){
_start:
{
lean_object* v___x_3508_; 
v___x_3508_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_mr_3507_);
return v___x_3508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size___boxed(lean_object* v_00_u03b1_3509_, lean_object* v_mr_3510_){
_start:
{
lean_object* v_res_3511_; 
v_res_3511_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size(v_00_u03b1_3509_, v_mr_3510_);
lean_dec_ref(v_mr_3510_);
return v_res_3511_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0(lean_object* v_00_u03b1_3512_, lean_object* v_as_3513_, size_t v_i_3514_, size_t v_stop_3515_, lean_object* v_b_3516_){
_start:
{
lean_object* v___x_3517_; 
v___x_3517_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v_as_3513_, v_i_3514_, v_stop_3515_, v_b_3516_);
return v___x_3517_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___boxed(lean_object* v_00_u03b1_3518_, lean_object* v_as_3519_, lean_object* v_i_3520_, lean_object* v_stop_3521_, lean_object* v_b_3522_){
_start:
{
size_t v_i_boxed_3523_; size_t v_stop_boxed_3524_; lean_object* v_res_3525_; 
v_i_boxed_3523_ = lean_unbox_usize(v_i_3520_);
lean_dec(v_i_3520_);
v_stop_boxed_3524_ = lean_unbox_usize(v_stop_3521_);
lean_dec(v_stop_3521_);
v_res_3525_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0(v_00_u03b1_3518_, v_as_3519_, v_i_boxed_3523_, v_stop_boxed_3524_, v_b_3522_);
lean_dec_ref(v_as_3519_);
return v_res_3525_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1(lean_object* v_00_u03b1_3526_, lean_object* v_as_3527_, size_t v_i_3528_, size_t v_stop_3529_, lean_object* v_b_3530_){
_start:
{
lean_object* v___x_3531_; 
v___x_3531_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_as_3527_, v_i_3528_, v_stop_3529_, v_b_3530_);
return v___x_3531_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___boxed(lean_object* v_00_u03b1_3532_, lean_object* v_as_3533_, lean_object* v_i_3534_, lean_object* v_stop_3535_, lean_object* v_b_3536_){
_start:
{
size_t v_i_boxed_3537_; size_t v_stop_boxed_3538_; lean_object* v_res_3539_; 
v_i_boxed_3537_ = lean_unbox_usize(v_i_3534_);
lean_dec(v_i_3534_);
v_stop_boxed_3538_ = lean_unbox_usize(v_stop_3535_);
lean_dec(v_stop_3535_);
v_res_3539_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1(v_00_u03b1_3532_, v_as_3533_, v_i_boxed_3537_, v_stop_boxed_3538_, v_b_3536_);
lean_dec_ref(v_as_3533_);
return v_res_3539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__0(lean_object* v_f_3540_, lean_object* v_j_3541_, lean_object* v_x_3542_){
_start:
{
lean_object* v___x_3543_; 
v___x_3543_ = lean_apply_2(v_f_3540_, v_j_3541_, v_x_3542_);
return v___x_3543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1(lean_object* v___f_3563_, lean_object* v_x1_3564_, lean_object* v_x2_3565_){
_start:
{
lean_object* v___x_3566_; size_t v_sz_3567_; size_t v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; 
v___x_3566_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__9));
v_sz_3567_ = lean_array_size(v_x2_3565_);
v___x_3568_ = ((size_t)0ULL);
v___x_3569_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3566_, v___f_3563_, v_sz_3567_, v___x_3568_, v_x2_3565_);
v___x_3570_ = l_Array_append___redArg(v_x1_3564_, v___x_3569_);
lean_dec(v___x_3569_);
return v___x_3570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2(lean_object* v_n_3571_, lean_object* v_mr_3572_, lean_object* v_f_3573_, lean_object* v_i_3574_, lean_object* v_x_3575_, lean_object* v_r_3576_){
_start:
{
lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v_j_3579_; lean_object* v_b_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; uint8_t v___x_3584_; 
v___x_3577_ = lean_unsigned_to_nat(1u);
v___x_3578_ = lean_nat_sub(v_n_3571_, v___x_3577_);
v_j_3579_ = lean_nat_sub(v___x_3578_, v_i_3574_);
lean_dec(v___x_3578_);
v_b_3580_ = lean_array_fget_borrowed(v_mr_3572_, v_j_3579_);
v___x_3581_ = lean_unsigned_to_nat(0u);
v___x_3582_ = lean_array_get_size(v_b_3580_);
v___x_3583_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__9));
v___x_3584_ = lean_nat_dec_lt(v___x_3581_, v___x_3582_);
if (v___x_3584_ == 0)
{
lean_dec(v_j_3579_);
lean_dec(v_f_3573_);
return v_r_3576_;
}
else
{
lean_object* v___f_3585_; lean_object* v___f_3586_; uint8_t v___x_3587_; 
v___f_3585_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3585_, 0, v_f_3573_);
lean_closure_set(v___f_3585_, 1, v_j_3579_);
v___f_3586_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1), 3, 1);
lean_closure_set(v___f_3586_, 0, v___f_3585_);
v___x_3587_ = lean_nat_dec_le(v___x_3582_, v___x_3582_);
if (v___x_3587_ == 0)
{
if (v___x_3584_ == 0)
{
lean_dec_ref(v___f_3586_);
return v_r_3576_;
}
else
{
size_t v___x_3588_; size_t v___x_3589_; lean_object* v___x_3590_; 
v___x_3588_ = ((size_t)0ULL);
v___x_3589_ = lean_usize_of_nat(v___x_3582_);
lean_inc(v_b_3580_);
v___x_3590_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3583_, v___f_3586_, v_b_3580_, v___x_3588_, v___x_3589_, v_r_3576_);
return v___x_3590_;
}
}
else
{
size_t v___x_3591_; size_t v___x_3592_; lean_object* v___x_3593_; 
v___x_3591_ = ((size_t)0ULL);
v___x_3592_ = lean_usize_of_nat(v___x_3582_);
lean_inc(v_b_3580_);
v___x_3593_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3583_, v___f_3586_, v_b_3580_, v___x_3591_, v___x_3592_, v_r_3576_);
return v___x_3593_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2___boxed(lean_object* v_n_3594_, lean_object* v_mr_3595_, lean_object* v_f_3596_, lean_object* v_i_3597_, lean_object* v_x_3598_, lean_object* v_r_3599_){
_start:
{
lean_object* v_res_3600_; 
v_res_3600_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2(v_n_3594_, v_mr_3595_, v_f_3596_, v_i_3597_, v_x_3598_, v_r_3599_);
lean_dec(v_i_3597_);
lean_dec_ref(v_mr_3595_);
lean_dec(v_n_3594_);
return v_res_3600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg(lean_object* v_mr_3601_, lean_object* v_a_3602_, lean_object* v_f_3603_){
_start:
{
lean_object* v_n_3604_; lean_object* v___f_3605_; lean_object* v___x_3606_; 
v_n_3604_ = lean_array_get_size(v_mr_3601_);
v___f_3605_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_3605_, 0, v_n_3604_);
lean_closure_set(v___f_3605_, 1, v_mr_3601_);
lean_closure_set(v___f_3605_, 2, v_f_3603_);
v___x_3606_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop(lean_box(0), v_n_3604_, v___f_3605_, v_n_3604_, lean_box(0), v_a_3602_);
return v___x_3606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux(lean_object* v_00_u03b1_3607_, lean_object* v_00_u03b2_3608_, lean_object* v_mr_3609_, lean_object* v_a_3610_, lean_object* v_f_3611_){
_start:
{
lean_object* v___x_3612_; 
v___x_3612_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg(v_mr_3609_, v_a_3610_, v_f_3611_);
return v___x_3612_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(size_t v_sz_3613_, size_t v_i_3614_, lean_object* v_bs_3615_){
_start:
{
uint8_t v___x_3616_; 
v___x_3616_ = lean_usize_dec_lt(v_i_3614_, v_sz_3613_);
if (v___x_3616_ == 0)
{
return v_bs_3615_;
}
else
{
lean_object* v_v_3617_; lean_object* v___x_3618_; lean_object* v_bs_x27_3619_; size_t v___x_3620_; size_t v___x_3621_; lean_object* v___x_3622_; 
v_v_3617_ = lean_array_uget(v_bs_3615_, v_i_3614_);
v___x_3618_ = lean_unsigned_to_nat(0u);
v_bs_x27_3619_ = lean_array_uset(v_bs_3615_, v_i_3614_, v___x_3618_);
v___x_3620_ = ((size_t)1ULL);
v___x_3621_ = lean_usize_add(v_i_3614_, v___x_3620_);
v___x_3622_ = lean_array_uset(v_bs_x27_3619_, v_i_3614_, v_v_3617_);
v_i_3614_ = v___x_3621_;
v_bs_3615_ = v___x_3622_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg___boxed(lean_object* v_sz_3624_, lean_object* v_i_3625_, lean_object* v_bs_3626_){
_start:
{
size_t v_sz_boxed_3627_; size_t v_i_boxed_3628_; lean_object* v_res_3629_; 
v_sz_boxed_3627_ = lean_unbox_usize(v_sz_3624_);
lean_dec(v_sz_3624_);
v_i_boxed_3628_ = lean_unbox_usize(v_i_3625_);
lean_dec(v_i_3625_);
v_res_3629_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(v_sz_boxed_3627_, v_i_boxed_3628_, v_bs_3626_);
return v_res_3629_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(lean_object* v_as_3630_, size_t v_i_3631_, size_t v_stop_3632_, lean_object* v_b_3633_){
_start:
{
uint8_t v___x_3634_; 
v___x_3634_ = lean_usize_dec_eq(v_i_3631_, v_stop_3632_);
if (v___x_3634_ == 0)
{
lean_object* v___x_3635_; size_t v_sz_3636_; size_t v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; size_t v___x_3640_; size_t v___x_3641_; 
v___x_3635_ = lean_array_uget_borrowed(v_as_3630_, v_i_3631_);
v_sz_3636_ = lean_array_size(v___x_3635_);
v___x_3637_ = ((size_t)0ULL);
lean_inc(v___x_3635_);
v___x_3638_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(v_sz_3636_, v___x_3637_, v___x_3635_);
v___x_3639_ = l_Array_append___redArg(v_b_3633_, v___x_3638_);
lean_dec_ref(v___x_3638_);
v___x_3640_ = ((size_t)1ULL);
v___x_3641_ = lean_usize_add(v_i_3631_, v___x_3640_);
v_i_3631_ = v___x_3641_;
v_b_3633_ = v___x_3639_;
goto _start;
}
else
{
return v_b_3633_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg___boxed(lean_object* v_as_3643_, lean_object* v_i_3644_, lean_object* v_stop_3645_, lean_object* v_b_3646_){
_start:
{
size_t v_i_boxed_3647_; size_t v_stop_boxed_3648_; lean_object* v_res_3649_; 
v_i_boxed_3647_ = lean_unbox_usize(v_i_3644_);
lean_dec(v_i_3644_);
v_stop_boxed_3648_ = lean_unbox_usize(v_stop_3645_);
lean_dec(v_stop_3645_);
v_res_3649_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(v_as_3643_, v_i_boxed_3647_, v_stop_boxed_3648_, v_b_3646_);
lean_dec_ref(v_as_3643_);
return v_res_3649_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(lean_object* v_n_3650_, lean_object* v_aa_3651_, lean_object* v_n_3652_, lean_object* v_j_3653_, lean_object* v_a_3654_){
_start:
{
lean_object* v_zero_3655_; uint8_t v_isZero_3656_; 
v_zero_3655_ = lean_unsigned_to_nat(0u);
v_isZero_3656_ = lean_nat_dec_eq(v_j_3653_, v_zero_3655_);
if (v_isZero_3656_ == 1)
{
lean_dec(v_j_3653_);
return v_a_3654_;
}
else
{
lean_object* v_one_3657_; lean_object* v_n_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v_j_3661_; lean_object* v_b_3662_; lean_object* v___x_3663_; uint8_t v___x_3664_; 
v_one_3657_ = lean_unsigned_to_nat(1u);
v_n_3658_ = lean_nat_sub(v_j_3653_, v_one_3657_);
v___x_3659_ = lean_nat_sub(v_n_3652_, v_j_3653_);
lean_dec(v_j_3653_);
v___x_3660_ = lean_nat_sub(v_n_3650_, v_one_3657_);
v_j_3661_ = lean_nat_sub(v___x_3660_, v___x_3659_);
lean_dec(v___x_3659_);
lean_dec(v___x_3660_);
v_b_3662_ = lean_array_fget_borrowed(v_aa_3651_, v_j_3661_);
lean_dec(v_j_3661_);
v___x_3663_ = lean_array_get_size(v_b_3662_);
v___x_3664_ = lean_nat_dec_lt(v_zero_3655_, v___x_3663_);
if (v___x_3664_ == 0)
{
v_j_3653_ = v_n_3658_;
goto _start;
}
else
{
size_t v___x_3666_; size_t v___x_3667_; lean_object* v___x_3668_; 
v___x_3666_ = ((size_t)0ULL);
v___x_3667_ = lean_usize_of_nat(v___x_3663_);
v___x_3668_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(v_b_3662_, v___x_3666_, v___x_3667_, v_a_3654_);
v_j_3653_ = v_n_3658_;
v_a_3654_ = v___x_3668_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg___boxed(lean_object* v_n_3670_, lean_object* v_aa_3671_, lean_object* v_n_3672_, lean_object* v_j_3673_, lean_object* v_a_3674_){
_start:
{
lean_object* v_res_3675_; 
v_res_3675_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(v_n_3670_, v_aa_3671_, v_n_3672_, v_j_3673_, v_a_3674_);
lean_dec(v_n_3672_);
lean_dec_ref(v_aa_3671_);
lean_dec(v_n_3670_);
return v_res_3675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(lean_object* v_mr_3676_, lean_object* v_a_3677_){
_start:
{
lean_object* v_n_3678_; lean_object* v___x_3679_; 
v_n_3678_ = lean_array_get_size(v_mr_3676_);
v___x_3679_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(v_n_3678_, v_mr_3676_, v_n_3678_, v_n_3678_, v_a_3677_);
return v___x_3679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg___boxed(lean_object* v_mr_3680_, lean_object* v_a_3681_){
_start:
{
lean_object* v_res_3682_; 
v_res_3682_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3680_, v_a_3681_);
lean_dec_ref(v_mr_3680_);
return v_res_3682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___redArg(lean_object* v_mr_3683_, lean_object* v_a_3684_){
_start:
{
lean_object* v___x_3685_; 
v___x_3685_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3683_, v_a_3684_);
return v___x_3685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___redArg___boxed(lean_object* v_mr_3686_, lean_object* v_a_3687_){
_start:
{
lean_object* v_res_3688_; 
v_res_3688_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___redArg(v_mr_3686_, v_a_3687_);
lean_dec_ref(v_mr_3686_);
return v_res_3688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults(lean_object* v_00_u03b1_3689_, lean_object* v_mr_3690_, lean_object* v_a_3691_){
_start:
{
lean_object* v___x_3692_; 
v___x_3692_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3690_, v_a_3691_);
return v___x_3692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___boxed(lean_object* v_00_u03b1_3693_, lean_object* v_mr_3694_, lean_object* v_a_3695_){
_start:
{
lean_object* v_res_3696_; 
v_res_3696_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults(v_00_u03b1_3693_, v_mr_3694_, v_a_3695_);
lean_dec_ref(v_mr_3694_);
return v_res_3696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0(lean_object* v_00_u03b1_3697_, lean_object* v_mr_3698_, lean_object* v_a_3699_){
_start:
{
lean_object* v___x_3700_; 
v___x_3700_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3698_, v_a_3699_);
return v___x_3700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___boxed(lean_object* v_00_u03b1_3701_, lean_object* v_mr_3702_, lean_object* v_a_3703_){
_start:
{
lean_object* v_res_3704_; 
v_res_3704_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0(v_00_u03b1_3701_, v_mr_3702_, v_a_3703_);
lean_dec_ref(v_mr_3702_);
return v_res_3704_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0(lean_object* v_00_u03b1_3705_, size_t v_sz_3706_, size_t v_i_3707_, lean_object* v_bs_3708_){
_start:
{
lean_object* v___x_3709_; 
v___x_3709_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(v_sz_3706_, v_i_3707_, v_bs_3708_);
return v___x_3709_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3710_, lean_object* v_sz_3711_, lean_object* v_i_3712_, lean_object* v_bs_3713_){
_start:
{
size_t v_sz_boxed_3714_; size_t v_i_boxed_3715_; lean_object* v_res_3716_; 
v_sz_boxed_3714_ = lean_unbox_usize(v_sz_3711_);
lean_dec(v_sz_3711_);
v_i_boxed_3715_ = lean_unbox_usize(v_i_3712_);
lean_dec(v_i_3712_);
v_res_3716_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0(v_00_u03b1_3710_, v_sz_boxed_3714_, v_i_boxed_3715_, v_bs_3713_);
return v_res_3716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1(lean_object* v_00_u03b1_3717_, lean_object* v_as_3718_, size_t v_i_3719_, size_t v_stop_3720_, lean_object* v_b_3721_){
_start:
{
lean_object* v___x_3722_; 
v___x_3722_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(v_as_3718_, v_i_3719_, v_stop_3720_, v_b_3721_);
return v___x_3722_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3723_, lean_object* v_as_3724_, lean_object* v_i_3725_, lean_object* v_stop_3726_, lean_object* v_b_3727_){
_start:
{
size_t v_i_boxed_3728_; size_t v_stop_boxed_3729_; lean_object* v_res_3730_; 
v_i_boxed_3728_ = lean_unbox_usize(v_i_3725_);
lean_dec(v_i_3725_);
v_stop_boxed_3729_ = lean_unbox_usize(v_stop_3726_);
lean_dec(v_stop_3726_);
v_res_3730_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1(v_00_u03b1_3723_, v_as_3724_, v_i_boxed_3728_, v_stop_boxed_3729_, v_b_3727_);
lean_dec_ref(v_as_3724_);
return v_res_3730_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2(lean_object* v_00_u03b1_3731_, lean_object* v_n_3732_, lean_object* v_aa_3733_, lean_object* v_n_3734_, lean_object* v_j_3735_, lean_object* v_a_3736_, lean_object* v_a_3737_){
_start:
{
lean_object* v___x_3738_; 
v___x_3738_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(v_n_3732_, v_aa_3733_, v_n_3734_, v_j_3735_, v_a_3737_);
return v___x_3738_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___boxed(lean_object* v_00_u03b1_3739_, lean_object* v_n_3740_, lean_object* v_aa_3741_, lean_object* v_n_3742_, lean_object* v_j_3743_, lean_object* v_a_3744_, lean_object* v_a_3745_){
_start:
{
lean_object* v_res_3746_; 
v_res_3746_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2(v_00_u03b1_3739_, v_n_3740_, v_aa_3741_, v_n_3742_, v_j_3743_, v_a_3744_, v_a_3745_);
lean_dec(v_n_3742_);
lean_dec_ref(v_aa_3741_);
lean_dec(v_n_3740_);
return v_res_3746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0(lean_object* v_snd_3754_, lean_object* v___x_3755_, lean_object* v_score_3756_, lean_object* v___x_3757_, lean_object* v_k_3758_, lean_object* v_args_3759_, lean_object* v_cases_3760_){
_start:
{
lean_object* v___x_3761_; 
v___x_3761_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_snd_3754_, v_k_3758_);
if (lean_obj_tag(v___x_3761_) == 0)
{
lean_dec_ref(v___x_3755_);
return v_cases_3760_;
}
else
{
lean_object* v_val_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; 
v_val_3762_ = lean_ctor_get(v___x_3761_, 0);
lean_inc(v_val_3762_);
lean_dec_ref_known(v___x_3761_, 1);
v___x_3763_ = l_Array_append___redArg(v___x_3755_, v_args_3759_);
v___x_3764_ = lean_nat_add(v_score_3756_, v___x_3757_);
v___x_3765_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3765_, 0, v___x_3763_);
lean_ctor_set(v___x_3765_, 1, v___x_3764_);
lean_ctor_set(v___x_3765_, 2, v_val_3762_);
v___x_3766_ = lean_array_push(v_cases_3760_, v___x_3765_);
return v___x_3766_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0___boxed(lean_object* v_snd_3767_, lean_object* v___x_3768_, lean_object* v_score_3769_, lean_object* v___x_3770_, lean_object* v_k_3771_, lean_object* v_args_3772_, lean_object* v_cases_3773_){
_start:
{
lean_object* v_res_3774_; 
v_res_3774_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0(v_snd_3767_, v___x_3768_, v_score_3769_, v___x_3770_, v_k_3771_, v_args_3772_, v_cases_3773_);
lean_dec_ref(v_args_3772_);
lean_dec(v_k_3771_);
lean_dec(v___x_3770_);
lean_dec(v_score_3769_);
lean_dec_ref(v_snd_3767_);
return v_res_3774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(lean_object* v_cases_3775_, lean_object* v_result_3776_, lean_object* v_a_3777_, lean_object* v_a_3778_, lean_object* v_a_3779_, lean_object* v_a_3780_, lean_object* v_a_3781_){
_start:
{
lean_object* v___x_3783_; lean_object* v___x_3784_; uint8_t v___x_3785_; 
v___x_3783_ = lean_array_get_size(v_cases_3775_);
v___x_3784_ = lean_unsigned_to_nat(0u);
v___x_3785_ = lean_nat_dec_eq(v___x_3783_, v___x_3784_);
if (v___x_3785_ == 0)
{
lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v_ca_3789_; lean_object* v_todo_3790_; lean_object* v_score_3791_; lean_object* v_c_3792_; lean_object* v___x_3794_; uint8_t v_isShared_3795_; uint8_t v_isSharedCheck_3857_; 
v___x_3786_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedPartialMatch_default));
v___x_3787_ = lean_unsigned_to_nat(1u);
v___x_3788_ = lean_nat_sub(v___x_3783_, v___x_3787_);
v_ca_3789_ = lean_array_get(v___x_3786_, v_cases_3775_, v___x_3788_);
lean_dec(v___x_3788_);
v_todo_3790_ = lean_ctor_get(v_ca_3789_, 0);
v_score_3791_ = lean_ctor_get(v_ca_3789_, 1);
v_c_3792_ = lean_ctor_get(v_ca_3789_, 2);
v_isSharedCheck_3857_ = !lean_is_exclusive(v_ca_3789_);
if (v_isSharedCheck_3857_ == 0)
{
v___x_3794_ = v_ca_3789_;
v_isShared_3795_ = v_isSharedCheck_3857_;
goto v_resetjp_3793_;
}
else
{
lean_inc(v_c_3792_);
lean_inc(v_score_3791_);
lean_inc(v_todo_3790_);
lean_dec(v_ca_3789_);
v___x_3794_ = lean_box(0);
v_isShared_3795_ = v_isSharedCheck_3857_;
goto v_resetjp_3793_;
}
v_resetjp_3793_:
{
lean_object* v___x_3796_; 
v___x_3796_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_c_3792_, v_a_3777_, v_a_3778_, v_a_3779_, v_a_3780_, v_a_3781_);
lean_dec(v_c_3792_);
if (lean_obj_tag(v___x_3796_) == 0)
{
lean_object* v_a_3797_; uint8_t v___y_3799_; lean_object* v___y_3800_; lean_object* v___y_3801_; lean_object* v___y_3802_; lean_object* v_snd_3825_; lean_object* v_fst_3826_; lean_object* v_fst_3827_; lean_object* v_snd_3828_; lean_object* v_cases_3829_; lean_object* v___x_3830_; uint8_t v___x_3831_; 
v_a_3797_ = lean_ctor_get(v___x_3796_, 0);
lean_inc(v_a_3797_);
lean_dec_ref_known(v___x_3796_, 1);
v_snd_3825_ = lean_ctor_get(v_a_3797_, 1);
lean_inc(v_snd_3825_);
v_fst_3826_ = lean_ctor_get(v_a_3797_, 0);
lean_inc(v_fst_3826_);
lean_dec(v_a_3797_);
v_fst_3827_ = lean_ctor_get(v_snd_3825_, 0);
lean_inc(v_fst_3827_);
v_snd_3828_ = lean_ctor_get(v_snd_3825_, 1);
lean_inc(v_snd_3828_);
lean_dec(v_snd_3825_);
v_cases_3829_ = lean_array_pop(v_cases_3775_);
v___x_3830_ = lean_array_get_size(v_todo_3790_);
v___x_3831_ = lean_nat_dec_eq(v___x_3830_, v___x_3784_);
if (v___x_3831_ == 0)
{
lean_object* v___x_3832_; uint8_t v___x_3833_; uint8_t v___y_3835_; 
lean_dec(v_fst_3826_);
v___x_3832_ = l_Lean_instInhabitedExpr;
v___x_3833_ = lean_nat_dec_eq(v_fst_3827_, v___x_3784_);
if (v___x_3833_ == 0)
{
v___y_3835_ = v___x_3831_;
goto v___jp_3834_;
}
else
{
lean_object* v_size_3844_; uint8_t v___x_3845_; 
v_size_3844_ = lean_ctor_get(v_snd_3828_, 0);
v___x_3845_ = lean_nat_dec_eq(v_size_3844_, v___x_3784_);
if (v___x_3845_ == 0)
{
v___y_3835_ = v___x_3845_;
goto v___jp_3834_;
}
else
{
lean_dec(v_snd_3828_);
lean_dec(v_fst_3827_);
lean_del_object(v___x_3794_);
lean_dec(v_score_3791_);
lean_dec_ref(v_todo_3790_);
v_cases_3775_ = v_cases_3829_;
goto _start;
}
}
v___jp_3834_:
{
lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___f_3839_; 
v___x_3836_ = lean_nat_sub(v___x_3830_, v___x_3787_);
v___x_3837_ = lean_array_get(v___x_3832_, v_todo_3790_, v___x_3836_);
lean_dec(v___x_3836_);
v___x_3838_ = lean_array_pop(v_todo_3790_);
lean_inc(v_score_3791_);
lean_inc_ref(v___x_3838_);
v___f_3839_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0___boxed), 7, 4);
lean_closure_set(v___f_3839_, 0, v_snd_3828_);
lean_closure_set(v___f_3839_, 1, v___x_3838_);
lean_closure_set(v___f_3839_, 2, v_score_3791_);
lean_closure_set(v___f_3839_, 3, v___x_3787_);
if (v___x_3833_ == 0)
{
lean_object* v___x_3841_; 
if (v_isShared_3795_ == 0)
{
lean_ctor_set(v___x_3794_, 2, v_fst_3827_);
lean_ctor_set(v___x_3794_, 0, v___x_3838_);
v___x_3841_ = v___x_3794_;
goto v_reusejp_3840_;
}
else
{
lean_object* v_reuseFailAlloc_3843_; 
v_reuseFailAlloc_3843_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3843_, 0, v___x_3838_);
lean_ctor_set(v_reuseFailAlloc_3843_, 1, v_score_3791_);
lean_ctor_set(v_reuseFailAlloc_3843_, 2, v_fst_3827_);
v___x_3841_ = v_reuseFailAlloc_3843_;
goto v_reusejp_3840_;
}
v_reusejp_3840_:
{
lean_object* v___x_3842_; 
v___x_3842_ = lean_array_push(v_cases_3829_, v___x_3841_);
v___y_3799_ = v___y_3835_;
v___y_3800_ = v___f_3839_;
v___y_3801_ = v___x_3837_;
v___y_3802_ = v___x_3842_;
goto v___jp_3798_;
}
}
else
{
lean_dec_ref(v___x_3838_);
lean_dec(v_fst_3827_);
lean_del_object(v___x_3794_);
lean_dec(v_score_3791_);
v___y_3799_ = v___y_3835_;
v___y_3800_ = v___f_3839_;
v___y_3801_ = v___x_3837_;
v___y_3802_ = v_cases_3829_;
goto v___jp_3798_;
}
}
}
else
{
lean_object* v___x_3847_; 
lean_dec(v_snd_3828_);
lean_dec(v_fst_3827_);
lean_del_object(v___x_3794_);
lean_dec_ref(v_todo_3790_);
v___x_3847_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v_result_3776_, v_score_3791_, v_fst_3826_);
lean_dec(v_score_3791_);
v_cases_3775_ = v_cases_3829_;
v_result_3776_ = v___x_3847_;
goto _start;
}
v___jp_3798_:
{
uint8_t v___x_3803_; lean_object* v___x_3804_; 
v___x_3803_ = 1;
v___x_3804_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v___y_3801_, v___x_3803_, v___y_3799_, v_a_3778_, v_a_3779_, v_a_3780_, v_a_3781_);
if (lean_obj_tag(v___x_3804_) == 0)
{
lean_object* v_a_3805_; lean_object* v_fst_3806_; 
v_a_3805_ = lean_ctor_get(v___x_3804_, 0);
lean_inc(v_a_3805_);
lean_dec_ref_known(v___x_3804_, 1);
v_fst_3806_ = lean_ctor_get(v_a_3805_, 0);
lean_inc(v_fst_3806_);
switch(lean_obj_tag(v_fst_3806_))
{
case 3:
{
lean_dec(v_a_3805_);
lean_dec_ref(v___y_3800_);
v_cases_3775_ = v___y_3802_;
goto _start;
}
case 5:
{
lean_object* v_snd_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; 
v_snd_3808_ = lean_ctor_get(v_a_3805_, 1);
lean_inc(v_snd_3808_);
lean_dec(v_a_3805_);
v___x_3809_ = lean_box(4);
v___x_3810_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
lean_inc_ref(v___y_3800_);
v___x_3811_ = lean_apply_3(v___y_3800_, v___x_3809_, v___x_3810_, v___y_3802_);
v___x_3812_ = lean_apply_3(v___y_3800_, v_fst_3806_, v_snd_3808_, v___x_3811_);
v_cases_3775_ = v___x_3812_;
goto _start;
}
default: 
{
lean_object* v_snd_3814_; lean_object* v___x_3815_; 
v_snd_3814_ = lean_ctor_get(v_a_3805_, 1);
lean_inc(v_snd_3814_);
lean_dec(v_a_3805_);
v___x_3815_ = lean_apply_3(v___y_3800_, v_fst_3806_, v_snd_3814_, v___y_3802_);
v_cases_3775_ = v___x_3815_;
goto _start;
}
}
}
else
{
lean_object* v_a_3817_; lean_object* v___x_3819_; uint8_t v_isShared_3820_; uint8_t v_isSharedCheck_3824_; 
lean_dec_ref(v___y_3802_);
lean_dec_ref(v___y_3800_);
lean_dec_ref(v_result_3776_);
v_a_3817_ = lean_ctor_get(v___x_3804_, 0);
v_isSharedCheck_3824_ = !lean_is_exclusive(v___x_3804_);
if (v_isSharedCheck_3824_ == 0)
{
v___x_3819_ = v___x_3804_;
v_isShared_3820_ = v_isSharedCheck_3824_;
goto v_resetjp_3818_;
}
else
{
lean_inc(v_a_3817_);
lean_dec(v___x_3804_);
v___x_3819_ = lean_box(0);
v_isShared_3820_ = v_isSharedCheck_3824_;
goto v_resetjp_3818_;
}
v_resetjp_3818_:
{
lean_object* v___x_3822_; 
if (v_isShared_3820_ == 0)
{
v___x_3822_ = v___x_3819_;
goto v_reusejp_3821_;
}
else
{
lean_object* v_reuseFailAlloc_3823_; 
v_reuseFailAlloc_3823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3823_, 0, v_a_3817_);
v___x_3822_ = v_reuseFailAlloc_3823_;
goto v_reusejp_3821_;
}
v_reusejp_3821_:
{
return v___x_3822_;
}
}
}
}
}
else
{
lean_object* v_a_3849_; lean_object* v___x_3851_; uint8_t v_isShared_3852_; uint8_t v_isSharedCheck_3856_; 
lean_del_object(v___x_3794_);
lean_dec(v_score_3791_);
lean_dec_ref(v_todo_3790_);
lean_dec_ref(v_result_3776_);
lean_dec_ref(v_cases_3775_);
v_a_3849_ = lean_ctor_get(v___x_3796_, 0);
v_isSharedCheck_3856_ = !lean_is_exclusive(v___x_3796_);
if (v_isSharedCheck_3856_ == 0)
{
v___x_3851_ = v___x_3796_;
v_isShared_3852_ = v_isSharedCheck_3856_;
goto v_resetjp_3850_;
}
else
{
lean_inc(v_a_3849_);
lean_dec(v___x_3796_);
v___x_3851_ = lean_box(0);
v_isShared_3852_ = v_isSharedCheck_3856_;
goto v_resetjp_3850_;
}
v_resetjp_3850_:
{
lean_object* v___x_3854_; 
if (v_isShared_3852_ == 0)
{
v___x_3854_ = v___x_3851_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3855_; 
v_reuseFailAlloc_3855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3855_, 0, v_a_3849_);
v___x_3854_ = v_reuseFailAlloc_3855_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
return v___x_3854_;
}
}
}
}
}
else
{
lean_object* v___x_3858_; 
lean_dec_ref(v_cases_3775_);
v___x_3858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3858_, 0, v_result_3776_);
return v___x_3858_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___boxed(lean_object* v_cases_3859_, lean_object* v_result_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_, lean_object* v_a_3865_, lean_object* v_a_3866_){
_start:
{
lean_object* v_res_3867_; 
v_res_3867_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v_cases_3859_, v_result_3860_, v_a_3861_, v_a_3862_, v_a_3863_, v_a_3864_, v_a_3865_);
lean_dec(v_a_3865_);
lean_dec_ref(v_a_3864_);
lean_dec(v_a_3863_);
lean_dec_ref(v_a_3862_);
lean_dec(v_a_3861_);
return v_res_3867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop(lean_object* v_00_u03b1_3868_, lean_object* v_cases_3869_, lean_object* v_result_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_, lean_object* v_a_3873_, lean_object* v_a_3874_, lean_object* v_a_3875_){
_start:
{
lean_object* v___x_3877_; 
v___x_3877_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v_cases_3869_, v_result_3870_, v_a_3871_, v_a_3872_, v_a_3873_, v_a_3874_, v_a_3875_);
return v___x_3877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___boxed(lean_object* v_00_u03b1_3878_, lean_object* v_cases_3879_, lean_object* v_result_3880_, lean_object* v_a_3881_, lean_object* v_a_3882_, lean_object* v_a_3883_, lean_object* v_a_3884_, lean_object* v_a_3885_, lean_object* v_a_3886_){
_start:
{
lean_object* v_res_3887_; 
v_res_3887_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop(v_00_u03b1_3878_, v_cases_3879_, v_result_3880_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_, v_a_3885_);
lean_dec(v_a_3885_);
lean_dec_ref(v_a_3884_);
lean_dec(v_a_3883_);
lean_dec_ref(v_a_3882_);
lean_dec(v_a_3881_);
return v_res_3887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult___redArg(lean_object* v_root_3890_, lean_object* v_a_3891_, lean_object* v_a_3892_, lean_object* v_a_3893_, lean_object* v_a_3894_, lean_object* v_a_3895_){
_start:
{
lean_object* v___x_3897_; lean_object* v___x_3898_; 
v___x_3897_ = lean_box(3);
v___x_3898_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_root_3890_, v___x_3897_);
if (lean_obj_tag(v___x_3898_) == 0)
{
lean_object* v___x_3899_; lean_object* v___x_3900_; 
v___x_3899_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_getStarResult___redArg___closed__0));
v___x_3900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3900_, 0, v___x_3899_);
return v___x_3900_;
}
else
{
lean_object* v_val_3901_; lean_object* v___x_3902_; 
v_val_3901_ = lean_ctor_get(v___x_3898_, 0);
lean_inc(v_val_3901_);
lean_dec_ref_known(v___x_3898_, 1);
v___x_3902_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_val_3901_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_);
lean_dec(v_val_3901_);
if (lean_obj_tag(v___x_3902_) == 0)
{
lean_object* v_a_3903_; lean_object* v___x_3905_; uint8_t v_isShared_3906_; uint8_t v_isSharedCheck_3914_; 
v_a_3903_ = lean_ctor_get(v___x_3902_, 0);
v_isSharedCheck_3914_ = !lean_is_exclusive(v___x_3902_);
if (v_isSharedCheck_3914_ == 0)
{
v___x_3905_ = v___x_3902_;
v_isShared_3906_ = v_isSharedCheck_3914_;
goto v_resetjp_3904_;
}
else
{
lean_inc(v_a_3903_);
lean_dec(v___x_3902_);
v___x_3905_ = lean_box(0);
v_isShared_3906_ = v_isSharedCheck_3914_;
goto v_resetjp_3904_;
}
v_resetjp_3904_:
{
lean_object* v_fst_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3912_; 
v_fst_3907_ = lean_ctor_get(v_a_3903_, 0);
lean_inc(v_fst_3907_);
lean_dec(v_a_3903_);
v___x_3908_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_getStarResult___redArg___closed__0));
v___x_3909_ = lean_unsigned_to_nat(1u);
v___x_3910_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v___x_3908_, v___x_3909_, v_fst_3907_);
if (v_isShared_3906_ == 0)
{
lean_ctor_set(v___x_3905_, 0, v___x_3910_);
v___x_3912_ = v___x_3905_;
goto v_reusejp_3911_;
}
else
{
lean_object* v_reuseFailAlloc_3913_; 
v_reuseFailAlloc_3913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3913_, 0, v___x_3910_);
v___x_3912_ = v_reuseFailAlloc_3913_;
goto v_reusejp_3911_;
}
v_reusejp_3911_:
{
return v___x_3912_;
}
}
}
else
{
lean_object* v_a_3915_; lean_object* v___x_3917_; uint8_t v_isShared_3918_; uint8_t v_isSharedCheck_3922_; 
v_a_3915_ = lean_ctor_get(v___x_3902_, 0);
v_isSharedCheck_3922_ = !lean_is_exclusive(v___x_3902_);
if (v_isSharedCheck_3922_ == 0)
{
v___x_3917_ = v___x_3902_;
v_isShared_3918_ = v_isSharedCheck_3922_;
goto v_resetjp_3916_;
}
else
{
lean_inc(v_a_3915_);
lean_dec(v___x_3902_);
v___x_3917_ = lean_box(0);
v_isShared_3918_ = v_isSharedCheck_3922_;
goto v_resetjp_3916_;
}
v_resetjp_3916_:
{
lean_object* v___x_3920_; 
if (v_isShared_3918_ == 0)
{
v___x_3920_ = v___x_3917_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v_a_3915_);
v___x_3920_ = v_reuseFailAlloc_3921_;
goto v_reusejp_3919_;
}
v_reusejp_3919_:
{
return v___x_3920_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult___redArg___boxed(lean_object* v_root_3923_, lean_object* v_a_3924_, lean_object* v_a_3925_, lean_object* v_a_3926_, lean_object* v_a_3927_, lean_object* v_a_3928_, lean_object* v_a_3929_){
_start:
{
lean_object* v_res_3930_; 
v_res_3930_ = l_Lean_Meta_LazyDiscrTree_getStarResult___redArg(v_root_3923_, v_a_3924_, v_a_3925_, v_a_3926_, v_a_3927_, v_a_3928_);
lean_dec(v_a_3928_);
lean_dec_ref(v_a_3927_);
lean_dec(v_a_3926_);
lean_dec_ref(v_a_3925_);
lean_dec(v_a_3924_);
lean_dec_ref(v_root_3923_);
return v_res_3930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult(lean_object* v_00_u03b1_3931_, lean_object* v_root_3932_, lean_object* v_a_3933_, lean_object* v_a_3934_, lean_object* v_a_3935_, lean_object* v_a_3936_, lean_object* v_a_3937_){
_start:
{
lean_object* v___x_3939_; 
v___x_3939_ = l_Lean_Meta_LazyDiscrTree_getStarResult___redArg(v_root_3932_, v_a_3933_, v_a_3934_, v_a_3935_, v_a_3936_, v_a_3937_);
return v___x_3939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult___boxed(lean_object* v_00_u03b1_3940_, lean_object* v_root_3941_, lean_object* v_a_3942_, lean_object* v_a_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_){
_start:
{
lean_object* v_res_3948_; 
v_res_3948_ = l_Lean_Meta_LazyDiscrTree_getStarResult(v_00_u03b1_3940_, v_root_3941_, v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_, v_a_3946_);
lean_dec(v_a_3946_);
lean_dec_ref(v_a_3945_);
lean_dec(v_a_3944_);
lean_dec_ref(v_a_3943_);
lean_dec(v_a_3942_);
lean_dec_ref(v_root_3941_);
return v_res_3948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushRootCase(lean_object* v_r_3949_, lean_object* v_k_3950_, lean_object* v_args_3951_, lean_object* v_cases_3952_){
_start:
{
lean_object* v___x_3953_; 
v___x_3953_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_r_3949_, v_k_3950_);
if (lean_obj_tag(v___x_3953_) == 0)
{
lean_dec_ref(v_args_3951_);
return v_cases_3952_;
}
else
{
lean_object* v_val_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; 
v_val_3954_ = lean_ctor_get(v___x_3953_, 0);
lean_inc(v_val_3954_);
lean_dec_ref_known(v___x_3953_, 1);
v___x_3955_ = lean_unsigned_to_nat(1u);
v___x_3956_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3956_, 0, v_args_3951_);
lean_ctor_set(v___x_3956_, 1, v___x_3955_);
lean_ctor_set(v___x_3956_, 2, v_val_3954_);
v___x_3957_ = lean_array_push(v_cases_3952_, v___x_3956_);
return v___x_3957_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushRootCase___boxed(lean_object* v_r_3958_, lean_object* v_k_3959_, lean_object* v_args_3960_, lean_object* v_cases_3961_){
_start:
{
lean_object* v_res_3962_; 
v_res_3962_ = l_Lean_Meta_LazyDiscrTree_pushRootCase(v_r_3958_, v_k_3959_, v_args_3960_, v_cases_3961_);
lean_dec(v_k_3959_);
lean_dec_ref(v_r_3958_);
return v_res_3962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg(lean_object* v_root_3965_, lean_object* v_e_3966_, lean_object* v_a_3967_, lean_object* v_a_3968_, lean_object* v_a_3969_, lean_object* v_a_3970_, lean_object* v_a_3971_){
_start:
{
lean_object* v___x_3973_; 
v___x_3973_ = l_Lean_Meta_LazyDiscrTree_getStarResult___redArg(v_root_3965_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_, v_a_3971_);
if (lean_obj_tag(v___x_3973_) == 0)
{
lean_object* v_a_3974_; uint8_t v___x_3975_; lean_object* v___x_3976_; 
v_a_3974_ = lean_ctor_get(v___x_3973_, 0);
lean_inc(v_a_3974_);
lean_dec_ref_known(v___x_3973_, 1);
v___x_3975_ = 1;
v___x_3976_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_3966_, v___x_3975_, v___x_3975_, v_a_3968_, v_a_3969_, v_a_3970_, v_a_3971_);
if (lean_obj_tag(v___x_3976_) == 0)
{
lean_object* v_a_3977_; lean_object* v_fst_3978_; 
v_a_3977_ = lean_ctor_get(v___x_3976_, 0);
lean_inc(v_a_3977_);
lean_dec_ref_known(v___x_3976_, 1);
v_fst_3978_ = lean_ctor_get(v_a_3977_, 0);
lean_inc(v_fst_3978_);
switch(lean_obj_tag(v_fst_3978_))
{
case 3:
{
lean_object* v___x_3979_; lean_object* v___x_3980_; 
lean_dec(v_a_3977_);
v___x_3979_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg___closed__0));
v___x_3980_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v___x_3979_, v_a_3974_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_, v_a_3971_);
return v___x_3980_;
}
case 5:
{
lean_object* v_snd_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; 
v_snd_3981_ = lean_ctor_get(v_a_3977_, 1);
lean_inc(v_snd_3981_);
lean_dec(v_a_3977_);
v___x_3982_ = lean_box(4);
v___x_3983_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
v___x_3984_ = l_Lean_Meta_LazyDiscrTree_pushRootCase(v_root_3965_, v___x_3982_, v___x_3983_, v___x_3983_);
v___x_3985_ = l_Lean_Meta_LazyDiscrTree_pushRootCase(v_root_3965_, v_fst_3978_, v_snd_3981_, v___x_3984_);
v___x_3986_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v___x_3985_, v_a_3974_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_, v_a_3971_);
return v___x_3986_;
}
default: 
{
lean_object* v_snd_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; 
v_snd_3987_ = lean_ctor_get(v_a_3977_, 1);
lean_inc(v_snd_3987_);
lean_dec(v_a_3977_);
v___x_3988_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg___closed__0));
v___x_3989_ = l_Lean_Meta_LazyDiscrTree_pushRootCase(v_root_3965_, v_fst_3978_, v_snd_3987_, v___x_3988_);
lean_dec(v_fst_3978_);
v___x_3990_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v___x_3989_, v_a_3974_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_, v_a_3971_);
return v___x_3990_;
}
}
}
else
{
lean_object* v_a_3991_; lean_object* v___x_3993_; uint8_t v_isShared_3994_; uint8_t v_isSharedCheck_3998_; 
lean_dec(v_a_3974_);
v_a_3991_ = lean_ctor_get(v___x_3976_, 0);
v_isSharedCheck_3998_ = !lean_is_exclusive(v___x_3976_);
if (v_isSharedCheck_3998_ == 0)
{
v___x_3993_ = v___x_3976_;
v_isShared_3994_ = v_isSharedCheck_3998_;
goto v_resetjp_3992_;
}
else
{
lean_inc(v_a_3991_);
lean_dec(v___x_3976_);
v___x_3993_ = lean_box(0);
v_isShared_3994_ = v_isSharedCheck_3998_;
goto v_resetjp_3992_;
}
v_resetjp_3992_:
{
lean_object* v___x_3996_; 
if (v_isShared_3994_ == 0)
{
v___x_3996_ = v___x_3993_;
goto v_reusejp_3995_;
}
else
{
lean_object* v_reuseFailAlloc_3997_; 
v_reuseFailAlloc_3997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3997_, 0, v_a_3991_);
v___x_3996_ = v_reuseFailAlloc_3997_;
goto v_reusejp_3995_;
}
v_reusejp_3995_:
{
return v___x_3996_;
}
}
}
}
else
{
lean_dec_ref(v_e_3966_);
return v___x_3973_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg___boxed(lean_object* v_root_3999_, lean_object* v_e_4000_, lean_object* v_a_4001_, lean_object* v_a_4002_, lean_object* v_a_4003_, lean_object* v_a_4004_, lean_object* v_a_4005_, lean_object* v_a_4006_){
_start:
{
lean_object* v_res_4007_; 
v_res_4007_ = l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg(v_root_3999_, v_e_4000_, v_a_4001_, v_a_4002_, v_a_4003_, v_a_4004_, v_a_4005_);
lean_dec(v_a_4005_);
lean_dec_ref(v_a_4004_);
lean_dec(v_a_4003_);
lean_dec_ref(v_a_4002_);
lean_dec(v_a_4001_);
lean_dec_ref(v_root_3999_);
return v_res_4007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore(lean_object* v_00_u03b1_4008_, lean_object* v_root_4009_, lean_object* v_e_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_){
_start:
{
lean_object* v___x_4017_; 
v___x_4017_ = l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg(v_root_4009_, v_e_4010_, v_a_4011_, v_a_4012_, v_a_4013_, v_a_4014_, v_a_4015_);
return v___x_4017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore___boxed(lean_object* v_00_u03b1_4018_, lean_object* v_root_4019_, lean_object* v_e_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_, lean_object* v_a_4023_, lean_object* v_a_4024_, lean_object* v_a_4025_, lean_object* v_a_4026_){
_start:
{
lean_object* v_res_4027_; 
v_res_4027_ = l_Lean_Meta_LazyDiscrTree_getMatchCore(v_00_u03b1_4018_, v_root_4019_, v_e_4020_, v_a_4021_, v_a_4022_, v_a_4023_, v_a_4024_, v_a_4025_);
lean_dec(v_a_4025_);
lean_dec_ref(v_a_4024_);
lean_dec(v_a_4023_);
lean_dec_ref(v_a_4022_);
lean_dec(v_a_4021_);
lean_dec_ref(v_root_4019_);
return v_res_4027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch___redArg(lean_object* v_d_4028_, lean_object* v_e_4029_, lean_object* v_a_4030_, lean_object* v_a_4031_, lean_object* v_a_4032_, lean_object* v_a_4033_){
_start:
{
lean_object* v___y_4036_; lean_object* v_roots_4053_; lean_object* v___x_4054_; uint8_t v_transparency_4055_; lean_object* v___x_4056_; uint8_t v___x_4057_; uint8_t v___x_4058_; 
v_roots_4053_ = lean_ctor_get(v_d_4028_, 1);
v___x_4054_ = l_Lean_Meta_Context_config(v_a_4030_);
v_transparency_4055_ = lean_ctor_get_uint8(v___x_4054_, 9);
lean_dec_ref(v___x_4054_);
lean_inc_ref(v_roots_4053_);
v___x_4056_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getMatchCore___boxed), 9, 3);
lean_closure_set(v___x_4056_, 0, lean_box(0));
lean_closure_set(v___x_4056_, 1, v_roots_4053_);
lean_closure_set(v___x_4056_, 2, v_e_4029_);
v___x_4057_ = 2;
v___x_4058_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_4055_, v___x_4057_);
if (v___x_4058_ == 0)
{
lean_object* v_keyedConfig_4059_; uint8_t v_trackZetaDelta_4060_; lean_object* v_zetaDeltaSet_4061_; lean_object* v_lctx_4062_; lean_object* v_localInstances_4063_; lean_object* v_defEqCtx_x3f_4064_; lean_object* v_synthPendingDepth_4065_; lean_object* v_customCanUnfoldPredicate_x3f_4066_; uint8_t v_univApprox_4067_; uint8_t v_inTypeClassResolution_4068_; uint8_t v_cacheInferType_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; 
v_keyedConfig_4059_ = lean_ctor_get(v_a_4030_, 0);
v_trackZetaDelta_4060_ = lean_ctor_get_uint8(v_a_4030_, sizeof(void*)*7);
v_zetaDeltaSet_4061_ = lean_ctor_get(v_a_4030_, 1);
v_lctx_4062_ = lean_ctor_get(v_a_4030_, 2);
v_localInstances_4063_ = lean_ctor_get(v_a_4030_, 3);
v_defEqCtx_x3f_4064_ = lean_ctor_get(v_a_4030_, 4);
v_synthPendingDepth_4065_ = lean_ctor_get(v_a_4030_, 5);
v_customCanUnfoldPredicate_x3f_4066_ = lean_ctor_get(v_a_4030_, 6);
v_univApprox_4067_ = lean_ctor_get_uint8(v_a_4030_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4068_ = lean_ctor_get_uint8(v_a_4030_, sizeof(void*)*7 + 2);
v_cacheInferType_4069_ = lean_ctor_get_uint8(v_a_4030_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_4059_);
v___x_4070_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4057_, v_keyedConfig_4059_);
lean_inc(v_customCanUnfoldPredicate_x3f_4066_);
lean_inc(v_synthPendingDepth_4065_);
lean_inc(v_defEqCtx_x3f_4064_);
lean_inc_ref(v_localInstances_4063_);
lean_inc_ref(v_lctx_4062_);
lean_inc(v_zetaDeltaSet_4061_);
v___x_4071_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4071_, 0, v___x_4070_);
lean_ctor_set(v___x_4071_, 1, v_zetaDeltaSet_4061_);
lean_ctor_set(v___x_4071_, 2, v_lctx_4062_);
lean_ctor_set(v___x_4071_, 3, v_localInstances_4063_);
lean_ctor_set(v___x_4071_, 4, v_defEqCtx_x3f_4064_);
lean_ctor_set(v___x_4071_, 5, v_synthPendingDepth_4065_);
lean_ctor_set(v___x_4071_, 6, v_customCanUnfoldPredicate_x3f_4066_);
lean_ctor_set_uint8(v___x_4071_, sizeof(void*)*7, v_trackZetaDelta_4060_);
lean_ctor_set_uint8(v___x_4071_, sizeof(void*)*7 + 1, v_univApprox_4067_);
lean_ctor_set_uint8(v___x_4071_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4068_);
lean_ctor_set_uint8(v___x_4071_, sizeof(void*)*7 + 3, v_cacheInferType_4069_);
v___x_4072_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_d_4028_, v___x_4056_, v___x_4071_, v_a_4031_, v_a_4032_, v_a_4033_);
lean_dec_ref_known(v___x_4071_, 7);
v___y_4036_ = v___x_4072_;
goto v___jp_4035_;
}
else
{
lean_object* v___x_4073_; 
v___x_4073_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_d_4028_, v___x_4056_, v_a_4030_, v_a_4031_, v_a_4032_, v_a_4033_);
v___y_4036_ = v___x_4073_;
goto v___jp_4035_;
}
v___jp_4035_:
{
if (lean_obj_tag(v___y_4036_) == 0)
{
lean_object* v_a_4037_; lean_object* v___x_4039_; uint8_t v_isShared_4040_; uint8_t v_isSharedCheck_4044_; 
v_a_4037_ = lean_ctor_get(v___y_4036_, 0);
v_isSharedCheck_4044_ = !lean_is_exclusive(v___y_4036_);
if (v_isSharedCheck_4044_ == 0)
{
v___x_4039_ = v___y_4036_;
v_isShared_4040_ = v_isSharedCheck_4044_;
goto v_resetjp_4038_;
}
else
{
lean_inc(v_a_4037_);
lean_dec(v___y_4036_);
v___x_4039_ = lean_box(0);
v_isShared_4040_ = v_isSharedCheck_4044_;
goto v_resetjp_4038_;
}
v_resetjp_4038_:
{
lean_object* v___x_4042_; 
if (v_isShared_4040_ == 0)
{
v___x_4042_ = v___x_4039_;
goto v_reusejp_4041_;
}
else
{
lean_object* v_reuseFailAlloc_4043_; 
v_reuseFailAlloc_4043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4043_, 0, v_a_4037_);
v___x_4042_ = v_reuseFailAlloc_4043_;
goto v_reusejp_4041_;
}
v_reusejp_4041_:
{
return v___x_4042_;
}
}
}
else
{
lean_object* v_a_4045_; lean_object* v___x_4047_; uint8_t v_isShared_4048_; uint8_t v_isSharedCheck_4052_; 
v_a_4045_ = lean_ctor_get(v___y_4036_, 0);
v_isSharedCheck_4052_ = !lean_is_exclusive(v___y_4036_);
if (v_isSharedCheck_4052_ == 0)
{
v___x_4047_ = v___y_4036_;
v_isShared_4048_ = v_isSharedCheck_4052_;
goto v_resetjp_4046_;
}
else
{
lean_inc(v_a_4045_);
lean_dec(v___y_4036_);
v___x_4047_ = lean_box(0);
v_isShared_4048_ = v_isSharedCheck_4052_;
goto v_resetjp_4046_;
}
v_resetjp_4046_:
{
lean_object* v___x_4050_; 
if (v_isShared_4048_ == 0)
{
v___x_4050_ = v___x_4047_;
goto v_reusejp_4049_;
}
else
{
lean_object* v_reuseFailAlloc_4051_; 
v_reuseFailAlloc_4051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4051_, 0, v_a_4045_);
v___x_4050_ = v_reuseFailAlloc_4051_;
goto v_reusejp_4049_;
}
v_reusejp_4049_:
{
return v___x_4050_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch___redArg___boxed(lean_object* v_d_4074_, lean_object* v_e_4075_, lean_object* v_a_4076_, lean_object* v_a_4077_, lean_object* v_a_4078_, lean_object* v_a_4079_, lean_object* v_a_4080_){
_start:
{
lean_object* v_res_4081_; 
v_res_4081_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v_d_4074_, v_e_4075_, v_a_4076_, v_a_4077_, v_a_4078_, v_a_4079_);
lean_dec(v_a_4079_);
lean_dec_ref(v_a_4078_);
lean_dec(v_a_4077_);
lean_dec_ref(v_a_4076_);
return v_res_4081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch(lean_object* v_00_u03b1_4082_, lean_object* v_d_4083_, lean_object* v_e_4084_, lean_object* v_a_4085_, lean_object* v_a_4086_, lean_object* v_a_4087_, lean_object* v_a_4088_){
_start:
{
lean_object* v___x_4090_; 
v___x_4090_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v_d_4083_, v_e_4084_, v_a_4085_, v_a_4086_, v_a_4087_, v_a_4088_);
return v___x_4090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch___boxed(lean_object* v_00_u03b1_4091_, lean_object* v_d_4092_, lean_object* v_e_4093_, lean_object* v_a_4094_, lean_object* v_a_4095_, lean_object* v_a_4096_, lean_object* v_a_4097_, lean_object* v_a_4098_){
_start:
{
lean_object* v_res_4099_; 
v_res_4099_ = l_Lean_Meta_LazyDiscrTree_getMatch(v_00_u03b1_4091_, v_d_4092_, v_e_4093_, v_a_4094_, v_a_4095_, v_a_4096_, v_a_4097_);
lean_dec(v_a_4097_);
lean_dec_ref(v_a_4096_);
lean_dec(v_a_4095_);
lean_dec_ref(v_a_4094_);
return v_res_4099_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1(void){
_start:
{
lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; 
v___x_4102_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0));
v___x_4103_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_4104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4104_, 0, v___x_4103_);
lean_ctor_set(v___x_4104_, 1, v___x_4102_);
return v___x_4104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default(lean_object* v_00_u03b1_4105_){
_start:
{
lean_object* v___x_4106_; 
v___x_4106_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1);
return v___x_4106_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___closed__0(void){
_start:
{
lean_object* v___x_4107_; 
v___x_4107_ = l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default(lean_box(0));
return v___x_4107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree(lean_object* v_a_4108_){
_start:
{
lean_object* v___x_4109_; 
v___x_4109_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___closed__0);
return v___x_4109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(lean_object* v_d_4110_, lean_object* v_k_4111_, lean_object* v_f_4112_){
_start:
{
lean_object* v_roots_4113_; lean_object* v_tries_4114_; lean_object* v___x_4115_; 
v_roots_4113_ = lean_ctor_get(v_d_4110_, 0);
v_tries_4114_ = lean_ctor_get(v_d_4110_, 1);
v___x_4115_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_roots_4113_, v_k_4111_);
if (lean_obj_tag(v___x_4115_) == 0)
{
lean_object* v___x_4117_; uint8_t v_isShared_4118_; uint8_t v_isSharedCheck_4127_; 
lean_inc_ref(v_tries_4114_);
lean_inc_ref(v_roots_4113_);
v_isSharedCheck_4127_ = !lean_is_exclusive(v_d_4110_);
if (v_isSharedCheck_4127_ == 0)
{
lean_object* v_unused_4128_; lean_object* v_unused_4129_; 
v_unused_4128_ = lean_ctor_get(v_d_4110_, 1);
lean_dec(v_unused_4128_);
v_unused_4129_ = lean_ctor_get(v_d_4110_, 0);
lean_dec(v_unused_4129_);
v___x_4117_ = v_d_4110_;
v_isShared_4118_ = v_isSharedCheck_4127_;
goto v_resetjp_4116_;
}
else
{
lean_dec(v_d_4110_);
v___x_4117_ = lean_box(0);
v_isShared_4118_ = v_isSharedCheck_4127_;
goto v_resetjp_4116_;
}
v_resetjp_4116_:
{
lean_object* v___x_4119_; lean_object* v_roots_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4125_; 
v___x_4119_ = lean_array_get_size(v_tries_4114_);
v_roots_4120_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_roots_4113_, v_k_4111_, v___x_4119_);
v___x_4121_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__3));
v___x_4122_ = lean_apply_1(v_f_4112_, v___x_4121_);
v___x_4123_ = lean_array_push(v_tries_4114_, v___x_4122_);
if (v_isShared_4118_ == 0)
{
lean_ctor_set(v___x_4117_, 1, v___x_4123_);
lean_ctor_set(v___x_4117_, 0, v_roots_4120_);
v___x_4125_ = v___x_4117_;
goto v_reusejp_4124_;
}
else
{
lean_object* v_reuseFailAlloc_4126_; 
v_reuseFailAlloc_4126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4126_, 0, v_roots_4120_);
lean_ctor_set(v_reuseFailAlloc_4126_, 1, v___x_4123_);
v___x_4125_ = v_reuseFailAlloc_4126_;
goto v_reusejp_4124_;
}
v_reusejp_4124_:
{
return v___x_4125_;
}
}
}
else
{
lean_object* v_val_4130_; lean_object* v___x_4131_; uint8_t v___x_4132_; 
lean_dec(v_k_4111_);
v_val_4130_ = lean_ctor_get(v___x_4115_, 0);
lean_inc(v_val_4130_);
lean_dec_ref_known(v___x_4115_, 1);
v___x_4131_ = lean_array_get_size(v_tries_4114_);
v___x_4132_ = lean_nat_dec_lt(v_val_4130_, v___x_4131_);
if (v___x_4132_ == 0)
{
lean_dec(v_val_4130_);
lean_dec_ref(v_f_4112_);
return v_d_4110_;
}
else
{
lean_object* v___x_4134_; uint8_t v_isShared_4135_; uint8_t v_isSharedCheck_4144_; 
lean_inc_ref(v_tries_4114_);
lean_inc_ref(v_roots_4113_);
v_isSharedCheck_4144_ = !lean_is_exclusive(v_d_4110_);
if (v_isSharedCheck_4144_ == 0)
{
lean_object* v_unused_4145_; lean_object* v_unused_4146_; 
v_unused_4145_ = lean_ctor_get(v_d_4110_, 1);
lean_dec(v_unused_4145_);
v_unused_4146_ = lean_ctor_get(v_d_4110_, 0);
lean_dec(v_unused_4146_);
v___x_4134_ = v_d_4110_;
v_isShared_4135_ = v_isSharedCheck_4144_;
goto v_resetjp_4133_;
}
else
{
lean_dec(v_d_4110_);
v___x_4134_ = lean_box(0);
v_isShared_4135_ = v_isSharedCheck_4144_;
goto v_resetjp_4133_;
}
v_resetjp_4133_:
{
lean_object* v_v_4136_; lean_object* v___x_4137_; lean_object* v_xs_x27_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4142_; 
v_v_4136_ = lean_array_fget(v_tries_4114_, v_val_4130_);
v___x_4137_ = lean_box(0);
v_xs_x27_4138_ = lean_array_fset(v_tries_4114_, v_val_4130_, v___x_4137_);
v___x_4139_ = lean_apply_1(v_f_4112_, v_v_4136_);
v___x_4140_ = lean_array_fset(v_xs_x27_4138_, v_val_4130_, v___x_4139_);
lean_dec(v_val_4130_);
if (v_isShared_4135_ == 0)
{
lean_ctor_set(v___x_4134_, 1, v___x_4140_);
v___x_4142_ = v___x_4134_;
goto v_reusejp_4141_;
}
else
{
lean_object* v_reuseFailAlloc_4143_; 
v_reuseFailAlloc_4143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4143_, 0, v_roots_4113_);
lean_ctor_set(v_reuseFailAlloc_4143_, 1, v___x_4140_);
v___x_4142_ = v_reuseFailAlloc_4143_;
goto v_reusejp_4141_;
}
v_reusejp_4141_:
{
return v___x_4142_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt(lean_object* v_00_u03b1_4147_, lean_object* v_d_4148_, lean_object* v_k_4149_, lean_object* v_f_4150_){
_start:
{
lean_object* v___x_4151_; 
v___x_4151_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(v_d_4148_, v_k_4149_, v_f_4150_);
return v___x_4151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg___lam__0(lean_object* v_e_4152_, lean_object* v_x_4153_){
_start:
{
lean_object* v___x_4154_; 
v___x_4154_ = lean_array_push(v_x_4153_, v_e_4152_);
return v___x_4154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg(lean_object* v_d_4155_, lean_object* v_k_4156_, lean_object* v_e_4157_){
_start:
{
lean_object* v___f_4158_; lean_object* v___x_4159_; 
v___f_4158_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4158_, 0, v_e_4157_);
v___x_4159_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(v_d_4155_, v_k_4156_, v___f_4158_);
return v___x_4159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push(lean_object* v_00_u03b1_4160_, lean_object* v_d_4161_, lean_object* v_k_4162_, lean_object* v_e_4163_){
_start:
{
lean_object* v___x_4164_; 
v___x_4164_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg(v_d_4161_, v_k_4162_, v_e_4163_);
return v___x_4164_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(size_t v_sz_4165_, size_t v_i_4166_, lean_object* v_bs_4167_){
_start:
{
uint8_t v___x_4168_; 
v___x_4168_ = lean_usize_dec_lt(v_i_4166_, v_sz_4165_);
if (v___x_4168_ == 0)
{
return v_bs_4167_;
}
else
{
lean_object* v_v_4169_; lean_object* v___x_4170_; lean_object* v_bs_x27_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; size_t v___x_4175_; size_t v___x_4176_; lean_object* v___x_4177_; 
v_v_4169_ = lean_array_uget(v_bs_4167_, v_i_4166_);
v___x_4170_ = lean_unsigned_to_nat(0u);
v_bs_x27_4171_ = lean_array_uset(v_bs_4167_, v_i_4166_, v___x_4170_);
v___x_4172_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0));
v___x_4173_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_4174_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4174_, 0, v___x_4172_);
lean_ctor_set(v___x_4174_, 1, v___x_4170_);
lean_ctor_set(v___x_4174_, 2, v___x_4173_);
lean_ctor_set(v___x_4174_, 3, v_v_4169_);
v___x_4175_ = ((size_t)1ULL);
v___x_4176_ = lean_usize_add(v_i_4166_, v___x_4175_);
v___x_4177_ = lean_array_uset(v_bs_x27_4171_, v_i_4166_, v___x_4174_);
v_i_4166_ = v___x_4176_;
v_bs_4167_ = v___x_4177_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg___boxed(lean_object* v_sz_4179_, lean_object* v_i_4180_, lean_object* v_bs_4181_){
_start:
{
size_t v_sz_boxed_4182_; size_t v_i_boxed_4183_; lean_object* v_res_4184_; 
v_sz_boxed_4182_ = lean_unbox_usize(v_sz_4179_);
lean_dec(v_sz_4179_);
v_i_boxed_4183_ = lean_unbox_usize(v_i_4180_);
lean_dec(v_i_4180_);
v_res_4184_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(v_sz_boxed_4182_, v_i_boxed_4183_, v_bs_4181_);
return v_res_4184_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__1(lean_object* v_x_4185_, lean_object* v_x_4186_){
_start:
{
if (lean_obj_tag(v_x_4186_) == 0)
{
return v_x_4185_;
}
else
{
lean_object* v_key_4187_; lean_object* v_value_4188_; lean_object* v_tail_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; 
v_key_4187_ = lean_ctor_get(v_x_4186_, 0);
lean_inc(v_key_4187_);
v_value_4188_ = lean_ctor_get(v_x_4186_, 1);
lean_inc(v_value_4188_);
v_tail_4189_ = lean_ctor_get(v_x_4186_, 2);
lean_inc(v_tail_4189_);
lean_dec_ref_known(v_x_4186_, 3);
v___x_4190_ = lean_unsigned_to_nat(1u);
v___x_4191_ = lean_nat_add(v_value_4188_, v___x_4190_);
lean_dec(v_value_4188_);
v___x_4192_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_x_4185_, v_key_4187_, v___x_4191_);
v_x_4185_ = v___x_4192_;
v_x_4186_ = v_tail_4189_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(lean_object* v_as_4194_, size_t v_i_4195_, size_t v_stop_4196_, lean_object* v_b_4197_){
_start:
{
uint8_t v___x_4198_; 
v___x_4198_ = lean_usize_dec_eq(v_i_4195_, v_stop_4196_);
if (v___x_4198_ == 0)
{
lean_object* v___x_4199_; lean_object* v___x_4200_; size_t v___x_4201_; size_t v___x_4202_; 
v___x_4199_ = lean_array_uget_borrowed(v_as_4194_, v_i_4195_);
lean_inc(v___x_4199_);
v___x_4200_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__1(v_b_4197_, v___x_4199_);
v___x_4201_ = ((size_t)1ULL);
v___x_4202_ = lean_usize_add(v_i_4195_, v___x_4201_);
v_i_4195_ = v___x_4202_;
v_b_4197_ = v___x_4200_;
goto _start;
}
else
{
return v_b_4197_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2___boxed(lean_object* v_as_4204_, lean_object* v_i_4205_, lean_object* v_stop_4206_, lean_object* v_b_4207_){
_start:
{
size_t v_i_boxed_4208_; size_t v_stop_boxed_4209_; lean_object* v_res_4210_; 
v_i_boxed_4208_ = lean_unbox_usize(v_i_4205_);
lean_dec(v_i_4205_);
v_stop_boxed_4209_ = lean_unbox_usize(v_stop_4206_);
lean_dec(v_stop_4206_);
v_res_4210_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(v_as_4204_, v_i_boxed_4208_, v_stop_boxed_4209_, v_b_4207_);
lean_dec_ref(v_as_4204_);
return v_res_4210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(lean_object* v_d_4211_){
_start:
{
lean_object* v_roots_4212_; lean_object* v_tries_4213_; lean_object* v___x_4215_; uint8_t v_isShared_4216_; uint8_t v_isSharedCheck_4236_; 
v_roots_4212_ = lean_ctor_get(v_d_4211_, 0);
v_tries_4213_ = lean_ctor_get(v_d_4211_, 1);
v_isSharedCheck_4236_ = !lean_is_exclusive(v_d_4211_);
if (v_isSharedCheck_4236_ == 0)
{
v___x_4215_ = v_d_4211_;
v_isShared_4216_ = v_isSharedCheck_4236_;
goto v_resetjp_4214_;
}
else
{
lean_inc(v_tries_4213_);
lean_inc(v_roots_4212_);
lean_dec(v_d_4211_);
v___x_4215_ = lean_box(0);
v_isShared_4216_ = v_isSharedCheck_4236_;
goto v_resetjp_4214_;
}
v_resetjp_4214_:
{
lean_object* v___y_4218_; lean_object* v_buckets_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; uint8_t v___x_4232_; 
v_buckets_4229_ = lean_ctor_get(v_roots_4212_, 1);
v___x_4230_ = lean_unsigned_to_nat(0u);
v___x_4231_ = lean_array_get_size(v_buckets_4229_);
v___x_4232_ = lean_nat_dec_lt(v___x_4230_, v___x_4231_);
if (v___x_4232_ == 0)
{
v___y_4218_ = v_roots_4212_;
goto v___jp_4217_;
}
else
{
size_t v___x_4233_; size_t v___x_4234_; lean_object* v___x_4235_; 
lean_inc_ref(v_buckets_4229_);
v___x_4233_ = ((size_t)0ULL);
v___x_4234_ = lean_usize_of_nat(v___x_4231_);
v___x_4235_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(v_buckets_4229_, v___x_4233_, v___x_4234_, v_roots_4212_);
lean_dec_ref(v_buckets_4229_);
v___y_4218_ = v___x_4235_;
goto v___jp_4217_;
}
v___jp_4217_:
{
lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; size_t v_sz_4222_; size_t v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4227_; 
v___x_4219_ = lean_unsigned_to_nat(1u);
v___x_4220_ = lean_mk_empty_array_with_capacity(v___x_4219_);
lean_dec_ref(v___x_4220_);
v___x_4221_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0);
v_sz_4222_ = lean_array_size(v_tries_4213_);
v___x_4223_ = ((size_t)0ULL);
v___x_4224_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(v_sz_4222_, v___x_4223_, v_tries_4213_);
v___x_4225_ = l_Array_append___redArg(v___x_4221_, v___x_4224_);
lean_dec_ref(v___x_4224_);
if (v_isShared_4216_ == 0)
{
lean_ctor_set(v___x_4215_, 1, v___y_4218_);
lean_ctor_set(v___x_4215_, 0, v___x_4225_);
v___x_4227_ = v___x_4215_;
goto v_reusejp_4226_;
}
else
{
lean_object* v_reuseFailAlloc_4228_; 
v_reuseFailAlloc_4228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4228_, 0, v___x_4225_);
lean_ctor_set(v_reuseFailAlloc_4228_, 1, v___y_4218_);
v___x_4227_ = v_reuseFailAlloc_4228_;
goto v_reusejp_4226_;
}
v_reusejp_4226_:
{
return v___x_4227_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy(lean_object* v_00_u03b1_4237_, lean_object* v_d_4238_){
_start:
{
lean_object* v___x_4239_; 
v___x_4239_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_d_4238_);
return v___x_4239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0(lean_object* v_00_u03b1_4240_, size_t v_sz_4241_, size_t v_i_4242_, lean_object* v_bs_4243_){
_start:
{
lean_object* v___x_4244_; 
v___x_4244_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(v_sz_4241_, v_i_4242_, v_bs_4243_);
return v___x_4244_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___boxed(lean_object* v_00_u03b1_4245_, lean_object* v_sz_4246_, lean_object* v_i_4247_, lean_object* v_bs_4248_){
_start:
{
size_t v_sz_boxed_4249_; size_t v_i_boxed_4250_; lean_object* v_res_4251_; 
v_sz_boxed_4249_ = lean_unbox_usize(v_sz_4246_);
lean_dec(v_sz_4246_);
v_i_boxed_4250_ = lean_unbox_usize(v_i_4247_);
lean_dec(v_i_4247_);
v_res_4251_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0(v_00_u03b1_4245_, v_sz_boxed_4249_, v_i_boxed_4250_, v_bs_4248_);
return v_res_4251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___lam__0(lean_object* v_y_4252_, lean_object* v_x_4253_){
_start:
{
lean_object* v___x_4254_; 
v___x_4254_ = l_Array_append___redArg(v_x_4253_, v_y_4252_);
return v___x_4254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___lam__0___boxed(lean_object* v_y_4255_, lean_object* v_x_4256_){
_start:
{
lean_object* v_res_4257_; 
v_res_4257_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___lam__0(v_y_4255_, v_x_4256_);
lean_dec_ref(v_y_4255_);
return v_res_4257_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4258_; 
v___x_4258_ = l_Array_instInhabited(lean_box(0));
return v___x_4258_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(lean_object* v_tries_4259_, lean_object* v_snd_4260_, lean_object* v_x_4261_, lean_object* v_x_4262_){
_start:
{
if (lean_obj_tag(v_x_4262_) == 0)
{
lean_dec_ref(v_snd_4260_);
return v_x_4261_;
}
else
{
lean_object* v_key_4263_; lean_object* v_value_4264_; lean_object* v_tail_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; 
v_key_4263_ = lean_ctor_get(v_x_4262_, 0);
lean_inc(v_key_4263_);
v_value_4264_ = lean_ctor_get(v_x_4262_, 1);
lean_inc(v_value_4264_);
v_tail_4265_ = lean_ctor_get(v_x_4262_, 2);
lean_inc(v_tail_4265_);
lean_dec_ref_known(v_x_4262_, 3);
v___x_4266_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0);
v___x_4267_ = lean_array_get_borrowed(v___x_4266_, v_tries_4259_, v_value_4264_);
lean_dec(v_value_4264_);
lean_inc_ref(v_snd_4260_);
lean_inc(v___x_4267_);
v___x_4268_ = lean_apply_1(v_snd_4260_, v___x_4267_);
v___x_4269_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(v_x_4261_, v_key_4263_, v___x_4268_);
v_x_4261_ = v___x_4269_;
v_x_4262_ = v_tail_4265_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___boxed(lean_object* v_tries_4271_, lean_object* v_snd_4272_, lean_object* v_x_4273_, lean_object* v_x_4274_){
_start:
{
lean_object* v_res_4275_; 
v_res_4275_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(v_tries_4271_, v_snd_4272_, v_x_4273_, v_x_4274_);
lean_dec_ref(v_tries_4271_);
return v_res_4275_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(lean_object* v_tries_4276_, lean_object* v_snd_4277_, lean_object* v_as_4278_, size_t v_i_4279_, size_t v_stop_4280_, lean_object* v_b_4281_){
_start:
{
uint8_t v___x_4282_; 
v___x_4282_ = lean_usize_dec_eq(v_i_4279_, v_stop_4280_);
if (v___x_4282_ == 0)
{
lean_object* v___x_4283_; lean_object* v___x_4284_; size_t v___x_4285_; size_t v___x_4286_; 
v___x_4283_ = lean_array_uget_borrowed(v_as_4278_, v_i_4279_);
lean_inc(v___x_4283_);
lean_inc_ref(v_snd_4277_);
v___x_4284_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(v_tries_4276_, v_snd_4277_, v_b_4281_, v___x_4283_);
v___x_4285_ = ((size_t)1ULL);
v___x_4286_ = lean_usize_add(v_i_4279_, v___x_4285_);
v_i_4279_ = v___x_4286_;
v_b_4281_ = v___x_4284_;
goto _start;
}
else
{
lean_dec_ref(v_snd_4277_);
return v_b_4281_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg___boxed(lean_object* v_tries_4288_, lean_object* v_snd_4289_, lean_object* v_as_4290_, lean_object* v_i_4291_, lean_object* v_stop_4292_, lean_object* v_b_4293_){
_start:
{
size_t v_i_boxed_4294_; size_t v_stop_boxed_4295_; lean_object* v_res_4296_; 
v_i_boxed_4294_ = lean_unbox_usize(v_i_4291_);
lean_dec(v_i_4291_);
v_stop_boxed_4295_ = lean_unbox_usize(v_stop_4292_);
lean_dec(v_stop_4292_);
v_res_4296_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(v_tries_4288_, v_snd_4289_, v_as_4290_, v_i_boxed_4294_, v_stop_boxed_4295_, v_b_4293_);
lean_dec_ref(v_as_4290_);
lean_dec_ref(v_tries_4288_);
return v_res_4296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg(lean_object* v_x_4299_, lean_object* v_y_4300_){
_start:
{
lean_object* v_fst_4302_; lean_object* v_buckets_4303_; lean_object* v_tries_4304_; lean_object* v_snd_4305_; lean_object* v_roots_4312_; lean_object* v_roots_4313_; lean_object* v_tries_4314_; lean_object* v_size_4315_; lean_object* v_buckets_4316_; lean_object* v_tries_4317_; lean_object* v_size_4318_; lean_object* v_buckets_4319_; uint8_t v___x_4320_; 
v_roots_4312_ = lean_ctor_get(v_y_4300_, 0);
v_roots_4313_ = lean_ctor_get(v_x_4299_, 0);
v_tries_4314_ = lean_ctor_get(v_y_4300_, 1);
v_size_4315_ = lean_ctor_get(v_roots_4312_, 0);
v_buckets_4316_ = lean_ctor_get(v_roots_4312_, 1);
v_tries_4317_ = lean_ctor_get(v_x_4299_, 1);
v_size_4318_ = lean_ctor_get(v_roots_4313_, 0);
v_buckets_4319_ = lean_ctor_get(v_roots_4313_, 1);
v___x_4320_ = lean_nat_dec_le(v_size_4315_, v_size_4318_);
if (v___x_4320_ == 0)
{
lean_object* v___f_4321_; 
lean_inc_ref(v_buckets_4319_);
lean_inc_ref(v_tries_4317_);
lean_dec_ref(v_x_4299_);
v___f_4321_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___closed__0));
v_fst_4302_ = v_y_4300_;
v_buckets_4303_ = v_buckets_4319_;
v_tries_4304_ = v_tries_4317_;
v_snd_4305_ = v___f_4321_;
goto v___jp_4301_;
}
else
{
lean_object* v___f_4322_; 
lean_inc_ref(v_buckets_4316_);
lean_inc_ref(v_tries_4314_);
lean_dec_ref(v_y_4300_);
v___f_4322_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___closed__1));
v_fst_4302_ = v_x_4299_;
v_buckets_4303_ = v_buckets_4316_;
v_tries_4304_ = v_tries_4314_;
v_snd_4305_ = v___f_4322_;
goto v___jp_4301_;
}
v___jp_4301_:
{
lean_object* v___x_4306_; lean_object* v___x_4307_; uint8_t v___x_4308_; 
v___x_4306_ = lean_unsigned_to_nat(0u);
v___x_4307_ = lean_array_get_size(v_buckets_4303_);
v___x_4308_ = lean_nat_dec_lt(v___x_4306_, v___x_4307_);
if (v___x_4308_ == 0)
{
lean_dec_ref(v_tries_4304_);
lean_dec_ref(v_buckets_4303_);
return v_fst_4302_;
}
else
{
size_t v___x_4309_; size_t v___x_4310_; lean_object* v___x_4311_; 
v___x_4309_ = ((size_t)0ULL);
v___x_4310_ = lean_usize_of_nat(v___x_4307_);
lean_inc_ref(v_snd_4305_);
v___x_4311_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(v_tries_4304_, v_snd_4305_, v_buckets_4303_, v___x_4309_, v___x_4310_, v_fst_4302_);
lean_dec_ref(v_buckets_4303_);
lean_dec_ref(v_tries_4304_);
return v___x_4311_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append(lean_object* v_00_u03b1_4323_, lean_object* v_x_4324_, lean_object* v_y_4325_){
_start:
{
lean_object* v___x_4326_; 
v___x_4326_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg(v_x_4324_, v_y_4325_);
return v___x_4326_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0(lean_object* v_00_u03b1_4327_, lean_object* v_tries_4328_, lean_object* v_snd_4329_, lean_object* v_x_4330_, lean_object* v_x_4331_){
_start:
{
lean_object* v___x_4332_; 
v___x_4332_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(v_tries_4328_, v_snd_4329_, v_x_4330_, v_x_4331_);
return v___x_4332_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___boxed(lean_object* v_00_u03b1_4333_, lean_object* v_tries_4334_, lean_object* v_snd_4335_, lean_object* v_x_4336_, lean_object* v_x_4337_){
_start:
{
lean_object* v_res_4338_; 
v_res_4338_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0(v_00_u03b1_4333_, v_tries_4334_, v_snd_4335_, v_x_4336_, v_x_4337_);
lean_dec_ref(v_tries_4334_);
return v_res_4338_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1(lean_object* v_00_u03b1_4339_, lean_object* v_tries_4340_, lean_object* v_snd_4341_, lean_object* v_as_4342_, size_t v_i_4343_, size_t v_stop_4344_, lean_object* v_b_4345_){
_start:
{
lean_object* v___x_4346_; 
v___x_4346_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(v_tries_4340_, v_snd_4341_, v_as_4342_, v_i_4343_, v_stop_4344_, v_b_4345_);
return v___x_4346_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___boxed(lean_object* v_00_u03b1_4347_, lean_object* v_tries_4348_, lean_object* v_snd_4349_, lean_object* v_as_4350_, lean_object* v_i_4351_, lean_object* v_stop_4352_, lean_object* v_b_4353_){
_start:
{
size_t v_i_boxed_4354_; size_t v_stop_boxed_4355_; lean_object* v_res_4356_; 
v_i_boxed_4354_ = lean_unbox_usize(v_i_4351_);
lean_dec(v_i_4351_);
v_stop_boxed_4355_ = lean_unbox_usize(v_stop_4352_);
lean_dec(v_stop_4352_);
v_res_4356_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1(v_00_u03b1_4347_, v_tries_4348_, v_snd_4349_, v_as_4350_, v_i_boxed_4354_, v_stop_boxed_4355_, v_b_4353_);
lean_dec_ref(v_as_4350_);
lean_dec_ref(v_tries_4348_);
return v_res_4356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend(lean_object* v_00_u03b1_4358_){
_start:
{
lean_object* v___x_4359_; 
v___x_4359_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend___closed__0));
return v___x_4359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(lean_object* v_expr_4360_, lean_object* v_value_4361_, lean_object* v_a_4362_, lean_object* v_a_4363_, lean_object* v_a_4364_, lean_object* v_a_4365_){
_start:
{
lean_object* v___x_4367_; 
v___x_4367_ = l_Lean_Meta_LazyDiscrTree_rootKey(v_expr_4360_, v_a_4362_, v_a_4363_, v_a_4364_, v_a_4365_);
if (lean_obj_tag(v___x_4367_) == 0)
{
lean_object* v_a_4368_; lean_object* v___x_4370_; uint8_t v_isShared_4371_; uint8_t v_isSharedCheck_4389_; 
v_a_4368_ = lean_ctor_get(v___x_4367_, 0);
v_isSharedCheck_4389_ = !lean_is_exclusive(v___x_4367_);
if (v_isSharedCheck_4389_ == 0)
{
v___x_4370_ = v___x_4367_;
v_isShared_4371_ = v_isSharedCheck_4389_;
goto v_resetjp_4369_;
}
else
{
lean_inc(v_a_4368_);
lean_dec(v___x_4367_);
v___x_4370_ = lean_box(0);
v_isShared_4371_ = v_isSharedCheck_4389_;
goto v_resetjp_4369_;
}
v_resetjp_4369_:
{
lean_object* v_fst_4372_; lean_object* v_snd_4373_; lean_object* v___x_4375_; uint8_t v_isShared_4376_; uint8_t v_isSharedCheck_4388_; 
v_fst_4372_ = lean_ctor_get(v_a_4368_, 0);
v_snd_4373_ = lean_ctor_get(v_a_4368_, 1);
v_isSharedCheck_4388_ = !lean_is_exclusive(v_a_4368_);
if (v_isSharedCheck_4388_ == 0)
{
v___x_4375_ = v_a_4368_;
v_isShared_4376_ = v_isSharedCheck_4388_;
goto v_resetjp_4374_;
}
else
{
lean_inc(v_snd_4373_);
lean_inc(v_fst_4372_);
lean_dec(v_a_4368_);
v___x_4375_ = lean_box(0);
v_isShared_4376_ = v_isSharedCheck_4388_;
goto v_resetjp_4374_;
}
v_resetjp_4374_:
{
lean_object* v_lctx_4377_; lean_object* v_localInstances_4378_; lean_object* v___x_4380_; 
v_lctx_4377_ = lean_ctor_get(v_a_4362_, 2);
v_localInstances_4378_ = lean_ctor_get(v_a_4362_, 3);
lean_inc_ref(v_localInstances_4378_);
lean_inc_ref(v_lctx_4377_);
if (v_isShared_4376_ == 0)
{
lean_ctor_set(v___x_4375_, 1, v_localInstances_4378_);
lean_ctor_set(v___x_4375_, 0, v_lctx_4377_);
v___x_4380_ = v___x_4375_;
goto v_reusejp_4379_;
}
else
{
lean_object* v_reuseFailAlloc_4387_; 
v_reuseFailAlloc_4387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4387_, 0, v_lctx_4377_);
lean_ctor_set(v_reuseFailAlloc_4387_, 1, v_localInstances_4378_);
v___x_4380_ = v_reuseFailAlloc_4387_;
goto v_reusejp_4379_;
}
v_reusejp_4379_:
{
lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4385_; 
v___x_4381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4381_, 0, v___x_4380_);
lean_ctor_set(v___x_4381_, 1, v_value_4361_);
v___x_4382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4382_, 0, v_snd_4373_);
lean_ctor_set(v___x_4382_, 1, v___x_4381_);
v___x_4383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4383_, 0, v_fst_4372_);
lean_ctor_set(v___x_4383_, 1, v___x_4382_);
if (v_isShared_4371_ == 0)
{
lean_ctor_set(v___x_4370_, 0, v___x_4383_);
v___x_4385_ = v___x_4370_;
goto v_reusejp_4384_;
}
else
{
lean_object* v_reuseFailAlloc_4386_; 
v_reuseFailAlloc_4386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4386_, 0, v___x_4383_);
v___x_4385_ = v_reuseFailAlloc_4386_;
goto v_reusejp_4384_;
}
v_reusejp_4384_:
{
return v___x_4385_;
}
}
}
}
}
else
{
lean_object* v_a_4390_; lean_object* v___x_4392_; uint8_t v_isShared_4393_; uint8_t v_isSharedCheck_4397_; 
lean_dec(v_value_4361_);
v_a_4390_ = lean_ctor_get(v___x_4367_, 0);
v_isSharedCheck_4397_ = !lean_is_exclusive(v___x_4367_);
if (v_isSharedCheck_4397_ == 0)
{
v___x_4392_ = v___x_4367_;
v_isShared_4393_ = v_isSharedCheck_4397_;
goto v_resetjp_4391_;
}
else
{
lean_inc(v_a_4390_);
lean_dec(v___x_4367_);
v___x_4392_ = lean_box(0);
v_isShared_4393_ = v_isSharedCheck_4397_;
goto v_resetjp_4391_;
}
v_resetjp_4391_:
{
lean_object* v___x_4395_; 
if (v_isShared_4393_ == 0)
{
v___x_4395_ = v___x_4392_;
goto v_reusejp_4394_;
}
else
{
lean_object* v_reuseFailAlloc_4396_; 
v_reuseFailAlloc_4396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4396_, 0, v_a_4390_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg___boxed(lean_object* v_expr_4398_, lean_object* v_value_4399_, lean_object* v_a_4400_, lean_object* v_a_4401_, lean_object* v_a_4402_, lean_object* v_a_4403_, lean_object* v_a_4404_){
_start:
{
lean_object* v_res_4405_; 
v_res_4405_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(v_expr_4398_, v_value_4399_, v_a_4400_, v_a_4401_, v_a_4402_, v_a_4403_);
lean_dec(v_a_4403_);
lean_dec_ref(v_a_4402_);
lean_dec(v_a_4401_);
lean_dec_ref(v_a_4400_);
return v_res_4405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr(lean_object* v_00_u03b1_4406_, lean_object* v_expr_4407_, lean_object* v_value_4408_, lean_object* v_a_4409_, lean_object* v_a_4410_, lean_object* v_a_4411_, lean_object* v_a_4412_){
_start:
{
lean_object* v___x_4414_; 
v___x_4414_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(v_expr_4407_, v_value_4408_, v_a_4409_, v_a_4410_, v_a_4411_, v_a_4412_);
return v___x_4414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___boxed(lean_object* v_00_u03b1_4415_, lean_object* v_expr_4416_, lean_object* v_value_4417_, lean_object* v_a_4418_, lean_object* v_a_4419_, lean_object* v_a_4420_, lean_object* v_a_4421_, lean_object* v_a_4422_){
_start:
{
lean_object* v_res_4423_; 
v_res_4423_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr(v_00_u03b1_4415_, v_expr_4416_, v_value_4417_, v_a_4418_, v_a_4419_, v_a_4420_, v_a_4421_);
lean_dec(v_a_4421_);
lean_dec_ref(v_a_4420_);
lean_dec(v_a_4419_);
lean_dec_ref(v_a_4418_);
return v_res_4423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(lean_object* v_e_4424_, lean_object* v_idx_4425_, lean_object* v_value_4426_, lean_object* v_a_4427_, lean_object* v_a_4428_, lean_object* v_a_4429_, lean_object* v_a_4430_){
_start:
{
lean_object* v_entry_4432_; lean_object* v___x_4434_; uint8_t v_isShared_4435_; uint8_t v_isSharedCheck_4478_; 
v_entry_4432_ = lean_ctor_get(v_e_4424_, 1);
v_isSharedCheck_4478_ = !lean_is_exclusive(v_e_4424_);
if (v_isSharedCheck_4478_ == 0)
{
lean_object* v_unused_4479_; 
v_unused_4479_ = lean_ctor_get(v_e_4424_, 0);
lean_dec(v_unused_4479_);
v___x_4434_ = v_e_4424_;
v_isShared_4435_ = v_isSharedCheck_4478_;
goto v_resetjp_4433_;
}
else
{
lean_inc(v_entry_4432_);
lean_dec(v_e_4424_);
v___x_4434_ = lean_box(0);
v_isShared_4435_ = v_isSharedCheck_4478_;
goto v_resetjp_4433_;
}
v_resetjp_4433_:
{
lean_object* v_snd_4436_; lean_object* v_fst_4437_; lean_object* v_fst_4438_; lean_object* v___x_4440_; uint8_t v_isShared_4441_; uint8_t v_isSharedCheck_4476_; 
v_snd_4436_ = lean_ctor_get(v_entry_4432_, 1);
lean_inc(v_snd_4436_);
v_fst_4437_ = lean_ctor_get(v_entry_4432_, 0);
lean_inc(v_fst_4437_);
lean_dec_ref(v_entry_4432_);
v_fst_4438_ = lean_ctor_get(v_snd_4436_, 0);
v_isSharedCheck_4476_ = !lean_is_exclusive(v_snd_4436_);
if (v_isSharedCheck_4476_ == 0)
{
lean_object* v_unused_4477_; 
v_unused_4477_ = lean_ctor_get(v_snd_4436_, 1);
lean_dec(v_unused_4477_);
v___x_4440_ = v_snd_4436_;
v_isShared_4441_ = v_isSharedCheck_4476_;
goto v_resetjp_4439_;
}
else
{
lean_inc(v_fst_4438_);
lean_dec(v_snd_4436_);
v___x_4440_ = lean_box(0);
v_isShared_4441_ = v_isSharedCheck_4476_;
goto v_resetjp_4439_;
}
v_resetjp_4439_:
{
lean_object* v___x_4442_; lean_object* v___x_4443_; lean_object* v___x_4444_; 
v___x_4442_ = l_Lean_instInhabitedExpr;
v___x_4443_ = lean_array_get(v___x_4442_, v_fst_4437_, v_idx_4425_);
lean_dec(v_fst_4437_);
v___x_4444_ = l_Lean_Meta_LazyDiscrTree_rootKey(v___x_4443_, v_a_4427_, v_a_4428_, v_a_4429_, v_a_4430_);
if (lean_obj_tag(v___x_4444_) == 0)
{
lean_object* v_a_4445_; lean_object* v___x_4447_; uint8_t v_isShared_4448_; uint8_t v_isSharedCheck_4467_; 
v_a_4445_ = lean_ctor_get(v___x_4444_, 0);
v_isSharedCheck_4467_ = !lean_is_exclusive(v___x_4444_);
if (v_isSharedCheck_4467_ == 0)
{
v___x_4447_ = v___x_4444_;
v_isShared_4448_ = v_isSharedCheck_4467_;
goto v_resetjp_4446_;
}
else
{
lean_inc(v_a_4445_);
lean_dec(v___x_4444_);
v___x_4447_ = lean_box(0);
v_isShared_4448_ = v_isSharedCheck_4467_;
goto v_resetjp_4446_;
}
v_resetjp_4446_:
{
lean_object* v_fst_4449_; lean_object* v_snd_4450_; lean_object* v___x_4452_; uint8_t v_isShared_4453_; uint8_t v_isSharedCheck_4466_; 
v_fst_4449_ = lean_ctor_get(v_a_4445_, 0);
v_snd_4450_ = lean_ctor_get(v_a_4445_, 1);
v_isSharedCheck_4466_ = !lean_is_exclusive(v_a_4445_);
if (v_isSharedCheck_4466_ == 0)
{
v___x_4452_ = v_a_4445_;
v_isShared_4453_ = v_isSharedCheck_4466_;
goto v_resetjp_4451_;
}
else
{
lean_inc(v_snd_4450_);
lean_inc(v_fst_4449_);
lean_dec(v_a_4445_);
v___x_4452_ = lean_box(0);
v_isShared_4453_ = v_isSharedCheck_4466_;
goto v_resetjp_4451_;
}
v_resetjp_4451_:
{
lean_object* v___x_4455_; 
if (v_isShared_4453_ == 0)
{
lean_ctor_set(v___x_4452_, 1, v_value_4426_);
lean_ctor_set(v___x_4452_, 0, v_fst_4438_);
v___x_4455_ = v___x_4452_;
goto v_reusejp_4454_;
}
else
{
lean_object* v_reuseFailAlloc_4465_; 
v_reuseFailAlloc_4465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4465_, 0, v_fst_4438_);
lean_ctor_set(v_reuseFailAlloc_4465_, 1, v_value_4426_);
v___x_4455_ = v_reuseFailAlloc_4465_;
goto v_reusejp_4454_;
}
v_reusejp_4454_:
{
lean_object* v___x_4457_; 
if (v_isShared_4441_ == 0)
{
lean_ctor_set(v___x_4440_, 1, v___x_4455_);
lean_ctor_set(v___x_4440_, 0, v_snd_4450_);
v___x_4457_ = v___x_4440_;
goto v_reusejp_4456_;
}
else
{
lean_object* v_reuseFailAlloc_4464_; 
v_reuseFailAlloc_4464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4464_, 0, v_snd_4450_);
lean_ctor_set(v_reuseFailAlloc_4464_, 1, v___x_4455_);
v___x_4457_ = v_reuseFailAlloc_4464_;
goto v_reusejp_4456_;
}
v_reusejp_4456_:
{
lean_object* v___x_4459_; 
if (v_isShared_4435_ == 0)
{
lean_ctor_set(v___x_4434_, 1, v___x_4457_);
lean_ctor_set(v___x_4434_, 0, v_fst_4449_);
v___x_4459_ = v___x_4434_;
goto v_reusejp_4458_;
}
else
{
lean_object* v_reuseFailAlloc_4463_; 
v_reuseFailAlloc_4463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4463_, 0, v_fst_4449_);
lean_ctor_set(v_reuseFailAlloc_4463_, 1, v___x_4457_);
v___x_4459_ = v_reuseFailAlloc_4463_;
goto v_reusejp_4458_;
}
v_reusejp_4458_:
{
lean_object* v___x_4461_; 
if (v_isShared_4448_ == 0)
{
lean_ctor_set(v___x_4447_, 0, v___x_4459_);
v___x_4461_ = v___x_4447_;
goto v_reusejp_4460_;
}
else
{
lean_object* v_reuseFailAlloc_4462_; 
v_reuseFailAlloc_4462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4462_, 0, v___x_4459_);
v___x_4461_ = v_reuseFailAlloc_4462_;
goto v_reusejp_4460_;
}
v_reusejp_4460_:
{
return v___x_4461_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4468_; lean_object* v___x_4470_; uint8_t v_isShared_4471_; uint8_t v_isSharedCheck_4475_; 
lean_del_object(v___x_4440_);
lean_dec(v_fst_4438_);
lean_del_object(v___x_4434_);
lean_dec(v_value_4426_);
v_a_4468_ = lean_ctor_get(v___x_4444_, 0);
v_isSharedCheck_4475_ = !lean_is_exclusive(v___x_4444_);
if (v_isSharedCheck_4475_ == 0)
{
v___x_4470_ = v___x_4444_;
v_isShared_4471_ = v_isSharedCheck_4475_;
goto v_resetjp_4469_;
}
else
{
lean_inc(v_a_4468_);
lean_dec(v___x_4444_);
v___x_4470_ = lean_box(0);
v_isShared_4471_ = v_isSharedCheck_4475_;
goto v_resetjp_4469_;
}
v_resetjp_4469_:
{
lean_object* v___x_4473_; 
if (v_isShared_4471_ == 0)
{
v___x_4473_ = v___x_4470_;
goto v_reusejp_4472_;
}
else
{
lean_object* v_reuseFailAlloc_4474_; 
v_reuseFailAlloc_4474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4474_, 0, v_a_4468_);
v___x_4473_ = v_reuseFailAlloc_4474_;
goto v_reusejp_4472_;
}
v_reusejp_4472_:
{
return v___x_4473_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg___boxed(lean_object* v_e_4480_, lean_object* v_idx_4481_, lean_object* v_value_4482_, lean_object* v_a_4483_, lean_object* v_a_4484_, lean_object* v_a_4485_, lean_object* v_a_4486_, lean_object* v_a_4487_){
_start:
{
lean_object* v_res_4488_; 
v_res_4488_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(v_e_4480_, v_idx_4481_, v_value_4482_, v_a_4483_, v_a_4484_, v_a_4485_, v_a_4486_);
lean_dec(v_a_4486_);
lean_dec_ref(v_a_4485_);
lean_dec(v_a_4484_);
lean_dec_ref(v_a_4483_);
lean_dec(v_idx_4481_);
return v_res_4488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry(lean_object* v_00_u03b1_4489_, lean_object* v_e_4490_, lean_object* v_idx_4491_, lean_object* v_value_4492_, lean_object* v_a_4493_, lean_object* v_a_4494_, lean_object* v_a_4495_, lean_object* v_a_4496_){
_start:
{
lean_object* v___x_4498_; 
v___x_4498_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(v_e_4490_, v_idx_4491_, v_value_4492_, v_a_4493_, v_a_4494_, v_a_4495_, v_a_4496_);
return v___x_4498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___boxed(lean_object* v_00_u03b1_4499_, lean_object* v_e_4500_, lean_object* v_idx_4501_, lean_object* v_value_4502_, lean_object* v_a_4503_, lean_object* v_a_4504_, lean_object* v_a_4505_, lean_object* v_a_4506_, lean_object* v_a_4507_){
_start:
{
lean_object* v_res_4508_; 
v_res_4508_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry(v_00_u03b1_4499_, v_e_4500_, v_idx_4501_, v_value_4502_, v_a_4503_, v_a_4504_, v_a_4505_, v_a_4506_);
lean_dec(v_a_4506_);
lean_dec_ref(v_a_4505_);
lean_dec(v_a_4504_);
lean_dec_ref(v_a_4503_);
lean_dec(v_idx_4501_);
return v_res_4508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_ImportData_new(){
_start:
{
lean_object* v___x_4512_; lean_object* v___x_4513_; 
v___x_4512_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_ImportData_new___closed__0));
v___x_4513_ = lean_st_mk_ref(v___x_4512_);
return v___x_4513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_ImportData_new___boxed(lean_object* v_a_4514_){
_start:
{
lean_object* v_res_4515_; 
v_res_4515_ = l_Lean_Meta_LazyDiscrTree_ImportData_new();
return v_res_4515_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0(void){
_start:
{
lean_object* v___x_4516_; 
v___x_4516_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4516_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1(void){
_start:
{
lean_object* v___x_4517_; lean_object* v___x_4518_; 
v___x_4517_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0);
v___x_4518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4518_, 0, v___x_4517_);
return v___x_4518_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2(void){
_start:
{
lean_object* v___x_4519_; lean_object* v___x_4520_; 
v___x_4519_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1);
v___x_4520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4520_, 0, v___x_4519_);
lean_ctor_set(v___x_4520_, 1, v___x_4519_);
return v___x_4520_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3(void){
_start:
{
lean_object* v___x_4521_; lean_object* v___x_4522_; 
v___x_4521_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1);
v___x_4522_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4522_, 0, v___x_4521_);
lean_ctor_set(v___x_4522_, 1, v___x_4521_);
lean_ctor_set(v___x_4522_, 2, v___x_4521_);
lean_ctor_set(v___x_4522_, 3, v___x_4521_);
lean_ctor_set(v___x_4522_, 4, v___x_4521_);
lean_ctor_set(v___x_4522_, 5, v___x_4521_);
return v___x_4522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Cache_empty(lean_object* v_ngen_4523_){
_start:
{
lean_object* v___x_4524_; lean_object* v___x_4525_; lean_object* v___x_4526_; 
v___x_4524_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2);
v___x_4525_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3);
v___x_4526_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4526_, 0, v_ngen_4523_);
lean_ctor_set(v___x_4526_, 1, v___x_4524_);
lean_ctor_set(v___x_4526_, 2, v___x_4525_);
return v___x_4526_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName(lean_object* v_env_4527_, lean_object* v_declName_4528_){
_start:
{
uint8_t v___x_4529_; 
v___x_4529_ = l_Lean_isPrivateName(v_declName_4528_);
if (v___x_4529_ == 0)
{
return v___x_4529_;
}
else
{
lean_object* v___x_4530_; 
v___x_4530_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4527_, v_declName_4528_);
if (lean_obj_tag(v___x_4530_) == 0)
{
return v___x_4529_;
}
else
{
lean_object* v_val_4531_; lean_object* v___x_4532_; uint8_t v_isModule_4533_; lean_object* v_modules_4534_; uint8_t v___x_4535_; 
v_val_4531_ = lean_ctor_get(v___x_4530_, 0);
lean_inc(v_val_4531_);
lean_dec_ref_known(v___x_4530_, 1);
v___x_4532_ = l_Lean_Environment_header(v_env_4527_);
v_isModule_4533_ = lean_ctor_get_uint8(v___x_4532_, sizeof(void*)*7 + 4);
v_modules_4534_ = lean_ctor_get(v___x_4532_, 3);
lean_inc_ref(v_modules_4534_);
lean_dec_ref(v___x_4532_);
v___x_4535_ = 0;
if (v_isModule_4533_ == 0)
{
lean_dec_ref(v_modules_4534_);
lean_dec(v_val_4531_);
return v___x_4535_;
}
else
{
lean_object* v___x_4536_; uint8_t v___x_4537_; 
v___x_4536_ = lean_array_get_size(v_modules_4534_);
v___x_4537_ = lean_nat_dec_lt(v_val_4531_, v___x_4536_);
if (v___x_4537_ == 0)
{
lean_dec_ref(v_modules_4534_);
lean_dec(v_val_4531_);
return v___x_4535_;
}
else
{
lean_object* v___x_4538_; lean_object* v_toImport_4539_; uint8_t v_importAll_4540_; 
v___x_4538_ = lean_array_fget(v_modules_4534_, v_val_4531_);
lean_dec(v_val_4531_);
lean_dec_ref(v_modules_4534_);
v_toImport_4539_ = lean_ctor_get(v___x_4538_, 0);
lean_inc_ref(v_toImport_4539_);
lean_dec(v___x_4538_);
v_importAll_4540_ = lean_ctor_get_uint8(v_toImport_4539_, sizeof(void*)*1);
lean_dec_ref(v_toImport_4539_);
return v_importAll_4540_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName___boxed(lean_object* v_env_4541_, lean_object* v_declName_4542_){
_start:
{
uint8_t v_res_4543_; lean_object* v_r_4544_; 
v_res_4543_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName(v_env_4541_, v_declName_4542_);
lean_dec(v_declName_4542_);
lean_dec_ref(v_env_4541_);
v_r_4544_ = lean_box(v_res_4543_);
return v_r_4544_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_LazyDiscrTree_blacklistInsertion(lean_object* v_env_4550_, lean_object* v_declName_4551_){
_start:
{
uint8_t v___x_4552_; 
lean_inc(v_declName_4551_);
lean_inc_ref(v_env_4550_);
v___x_4552_ = l_Lean_Meta_allowCompletion(v_env_4550_, v_declName_4551_);
if (v___x_4552_ == 0)
{
uint8_t v___x_4553_; 
lean_dec(v_declName_4551_);
lean_dec_ref(v_env_4550_);
v___x_4553_ = 1;
return v___x_4553_;
}
else
{
lean_object* v___x_4554_; uint8_t v___x_4555_; uint8_t v___y_4565_; 
v___x_4554_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__1));
v___x_4555_ = lean_name_eq(v_declName_4551_, v___x_4554_);
if (v___x_4555_ == 0)
{
uint8_t v___x_4566_; 
lean_inc(v_declName_4551_);
v___x_4566_ = l_Lean_Name_isInternalDetail(v_declName_4551_);
if (v___x_4566_ == 0)
{
lean_dec_ref(v_env_4550_);
v___y_4565_ = v___x_4566_;
goto v___jp_4564_;
}
else
{
uint8_t v___x_4567_; 
v___x_4567_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName(v_env_4550_, v_declName_4551_);
lean_dec_ref(v_env_4550_);
if (v___x_4567_ == 0)
{
v___y_4565_ = v___x_4566_;
goto v___jp_4564_;
}
else
{
goto v___jp_4560_;
}
}
}
else
{
lean_dec(v_declName_4551_);
lean_dec_ref(v_env_4550_);
return v___x_4555_;
}
v___jp_4556_:
{
if (lean_obj_tag(v_declName_4551_) == 1)
{
lean_object* v_str_4557_; lean_object* v___x_4558_; uint8_t v___x_4559_; 
v_str_4557_ = lean_ctor_get(v_declName_4551_, 1);
lean_inc_ref(v_str_4557_);
lean_dec_ref_known(v_declName_4551_, 2);
v___x_4558_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__2));
v___x_4559_ = lean_string_dec_eq(v_str_4557_, v___x_4558_);
lean_dec_ref(v_str_4557_);
return v___x_4559_;
}
else
{
lean_dec(v_declName_4551_);
return v___x_4555_;
}
}
v___jp_4560_:
{
if (lean_obj_tag(v_declName_4551_) == 1)
{
lean_object* v_str_4561_; lean_object* v___x_4562_; uint8_t v___x_4563_; 
v_str_4561_ = lean_ctor_get(v_declName_4551_, 1);
v___x_4562_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__3));
v___x_4563_ = lean_string_dec_eq(v_str_4561_, v___x_4562_);
if (v___x_4563_ == 0)
{
goto v___jp_4556_;
}
else
{
lean_dec_ref_known(v_declName_4551_, 2);
return v___x_4563_;
}
}
else
{
goto v___jp_4556_;
}
}
v___jp_4564_:
{
if (v___y_4565_ == 0)
{
goto v___jp_4560_;
}
else
{
lean_dec(v_declName_4551_);
return v___y_4565_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_blacklistInsertion___boxed(lean_object* v_env_4568_, lean_object* v_declName_4569_){
_start:
{
uint8_t v_res_4570_; lean_object* v_r_4571_; 
v_res_4570_ = l_Lean_Meta_LazyDiscrTree_blacklistInsertion(v_env_4568_, v_declName_4569_);
v_r_4571_ = lean_box(v_res_4570_);
return v_r_4571_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(lean_object* v_opts_4572_, lean_object* v_opt_4573_){
_start:
{
lean_object* v_name_4574_; lean_object* v_defValue_4575_; lean_object* v_map_4576_; lean_object* v___x_4577_; 
v_name_4574_ = lean_ctor_get(v_opt_4573_, 0);
v_defValue_4575_ = lean_ctor_get(v_opt_4573_, 1);
v_map_4576_ = lean_ctor_get(v_opts_4572_, 0);
v___x_4577_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4576_, v_name_4574_);
if (lean_obj_tag(v___x_4577_) == 0)
{
uint8_t v___x_4578_; 
v___x_4578_ = lean_unbox(v_defValue_4575_);
return v___x_4578_;
}
else
{
lean_object* v_val_4579_; 
v_val_4579_ = lean_ctor_get(v___x_4577_, 0);
lean_inc(v_val_4579_);
lean_dec_ref_known(v___x_4577_, 1);
if (lean_obj_tag(v_val_4579_) == 1)
{
uint8_t v_v_4580_; 
v_v_4580_ = lean_ctor_get_uint8(v_val_4579_, 0);
lean_dec_ref_known(v_val_4579_, 0);
return v_v_4580_;
}
else
{
uint8_t v___x_4581_; 
lean_dec(v_val_4579_);
v___x_4581_ = lean_unbox(v_defValue_4575_);
return v___x_4581_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0___boxed(lean_object* v_opts_4582_, lean_object* v_opt_4583_){
_start:
{
uint8_t v_res_4584_; lean_object* v_r_4585_; 
v_res_4584_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(v_opts_4582_, v_opt_4583_);
lean_dec_ref(v_opt_4583_);
lean_dec_ref(v_opts_4582_);
v_r_4585_ = lean_box(v_res_4584_);
return v_r_4585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1(lean_object* v_opts_4586_, lean_object* v_opt_4587_){
_start:
{
lean_object* v_name_4588_; lean_object* v_defValue_4589_; lean_object* v_map_4590_; lean_object* v___x_4591_; 
v_name_4588_ = lean_ctor_get(v_opt_4587_, 0);
v_defValue_4589_ = lean_ctor_get(v_opt_4587_, 1);
v_map_4590_ = lean_ctor_get(v_opts_4586_, 0);
v___x_4591_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4590_, v_name_4588_);
if (lean_obj_tag(v___x_4591_) == 0)
{
lean_inc(v_defValue_4589_);
return v_defValue_4589_;
}
else
{
lean_object* v_val_4592_; 
v_val_4592_ = lean_ctor_get(v___x_4591_, 0);
lean_inc(v_val_4592_);
lean_dec_ref_known(v___x_4591_, 1);
if (lean_obj_tag(v_val_4592_) == 3)
{
lean_object* v_v_4593_; 
v_v_4593_ = lean_ctor_get(v_val_4592_, 0);
lean_inc(v_v_4593_);
lean_dec_ref_known(v_val_4592_, 1);
return v_v_4593_;
}
else
{
lean_dec(v_val_4592_);
lean_inc(v_defValue_4589_);
return v_defValue_4589_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1___boxed(lean_object* v_opts_4594_, lean_object* v_opt_4595_){
_start:
{
lean_object* v_res_4596_; 
v_res_4596_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1(v_opts_4594_, v_opt_4595_);
lean_dec_ref(v_opt_4595_);
lean_dec_ref(v_opts_4594_);
return v_res_4596_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg(lean_object* v_as_4597_, size_t v_i_4598_, size_t v_stop_4599_, lean_object* v_b_4600_){
_start:
{
uint8_t v___x_4601_; 
v___x_4601_ = lean_usize_dec_eq(v_i_4598_, v_stop_4599_);
if (v___x_4601_ == 0)
{
lean_object* v___x_4602_; lean_object* v_key_4603_; lean_object* v_entry_4604_; lean_object* v___x_4605_; size_t v___x_4606_; size_t v___x_4607_; 
v___x_4602_ = lean_array_uget_borrowed(v_as_4597_, v_i_4598_);
v_key_4603_ = lean_ctor_get(v___x_4602_, 0);
v_entry_4604_ = lean_ctor_get(v___x_4602_, 1);
lean_inc_ref(v_entry_4604_);
lean_inc(v_key_4603_);
v___x_4605_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg(v_b_4600_, v_key_4603_, v_entry_4604_);
v___x_4606_ = ((size_t)1ULL);
v___x_4607_ = lean_usize_add(v_i_4598_, v___x_4606_);
v_i_4598_ = v___x_4607_;
v_b_4600_ = v___x_4605_;
goto _start;
}
else
{
return v_b_4600_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg___boxed(lean_object* v_as_4609_, lean_object* v_i_4610_, lean_object* v_stop_4611_, lean_object* v_b_4612_){
_start:
{
size_t v_i_boxed_4613_; size_t v_stop_boxed_4614_; lean_object* v_res_4615_; 
v_i_boxed_4613_ = lean_unbox_usize(v_i_4610_);
lean_dec(v_i_4610_);
v_stop_boxed_4614_ = lean_unbox_usize(v_stop_4611_);
lean_dec(v_stop_4611_);
v_res_4615_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg(v_as_4609_, v_i_boxed_4613_, v_stop_boxed_4614_, v_b_4612_);
lean_dec_ref(v_as_4609_);
return v_res_4615_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0(void){
_start:
{
lean_object* v___x_4616_; 
v___x_4616_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4616_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1(void){
_start:
{
lean_object* v___x_4617_; lean_object* v___x_4618_; 
v___x_4617_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0);
v___x_4618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4618_, 0, v___x_4617_);
return v___x_4618_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2(void){
_start:
{
lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; 
v___x_4619_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4620_ = lean_unsigned_to_nat(0u);
v___x_4621_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_4621_, 0, v___x_4620_);
lean_ctor_set(v___x_4621_, 1, v___x_4620_);
lean_ctor_set(v___x_4621_, 2, v___x_4620_);
lean_ctor_set(v___x_4621_, 3, v___x_4620_);
lean_ctor_set(v___x_4621_, 4, v___x_4619_);
lean_ctor_set(v___x_4621_, 5, v___x_4619_);
lean_ctor_set(v___x_4621_, 6, v___x_4619_);
lean_ctor_set(v___x_4621_, 7, v___x_4619_);
lean_ctor_set(v___x_4621_, 8, v___x_4619_);
lean_ctor_set(v___x_4621_, 9, v___x_4619_);
lean_ctor_set(v___x_4621_, 10, v___x_4619_);
return v___x_4621_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3(void){
_start:
{
lean_object* v___x_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; 
v___x_4622_ = lean_unsigned_to_nat(32u);
v___x_4623_ = lean_mk_empty_array_with_capacity(v___x_4622_);
v___x_4624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4624_, 0, v___x_4623_);
return v___x_4624_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4(void){
_start:
{
size_t v___x_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; lean_object* v___x_4630_; 
v___x_4625_ = ((size_t)5ULL);
v___x_4626_ = lean_unsigned_to_nat(0u);
v___x_4627_ = lean_unsigned_to_nat(32u);
v___x_4628_ = lean_mk_empty_array_with_capacity(v___x_4627_);
v___x_4629_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3);
v___x_4630_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4630_, 0, v___x_4629_);
lean_ctor_set(v___x_4630_, 1, v___x_4628_);
lean_ctor_set(v___x_4630_, 2, v___x_4626_);
lean_ctor_set(v___x_4630_, 3, v___x_4626_);
lean_ctor_set_usize(v___x_4630_, 4, v___x_4625_);
return v___x_4630_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5(void){
_start:
{
lean_object* v___x_4631_; lean_object* v___x_4632_; 
v___x_4631_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4632_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4632_, 0, v___x_4631_);
lean_ctor_set(v___x_4632_, 1, v___x_4631_);
lean_ctor_set(v___x_4632_, 2, v___x_4631_);
lean_ctor_set(v___x_4632_, 3, v___x_4631_);
lean_ctor_set(v___x_4632_, 4, v___x_4631_);
return v___x_4632_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6(void){
_start:
{
lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; lean_object* v___x_4636_; 
v___x_4633_ = lean_box(1);
v___x_4634_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4635_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4636_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4636_, 0, v___x_4635_);
lean_ctor_set(v___x_4636_, 1, v___x_4634_);
lean_ctor_set(v___x_4636_, 2, v___x_4633_);
return v___x_4636_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__8(void){
_start:
{
lean_object* v___x_4639_; lean_object* v___x_4640_; lean_object* v___x_4641_; 
v___x_4639_ = lean_unsigned_to_nat(1u);
v___x_4640_ = l_Lean_firstFrontendMacroScope;
v___x_4641_ = lean_nat_add(v___x_4640_, v___x_4639_);
return v___x_4641_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10(void){
_start:
{
lean_object* v___x_4646_; uint64_t v___x_4647_; lean_object* v___x_4648_; 
v___x_4646_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4647_ = 0ULL;
v___x_4648_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4648_, 0, v___x_4646_);
lean_ctor_set_uint64(v___x_4648_, sizeof(void*)*1, v___x_4647_);
return v___x_4648_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11(void){
_start:
{
lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; 
v___x_4649_ = l_Lean_NameSet_empty;
v___x_4650_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4651_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4651_, 0, v___x_4650_);
lean_ctor_set(v___x_4651_, 1, v___x_4650_);
lean_ctor_set(v___x_4651_, 2, v___x_4649_);
return v___x_4651_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12(void){
_start:
{
lean_object* v___x_4652_; lean_object* v___x_4653_; uint8_t v___x_4654_; lean_object* v___x_4655_; 
v___x_4652_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4653_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4654_ = 1;
v___x_4655_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4655_, 0, v___x_4653_);
lean_ctor_set(v___x_4655_, 1, v___x_4653_);
lean_ctor_set(v___x_4655_, 2, v___x_4652_);
lean_ctor_set_uint8(v___x_4655_, sizeof(void*)*3, v___x_4654_);
return v___x_4655_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13(void){
_start:
{
lean_object* v___x_4656_; lean_object* v___x_4657_; 
v___x_4656_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4657_, 0, v___x_4656_);
lean_ctor_set(v___x_4657_, 1, v___x_4656_);
return v___x_4657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(lean_object* v_cctx_4658_, lean_object* v_env_4659_, lean_object* v_modName_4660_, lean_object* v_d_4661_, lean_object* v_cacheRef_4662_, lean_object* v_tree_4663_, lean_object* v_act_4664_, lean_object* v_c_4665_){
_start:
{
uint8_t v___x_4667_; 
lean_inc_ref(v_c_4665_);
v___x_4667_ = l_Lean_AsyncConstantInfo_isUnsafe(v_c_4665_);
if (v___x_4667_ == 0)
{
lean_object* v_name_4668_; uint8_t v___x_4669_; 
v_name_4668_ = lean_ctor_get(v_c_4665_, 0);
lean_inc_n(v_name_4668_, 2);
lean_inc_ref(v_env_4659_);
v___x_4669_ = l_Lean_Meta_LazyDiscrTree_blacklistInsertion(v_env_4659_, v_name_4668_);
if (v___x_4669_ == 0)
{
lean_object* v___x_4670_; lean_object* v_ngen_4671_; lean_object* v_core_4672_; lean_object* v_meta_4673_; lean_object* v___x_4675_; uint8_t v_isShared_4676_; uint8_t v_isSharedCheck_4791_; 
v___x_4670_ = lean_st_ref_get(v_cacheRef_4662_);
v_ngen_4671_ = lean_ctor_get(v___x_4670_, 0);
v_core_4672_ = lean_ctor_get(v___x_4670_, 1);
v_meta_4673_ = lean_ctor_get(v___x_4670_, 2);
v_isSharedCheck_4791_ = !lean_is_exclusive(v___x_4670_);
if (v_isSharedCheck_4791_ == 0)
{
v___x_4675_ = v___x_4670_;
v_isShared_4676_ = v_isSharedCheck_4791_;
goto v_resetjp_4674_;
}
else
{
lean_inc(v_meta_4673_);
lean_inc(v_core_4672_);
lean_inc(v_ngen_4671_);
lean_dec(v___x_4670_);
v___x_4675_ = lean_box(0);
v_isShared_4676_ = v_isSharedCheck_4791_;
goto v_resetjp_4674_;
}
v_resetjp_4674_:
{
lean_object* v___x_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; uint8_t v___x_4684_; lean_object* v___x_4685_; uint8_t v___x_4686_; uint8_t v___x_4687_; uint8_t v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; lean_object* v___x_4701_; lean_object* v___x_4702_; lean_object* v___x_4703_; lean_object* v___x_4704_; lean_object* v_toCold_4705_; lean_object* v_currRecDepth_4706_; lean_object* v_ref_4707_; uint8_t v_suppressElabErrors_4708_; lean_object* v___x_4710_; uint8_t v_isShared_4711_; uint8_t v_isSharedCheck_4790_; 
v___x_4677_ = lean_unsigned_to_nat(0u);
v___x_4678_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2);
v___x_4679_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4680_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5);
lean_inc_ref(v_ngen_4671_);
v___x_4681_ = l_Lean_Meta_LazyDiscrTree_Cache_empty(v_ngen_4671_);
v___x_4682_ = lean_st_ref_swap(v_cacheRef_4662_, v___x_4681_);
lean_dec(v___x_4682_);
v___x_4683_ = lean_box(1);
v___x_4684_ = 1;
v___x_4685_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4685_, 0, v___x_4678_);
lean_ctor_set(v___x_4685_, 1, v_meta_4673_);
lean_ctor_set(v___x_4685_, 2, v___x_4683_);
lean_ctor_set(v___x_4685_, 3, v___x_4679_);
lean_ctor_set(v___x_4685_, 4, v___x_4680_);
v___x_4686_ = 2;
v___x_4687_ = 0;
v___x_4688_ = 2;
v___x_4689_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_4689_, 0, v___x_4669_);
lean_ctor_set_uint8(v___x_4689_, 1, v___x_4669_);
lean_ctor_set_uint8(v___x_4689_, 2, v___x_4669_);
lean_ctor_set_uint8(v___x_4689_, 3, v___x_4669_);
lean_ctor_set_uint8(v___x_4689_, 4, v___x_4669_);
lean_ctor_set_uint8(v___x_4689_, 5, v___x_4684_);
lean_ctor_set_uint8(v___x_4689_, 6, v___x_4684_);
lean_ctor_set_uint8(v___x_4689_, 7, v___x_4669_);
lean_ctor_set_uint8(v___x_4689_, 8, v___x_4684_);
lean_ctor_set_uint8(v___x_4689_, 9, v___x_4686_);
lean_ctor_set_uint8(v___x_4689_, 10, v___x_4687_);
lean_ctor_set_uint8(v___x_4689_, 11, v___x_4684_);
lean_ctor_set_uint8(v___x_4689_, 12, v___x_4684_);
lean_ctor_set_uint8(v___x_4689_, 13, v___x_4684_);
lean_ctor_set_uint8(v___x_4689_, 14, v___x_4688_);
lean_ctor_set_uint8(v___x_4689_, 15, v___x_4684_);
lean_ctor_set_uint8(v___x_4689_, 16, v___x_4684_);
lean_ctor_set_uint8(v___x_4689_, 17, v___x_4684_);
lean_ctor_set_uint8(v___x_4689_, 18, v___x_4684_);
lean_ctor_set_uint8(v___x_4689_, 19, v___x_4669_);
v___x_4690_ = l_Lean_Meta_Config_toConfigWithKey(v___x_4689_);
v___x_4691_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6);
v___x_4692_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__7));
v___x_4693_ = lean_box(0);
v___x_4694_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4694_, 0, v___x_4690_);
lean_ctor_set(v___x_4694_, 1, v___x_4683_);
lean_ctor_set(v___x_4694_, 2, v___x_4691_);
lean_ctor_set(v___x_4694_, 3, v___x_4692_);
lean_ctor_set(v___x_4694_, 4, v___x_4693_);
lean_ctor_set(v___x_4694_, 5, v___x_4677_);
lean_ctor_set(v___x_4694_, 6, v___x_4693_);
lean_ctor_set_uint8(v___x_4694_, sizeof(void*)*7, v___x_4669_);
lean_ctor_set_uint8(v___x_4694_, sizeof(void*)*7 + 1, v___x_4669_);
lean_ctor_set_uint8(v___x_4694_, sizeof(void*)*7 + 2, v___x_4669_);
lean_ctor_set_uint8(v___x_4694_, sizeof(void*)*7 + 3, v___x_4684_);
v___x_4695_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__8, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__8_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__8);
v___x_4696_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__9));
v___x_4697_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10);
v___x_4698_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11);
v___x_4699_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12);
v___x_4700_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_4700_, 0, v_env_4659_);
lean_ctor_set(v___x_4700_, 1, v___x_4695_);
lean_ctor_set(v___x_4700_, 2, v_ngen_4671_);
lean_ctor_set(v___x_4700_, 3, v___x_4696_);
lean_ctor_set(v___x_4700_, 4, v___x_4697_);
lean_ctor_set(v___x_4700_, 5, v_core_4672_);
lean_ctor_set(v___x_4700_, 6, v___x_4698_);
lean_ctor_set(v___x_4700_, 7, v___x_4699_);
lean_ctor_set(v___x_4700_, 8, v___x_4692_);
v___x_4701_ = lean_st_mk_ref(v___x_4700_);
v___x_4702_ = l_Lean_inheritedTraceOptions;
v___x_4703_ = lean_st_ref_get(v___x_4702_);
v___x_4704_ = lean_st_ref_get(v___x_4701_);
v_toCold_4705_ = lean_ctor_get(v_cctx_4658_, 0);
v_currRecDepth_4706_ = lean_ctor_get(v_cctx_4658_, 1);
v_ref_4707_ = lean_ctor_get(v_cctx_4658_, 2);
v_suppressElabErrors_4708_ = lean_ctor_get_uint8(v_cctx_4658_, sizeof(void*)*3 + 1);
v_isSharedCheck_4790_ = !lean_is_exclusive(v_cctx_4658_);
if (v_isSharedCheck_4790_ == 0)
{
v___x_4710_ = v_cctx_4658_;
v_isShared_4711_ = v_isSharedCheck_4790_;
goto v_resetjp_4709_;
}
else
{
lean_inc(v_ref_4707_);
lean_inc(v_currRecDepth_4706_);
lean_inc(v_toCold_4705_);
lean_dec(v_cctx_4658_);
v___x_4710_ = lean_box(0);
v_isShared_4711_ = v_isSharedCheck_4790_;
goto v_resetjp_4709_;
}
v_resetjp_4709_:
{
lean_object* v_fileName_4712_; lean_object* v_fileMap_4713_; lean_object* v_options_4714_; lean_object* v_currNamespace_4715_; lean_object* v_openDecls_4716_; lean_object* v_initHeartbeats_4717_; lean_object* v_maxHeartbeats_4718_; lean_object* v_quotContext_4719_; lean_object* v_currMacroScope_4720_; lean_object* v_cancelTk_x3f_4721_; lean_object* v___x_4723_; uint8_t v_isShared_4724_; uint8_t v_isSharedCheck_4787_; 
v_fileName_4712_ = lean_ctor_get(v_toCold_4705_, 0);
v_fileMap_4713_ = lean_ctor_get(v_toCold_4705_, 1);
v_options_4714_ = lean_ctor_get(v_toCold_4705_, 2);
v_currNamespace_4715_ = lean_ctor_get(v_toCold_4705_, 4);
v_openDecls_4716_ = lean_ctor_get(v_toCold_4705_, 5);
v_initHeartbeats_4717_ = lean_ctor_get(v_toCold_4705_, 6);
v_maxHeartbeats_4718_ = lean_ctor_get(v_toCold_4705_, 7);
v_quotContext_4719_ = lean_ctor_get(v_toCold_4705_, 8);
v_currMacroScope_4720_ = lean_ctor_get(v_toCold_4705_, 9);
v_cancelTk_x3f_4721_ = lean_ctor_get(v_toCold_4705_, 10);
v_isSharedCheck_4787_ = !lean_is_exclusive(v_toCold_4705_);
if (v_isSharedCheck_4787_ == 0)
{
lean_object* v_unused_4788_; lean_object* v_unused_4789_; 
v_unused_4788_ = lean_ctor_get(v_toCold_4705_, 11);
lean_dec(v_unused_4788_);
v_unused_4789_ = lean_ctor_get(v_toCold_4705_, 3);
lean_dec(v_unused_4789_);
v___x_4723_ = v_toCold_4705_;
v_isShared_4724_ = v_isSharedCheck_4787_;
goto v_resetjp_4722_;
}
else
{
lean_inc(v_cancelTk_x3f_4721_);
lean_inc(v_currMacroScope_4720_);
lean_inc(v_quotContext_4719_);
lean_inc(v_maxHeartbeats_4718_);
lean_inc(v_initHeartbeats_4717_);
lean_inc(v_openDecls_4716_);
lean_inc(v_currNamespace_4715_);
lean_inc(v_options_4714_);
lean_inc(v_fileMap_4713_);
lean_inc(v_fileName_4712_);
lean_dec(v_toCold_4705_);
v___x_4723_ = lean_box(0);
v_isShared_4724_ = v_isSharedCheck_4787_;
goto v_resetjp_4722_;
}
v_resetjp_4722_:
{
lean_object* v_env_4725_; lean_object* v___x_4726_; uint8_t v___x_4727_; lean_object* v___y_4729_; uint8_t v___y_4765_; uint8_t v___x_4786_; 
v_env_4725_ = lean_ctor_get(v___x_4704_, 0);
lean_inc_ref(v_env_4725_);
lean_dec(v___x_4704_);
v___x_4726_ = l_Lean_diagnostics;
v___x_4727_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(v_options_4714_, v___x_4726_);
v___x_4786_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4725_);
lean_dec_ref(v_env_4725_);
if (v___x_4727_ == 0)
{
if (v___x_4786_ == 0)
{
lean_inc(v___x_4701_);
v___y_4729_ = v___x_4701_;
goto v___jp_4728_;
}
else
{
v___y_4765_ = v___x_4727_;
goto v___jp_4764_;
}
}
else
{
v___y_4765_ = v___x_4786_;
goto v___jp_4764_;
}
v___jp_4728_:
{
lean_object* v___x_4730_; lean_object* v___x_4731_; lean_object* v___x_4732_; lean_object* v___x_4734_; 
v___x_4730_ = lean_st_mk_ref(v___x_4685_);
v___x_4731_ = l_Lean_maxRecDepth;
v___x_4732_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1(v_options_4714_, v___x_4731_);
if (v_isShared_4724_ == 0)
{
lean_ctor_set(v___x_4723_, 11, v___x_4703_);
lean_ctor_set(v___x_4723_, 3, v___x_4732_);
v___x_4734_ = v___x_4723_;
goto v_reusejp_4733_;
}
else
{
lean_object* v_reuseFailAlloc_4763_; 
v_reuseFailAlloc_4763_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_4763_, 0, v_fileName_4712_);
lean_ctor_set(v_reuseFailAlloc_4763_, 1, v_fileMap_4713_);
lean_ctor_set(v_reuseFailAlloc_4763_, 2, v_options_4714_);
lean_ctor_set(v_reuseFailAlloc_4763_, 3, v___x_4732_);
lean_ctor_set(v_reuseFailAlloc_4763_, 4, v_currNamespace_4715_);
lean_ctor_set(v_reuseFailAlloc_4763_, 5, v_openDecls_4716_);
lean_ctor_set(v_reuseFailAlloc_4763_, 6, v_initHeartbeats_4717_);
lean_ctor_set(v_reuseFailAlloc_4763_, 7, v_maxHeartbeats_4718_);
lean_ctor_set(v_reuseFailAlloc_4763_, 8, v_quotContext_4719_);
lean_ctor_set(v_reuseFailAlloc_4763_, 9, v_currMacroScope_4720_);
lean_ctor_set(v_reuseFailAlloc_4763_, 10, v_cancelTk_x3f_4721_);
lean_ctor_set(v_reuseFailAlloc_4763_, 11, v___x_4703_);
v___x_4734_ = v_reuseFailAlloc_4763_;
goto v_reusejp_4733_;
}
v_reusejp_4733_:
{
lean_object* v___x_4736_; 
if (v_isShared_4711_ == 0)
{
lean_ctor_set(v___x_4710_, 0, v___x_4734_);
v___x_4736_ = v___x_4710_;
goto v_reusejp_4735_;
}
else
{
lean_object* v_reuseFailAlloc_4762_; 
v_reuseFailAlloc_4762_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4762_, 0, v___x_4734_);
lean_ctor_set(v_reuseFailAlloc_4762_, 1, v_currRecDepth_4706_);
lean_ctor_set(v_reuseFailAlloc_4762_, 2, v_ref_4707_);
lean_ctor_set_uint8(v_reuseFailAlloc_4762_, sizeof(void*)*3 + 1, v_suppressElabErrors_4708_);
v___x_4736_ = v_reuseFailAlloc_4762_;
goto v_reusejp_4735_;
}
v_reusejp_4735_:
{
lean_object* v___x_4737_; 
lean_ctor_set_uint8(v___x_4736_, sizeof(void*)*3, v___x_4727_);
lean_inc(v___x_4730_);
lean_inc(v_name_4668_);
v___x_4737_ = lean_apply_7(v_act_4664_, v_name_4668_, v_c_4665_, v___x_4694_, v___x_4730_, v___x_4736_, v___y_4729_, lean_box(0));
if (lean_obj_tag(v___x_4737_) == 0)
{
lean_object* v_a_4738_; lean_object* v___x_4739_; lean_object* v___x_4740_; lean_object* v_ngen_4741_; lean_object* v_cache_4742_; lean_object* v_cache_4743_; lean_object* v___x_4745_; 
lean_dec(v_name_4668_);
lean_dec(v_modName_4660_);
v_a_4738_ = lean_ctor_get(v___x_4737_, 0);
lean_inc(v_a_4738_);
lean_dec_ref_known(v___x_4737_, 1);
v___x_4739_ = lean_st_ref_get(v___x_4730_);
lean_dec(v___x_4730_);
v___x_4740_ = lean_st_ref_get(v___x_4701_);
lean_dec(v___x_4701_);
v_ngen_4741_ = lean_ctor_get(v___x_4740_, 2);
lean_inc_ref(v_ngen_4741_);
v_cache_4742_ = lean_ctor_get(v___x_4740_, 5);
lean_inc_ref(v_cache_4742_);
lean_dec(v___x_4740_);
v_cache_4743_ = lean_ctor_get(v___x_4739_, 1);
lean_inc_ref(v_cache_4743_);
lean_dec(v___x_4739_);
if (v_isShared_4676_ == 0)
{
lean_ctor_set(v___x_4675_, 2, v_cache_4743_);
lean_ctor_set(v___x_4675_, 1, v_cache_4742_);
lean_ctor_set(v___x_4675_, 0, v_ngen_4741_);
v___x_4745_ = v___x_4675_;
goto v_reusejp_4744_;
}
else
{
lean_object* v_reuseFailAlloc_4756_; 
v_reuseFailAlloc_4756_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4756_, 0, v_ngen_4741_);
lean_ctor_set(v_reuseFailAlloc_4756_, 1, v_cache_4742_);
lean_ctor_set(v_reuseFailAlloc_4756_, 2, v_cache_4743_);
v___x_4745_ = v_reuseFailAlloc_4756_;
goto v_reusejp_4744_;
}
v_reusejp_4744_:
{
lean_object* v___x_4746_; lean_object* v___x_4747_; uint8_t v___x_4748_; 
v___x_4746_ = lean_st_ref_swap(v_cacheRef_4662_, v___x_4745_);
lean_dec(v___x_4746_);
v___x_4747_ = lean_array_get_size(v_a_4738_);
v___x_4748_ = lean_nat_dec_lt(v___x_4677_, v___x_4747_);
if (v___x_4748_ == 0)
{
lean_dec(v_a_4738_);
return v_tree_4663_;
}
else
{
uint8_t v___x_4749_; 
v___x_4749_ = lean_nat_dec_le(v___x_4747_, v___x_4747_);
if (v___x_4749_ == 0)
{
if (v___x_4748_ == 0)
{
lean_dec(v_a_4738_);
return v_tree_4663_;
}
else
{
size_t v___x_4750_; size_t v___x_4751_; lean_object* v___x_4752_; 
v___x_4750_ = ((size_t)0ULL);
v___x_4751_ = lean_usize_of_nat(v___x_4747_);
v___x_4752_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg(v_a_4738_, v___x_4750_, v___x_4751_, v_tree_4663_);
lean_dec(v_a_4738_);
return v___x_4752_;
}
}
else
{
size_t v___x_4753_; size_t v___x_4754_; lean_object* v___x_4755_; 
v___x_4753_ = ((size_t)0ULL);
v___x_4754_ = lean_usize_of_nat(v___x_4747_);
v___x_4755_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg(v_a_4738_, v___x_4753_, v___x_4754_, v_tree_4663_);
lean_dec(v_a_4738_);
return v___x_4755_;
}
}
}
}
else
{
lean_object* v_a_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; lean_object* v___x_4760_; lean_object* v___x_4761_; 
lean_dec(v___x_4730_);
lean_dec(v___x_4701_);
lean_del_object(v___x_4675_);
v_a_4757_ = lean_ctor_get(v___x_4737_, 0);
lean_inc(v_a_4757_);
lean_dec_ref_known(v___x_4737_, 1);
v___x_4758_ = lean_st_ref_take(v_d_4661_);
v___x_4759_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4759_, 0, v_modName_4660_);
lean_ctor_set(v___x_4759_, 1, v_name_4668_);
lean_ctor_set(v___x_4759_, 2, v_a_4757_);
v___x_4760_ = lean_array_push(v___x_4758_, v___x_4759_);
v___x_4761_ = lean_st_ref_put(v_d_4661_, v___x_4760_);
return v_tree_4663_;
}
}
}
}
v___jp_4764_:
{
if (v___y_4765_ == 0)
{
lean_object* v___x_4766_; lean_object* v_env_4767_; lean_object* v_nextMacroScope_4768_; lean_object* v_ngen_4769_; lean_object* v_auxDeclNGen_4770_; lean_object* v_traceState_4771_; lean_object* v_messages_4772_; lean_object* v_infoState_4773_; lean_object* v_snapshotTasks_4774_; lean_object* v___x_4776_; uint8_t v_isShared_4777_; uint8_t v_isSharedCheck_4784_; 
v___x_4766_ = lean_st_ref_take(v___x_4701_);
v_env_4767_ = lean_ctor_get(v___x_4766_, 0);
v_nextMacroScope_4768_ = lean_ctor_get(v___x_4766_, 1);
v_ngen_4769_ = lean_ctor_get(v___x_4766_, 2);
v_auxDeclNGen_4770_ = lean_ctor_get(v___x_4766_, 3);
v_traceState_4771_ = lean_ctor_get(v___x_4766_, 4);
v_messages_4772_ = lean_ctor_get(v___x_4766_, 6);
v_infoState_4773_ = lean_ctor_get(v___x_4766_, 7);
v_snapshotTasks_4774_ = lean_ctor_get(v___x_4766_, 8);
v_isSharedCheck_4784_ = !lean_is_exclusive(v___x_4766_);
if (v_isSharedCheck_4784_ == 0)
{
lean_object* v_unused_4785_; 
v_unused_4785_ = lean_ctor_get(v___x_4766_, 5);
lean_dec(v_unused_4785_);
v___x_4776_ = v___x_4766_;
v_isShared_4777_ = v_isSharedCheck_4784_;
goto v_resetjp_4775_;
}
else
{
lean_inc(v_snapshotTasks_4774_);
lean_inc(v_infoState_4773_);
lean_inc(v_messages_4772_);
lean_inc(v_traceState_4771_);
lean_inc(v_auxDeclNGen_4770_);
lean_inc(v_ngen_4769_);
lean_inc(v_nextMacroScope_4768_);
lean_inc(v_env_4767_);
lean_dec(v___x_4766_);
v___x_4776_ = lean_box(0);
v_isShared_4777_ = v_isSharedCheck_4784_;
goto v_resetjp_4775_;
}
v_resetjp_4775_:
{
lean_object* v___x_4778_; lean_object* v___x_4779_; lean_object* v___x_4781_; 
v___x_4778_ = l_Lean_Kernel_enableDiag(v_env_4767_, v___x_4727_);
v___x_4779_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13);
if (v_isShared_4777_ == 0)
{
lean_ctor_set(v___x_4776_, 5, v___x_4779_);
lean_ctor_set(v___x_4776_, 0, v___x_4778_);
v___x_4781_ = v___x_4776_;
goto v_reusejp_4780_;
}
else
{
lean_object* v_reuseFailAlloc_4783_; 
v_reuseFailAlloc_4783_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4783_, 0, v___x_4778_);
lean_ctor_set(v_reuseFailAlloc_4783_, 1, v_nextMacroScope_4768_);
lean_ctor_set(v_reuseFailAlloc_4783_, 2, v_ngen_4769_);
lean_ctor_set(v_reuseFailAlloc_4783_, 3, v_auxDeclNGen_4770_);
lean_ctor_set(v_reuseFailAlloc_4783_, 4, v_traceState_4771_);
lean_ctor_set(v_reuseFailAlloc_4783_, 5, v___x_4779_);
lean_ctor_set(v_reuseFailAlloc_4783_, 6, v_messages_4772_);
lean_ctor_set(v_reuseFailAlloc_4783_, 7, v_infoState_4773_);
lean_ctor_set(v_reuseFailAlloc_4783_, 8, v_snapshotTasks_4774_);
v___x_4781_ = v_reuseFailAlloc_4783_;
goto v_reusejp_4780_;
}
v_reusejp_4780_:
{
lean_object* v___x_4782_; 
v___x_4782_ = lean_st_ref_put(v___x_4701_, v___x_4781_);
lean_inc(v___x_4701_);
v___y_4729_ = v___x_4701_;
goto v___jp_4728_;
}
}
}
else
{
lean_inc(v___x_4701_);
v___y_4729_ = v___x_4701_;
goto v___jp_4728_;
}
}
}
}
}
}
else
{
lean_dec(v_name_4668_);
lean_dec_ref(v_c_4665_);
lean_dec_ref(v_act_4664_);
lean_dec(v_modName_4660_);
lean_dec_ref(v_env_4659_);
lean_dec_ref(v_cctx_4658_);
return v_tree_4663_;
}
}
else
{
lean_dec_ref(v_c_4665_);
lean_dec_ref(v_act_4664_);
lean_dec(v_modName_4660_);
lean_dec_ref(v_env_4659_);
lean_dec_ref(v_cctx_4658_);
return v_tree_4663_;
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
lean_object* v___x_4950_; lean_object* v_moduleData_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; lean_object* v___x_4954_; lean_object* v_mname_4955_; lean_object* v_mdata_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; lean_object* v___x_4960_; 
v___x_4950_ = l_Lean_Environment_header(v_env_4940_);
v_moduleData_4951_ = lean_ctor_get(v___x_4950_, 6);
lean_inc_ref(v_moduleData_4951_);
v___x_4952_ = lean_box(0);
v___x_4953_ = l_Lean_instInhabitedModuleData_default;
v___x_4954_ = l_Lean_EnvironmentHeader_moduleNames(v___x_4950_);
v_mname_4955_ = lean_array_get(v___x_4952_, v___x_4954_, v_start_4945_);
lean_dec_ref(v___x_4954_);
v_mdata_4956_ = lean_array_get(v___x_4953_, v_moduleData_4951_, v_start_4945_);
lean_dec_ref(v_moduleData_4951_);
v___x_4957_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_act_4941_);
lean_inc_ref(v_env_4940_);
lean_inc_ref(v_cctx_4939_);
v___x_4958_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(v_cctx_4939_, v_env_4940_, v_act_4941_, v_d_4942_, v_cacheRef_4943_, v_tree_4944_, v_mname_4955_, v_mdata_4956_, v___x_4957_);
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
v___x_5329_ = lean_st_ref_put(v_a_5301_, v___x_5328_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__0(lean_object* v_tasks_5713_, lean_object* v_toPure_5714_, lean_object* v_t_5715_){
_start:
{
lean_object* v___x_5716_; lean_object* v___x_5717_; 
v___x_5716_ = lean_array_push(v_tasks_5713_, v_t_5715_);
v___x_5717_ = lean_apply_2(v_toPure_5714_, lean_box(0), v___x_5716_);
return v___x_5717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(lean_object* v_inst_5718_, lean_object* v_inst_5719_, lean_object* v_cctx_5720_, lean_object* v_env_5721_, lean_object* v_act_5722_, lean_object* v_constantsPerTask_5723_, lean_object* v_n_5724_, lean_object* v_ngen_5725_, lean_object* v_tasks_5726_, lean_object* v_start_5727_, lean_object* v_cnt_5728_, lean_object* v_idx_5729_){
_start:
{
lean_object* v___x_5730_; lean_object* v_toApplicative_5731_; lean_object* v_moduleData_5732_; lean_object* v_toBind_5733_; lean_object* v_toPure_5734_; lean_object* v___x_5735_; uint8_t v___x_5736_; 
v___x_5730_ = l_Lean_Environment_header(v_env_5721_);
v_toApplicative_5731_ = lean_ctor_get(v_inst_5718_, 0);
v_moduleData_5732_ = lean_ctor_get(v___x_5730_, 6);
lean_inc_ref(v_moduleData_5732_);
lean_dec_ref(v___x_5730_);
v_toBind_5733_ = lean_ctor_get(v_inst_5718_, 1);
v_toPure_5734_ = lean_ctor_get(v_toApplicative_5731_, 1);
v___x_5735_ = lean_array_get_size(v_moduleData_5732_);
v___x_5736_ = lean_nat_dec_lt(v_idx_5729_, v___x_5735_);
if (v___x_5736_ == 0)
{
uint8_t v___x_5737_; 
lean_inc(v_toPure_5734_);
lean_inc(v_toBind_5733_);
lean_dec_ref(v_moduleData_5732_);
lean_dec(v_idx_5729_);
lean_dec(v_cnt_5728_);
lean_dec(v_constantsPerTask_5723_);
lean_dec_ref(v_inst_5718_);
v___x_5737_ = lean_nat_dec_lt(v_start_5727_, v_n_5724_);
if (v___x_5737_ == 0)
{
lean_object* v___x_5738_; 
lean_dec(v_toBind_5733_);
lean_dec(v_start_5727_);
lean_dec_ref(v_ngen_5725_);
lean_dec(v_n_5724_);
lean_dec_ref(v_act_5722_);
lean_dec_ref(v_env_5721_);
lean_dec_ref(v_cctx_5720_);
lean_dec(v_inst_5719_);
v___x_5738_ = lean_apply_2(v_toPure_5734_, lean_box(0), v_tasks_5726_);
return v___x_5738_;
}
else
{
lean_object* v_namePrefix_5739_; lean_object* v_idx_5740_; lean_object* v___x_5742_; uint8_t v_isShared_5743_; uint8_t v_isSharedCheck_5755_; 
v_namePrefix_5739_ = lean_ctor_get(v_ngen_5725_, 0);
v_idx_5740_ = lean_ctor_get(v_ngen_5725_, 1);
v_isSharedCheck_5755_ = !lean_is_exclusive(v_ngen_5725_);
if (v_isSharedCheck_5755_ == 0)
{
v___x_5742_ = v_ngen_5725_;
v_isShared_5743_ = v_isSharedCheck_5755_;
goto v_resetjp_5741_;
}
else
{
lean_inc(v_idx_5740_);
lean_inc(v_namePrefix_5739_);
lean_dec(v_ngen_5725_);
v___x_5742_ = lean_box(0);
v_isShared_5743_ = v_isSharedCheck_5755_;
goto v_resetjp_5741_;
}
v_resetjp_5741_:
{
lean_object* v___f_5744_; lean_object* v___x_5745_; lean_object* v___x_5746_; lean_object* v___x_5748_; 
v___f_5744_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5744_, 0, v_tasks_5726_);
lean_closure_set(v___f_5744_, 1, v_toPure_5734_);
v___x_5745_ = l_Lean_Name_num___override(v_namePrefix_5739_, v_idx_5740_);
v___x_5746_ = lean_unsigned_to_nat(1u);
if (v_isShared_5743_ == 0)
{
lean_ctor_set(v___x_5742_, 1, v___x_5746_);
lean_ctor_set(v___x_5742_, 0, v___x_5745_);
v___x_5748_ = v___x_5742_;
goto v_reusejp_5747_;
}
else
{
lean_object* v_reuseFailAlloc_5754_; 
v_reuseFailAlloc_5754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5754_, 0, v___x_5745_);
lean_ctor_set(v_reuseFailAlloc_5754_, 1, v___x_5746_);
v___x_5748_ = v_reuseFailAlloc_5754_;
goto v_reusejp_5747_;
}
v_reusejp_5747_:
{
lean_object* v___x_5749_; lean_object* v___x_5750_; lean_object* v___x_5751_; lean_object* v___x_5752_; lean_object* v___x_5753_; 
v___x_5749_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_5749_, 0, lean_box(0));
lean_closure_set(v___x_5749_, 1, v_cctx_5720_);
lean_closure_set(v___x_5749_, 2, v___x_5748_);
lean_closure_set(v___x_5749_, 3, v_env_5721_);
lean_closure_set(v___x_5749_, 4, v_act_5722_);
lean_closure_set(v___x_5749_, 5, v_start_5727_);
lean_closure_set(v___x_5749_, 6, v_n_5724_);
v___x_5750_ = lean_unsigned_to_nat(0u);
v___x_5751_ = lean_alloc_closure((void*)(l_BaseIO_asTask___boxed), 4, 3);
lean_closure_set(v___x_5751_, 0, lean_box(0));
lean_closure_set(v___x_5751_, 1, v___x_5749_);
lean_closure_set(v___x_5751_, 2, v___x_5750_);
v___x_5752_ = lean_apply_2(v_inst_5719_, lean_box(0), v___x_5751_);
v___x_5753_ = lean_apply_4(v_toBind_5733_, lean_box(0), lean_box(0), v___x_5752_, v___f_5744_);
return v___x_5753_;
}
}
}
}
else
{
lean_object* v_mdata_5756_; lean_object* v_constants_5757_; lean_object* v___x_5758_; lean_object* v_cnt_5759_; uint8_t v___x_5760_; 
v_mdata_5756_ = lean_array_fget(v_moduleData_5732_, v_idx_5729_);
lean_dec_ref(v_moduleData_5732_);
v_constants_5757_ = lean_ctor_get(v_mdata_5756_, 2);
lean_inc_ref(v_constants_5757_);
lean_dec(v_mdata_5756_);
v___x_5758_ = lean_array_get_size(v_constants_5757_);
lean_dec_ref(v_constants_5757_);
v_cnt_5759_ = lean_nat_add(v_cnt_5728_, v___x_5758_);
lean_dec(v_cnt_5728_);
v___x_5760_ = lean_nat_dec_lt(v_constantsPerTask_5723_, v_cnt_5759_);
if (v___x_5760_ == 0)
{
lean_object* v___x_5761_; lean_object* v___x_5762_; 
v___x_5761_ = lean_unsigned_to_nat(1u);
v___x_5762_ = lean_nat_add(v_idx_5729_, v___x_5761_);
lean_dec(v_idx_5729_);
v_cnt_5728_ = v_cnt_5759_;
v_idx_5729_ = v___x_5762_;
goto _start;
}
else
{
lean_object* v_namePrefix_5764_; lean_object* v_idx_5765_; lean_object* v___x_5767_; uint8_t v_isShared_5768_; uint8_t v_isSharedCheck_5783_; 
lean_inc(v_toBind_5733_);
lean_dec(v_cnt_5759_);
v_namePrefix_5764_ = lean_ctor_get(v_ngen_5725_, 0);
v_idx_5765_ = lean_ctor_get(v_ngen_5725_, 1);
v_isSharedCheck_5783_ = !lean_is_exclusive(v_ngen_5725_);
if (v_isSharedCheck_5783_ == 0)
{
v___x_5767_ = v_ngen_5725_;
v_isShared_5768_ = v_isSharedCheck_5783_;
goto v_resetjp_5766_;
}
else
{
lean_inc(v_idx_5765_);
lean_inc(v_namePrefix_5764_);
lean_dec(v_ngen_5725_);
v___x_5767_ = lean_box(0);
v_isShared_5768_ = v_isSharedCheck_5783_;
goto v_resetjp_5766_;
}
v_resetjp_5766_:
{
lean_object* v___x_5769_; lean_object* v___x_5770_; lean_object* v___x_5772_; 
lean_inc(v_idx_5765_);
lean_inc(v_namePrefix_5764_);
v___x_5769_ = l_Lean_Name_num___override(v_namePrefix_5764_, v_idx_5765_);
v___x_5770_ = lean_unsigned_to_nat(1u);
if (v_isShared_5768_ == 0)
{
lean_ctor_set(v___x_5767_, 1, v___x_5770_);
lean_ctor_set(v___x_5767_, 0, v___x_5769_);
v___x_5772_ = v___x_5767_;
goto v_reusejp_5771_;
}
else
{
lean_object* v_reuseFailAlloc_5782_; 
v_reuseFailAlloc_5782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5782_, 0, v___x_5769_);
lean_ctor_set(v_reuseFailAlloc_5782_, 1, v___x_5770_);
v___x_5772_ = v_reuseFailAlloc_5782_;
goto v_reusejp_5771_;
}
v_reusejp_5771_:
{
lean_object* v___x_5773_; lean_object* v___x_5774_; lean_object* v___x_5775_; lean_object* v___f_5776_; lean_object* v___x_5777_; lean_object* v___x_5778_; lean_object* v___x_5779_; lean_object* v___x_5780_; lean_object* v___x_5781_; 
v___x_5773_ = lean_nat_add(v_idx_5765_, v___x_5770_);
lean_dec(v_idx_5765_);
v___x_5774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5774_, 0, v_namePrefix_5764_);
lean_ctor_set(v___x_5774_, 1, v___x_5773_);
v___x_5775_ = lean_nat_add(v_idx_5729_, v___x_5770_);
lean_dec(v_idx_5729_);
lean_inc(v___x_5775_);
lean_inc_ref(v_act_5722_);
lean_inc_ref(v_env_5721_);
lean_inc_ref(v_cctx_5720_);
lean_inc(v_inst_5719_);
v___f_5776_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__1), 11, 10);
lean_closure_set(v___f_5776_, 0, v_tasks_5726_);
lean_closure_set(v___f_5776_, 1, v_inst_5718_);
lean_closure_set(v___f_5776_, 2, v_inst_5719_);
lean_closure_set(v___f_5776_, 3, v_cctx_5720_);
lean_closure_set(v___f_5776_, 4, v_env_5721_);
lean_closure_set(v___f_5776_, 5, v_act_5722_);
lean_closure_set(v___f_5776_, 6, v_constantsPerTask_5723_);
lean_closure_set(v___f_5776_, 7, v_n_5724_);
lean_closure_set(v___f_5776_, 8, v___x_5774_);
lean_closure_set(v___f_5776_, 9, v___x_5775_);
v___x_5777_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_5777_, 0, lean_box(0));
lean_closure_set(v___x_5777_, 1, v_cctx_5720_);
lean_closure_set(v___x_5777_, 2, v___x_5772_);
lean_closure_set(v___x_5777_, 3, v_env_5721_);
lean_closure_set(v___x_5777_, 4, v_act_5722_);
lean_closure_set(v___x_5777_, 5, v_start_5727_);
lean_closure_set(v___x_5777_, 6, v___x_5775_);
v___x_5778_ = lean_unsigned_to_nat(0u);
v___x_5779_ = lean_alloc_closure((void*)(l_BaseIO_asTask___boxed), 4, 3);
lean_closure_set(v___x_5779_, 0, lean_box(0));
lean_closure_set(v___x_5779_, 1, v___x_5777_);
lean_closure_set(v___x_5779_, 2, v___x_5778_);
v___x_5780_ = lean_apply_2(v_inst_5719_, lean_box(0), v___x_5779_);
v___x_5781_ = lean_apply_4(v_toBind_5733_, lean_box(0), lean_box(0), v___x_5780_, v___f_5776_);
return v___x_5781_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__1(lean_object* v_tasks_5784_, lean_object* v_inst_5785_, lean_object* v_inst_5786_, lean_object* v_cctx_5787_, lean_object* v_env_5788_, lean_object* v_act_5789_, lean_object* v_constantsPerTask_5790_, lean_object* v_n_5791_, lean_object* v___x_5792_, lean_object* v___x_5793_, lean_object* v_t_5794_){
_start:
{
lean_object* v___x_5795_; lean_object* v___x_5796_; lean_object* v___x_5797_; 
v___x_5795_ = lean_array_push(v_tasks_5784_, v_t_5794_);
v___x_5796_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_5793_);
v___x_5797_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(v_inst_5785_, v_inst_5786_, v_cctx_5787_, v_env_5788_, v_act_5789_, v_constantsPerTask_5790_, v_n_5791_, v___x_5792_, v___x_5795_, v___x_5793_, v___x_5796_, v___x_5793_);
return v___x_5797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go(lean_object* v_m_5798_, lean_object* v_00_u03b1_5799_, lean_object* v_inst_5800_, lean_object* v_inst_5801_, lean_object* v_cctx_5802_, lean_object* v_env_5803_, lean_object* v_act_5804_, lean_object* v_constantsPerTask_5805_, lean_object* v_n_5806_, lean_object* v_ngen_5807_, lean_object* v_tasks_5808_, lean_object* v_start_5809_, lean_object* v_cnt_5810_, lean_object* v_idx_5811_){
_start:
{
lean_object* v___x_5812_; 
v___x_5812_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(v_inst_5800_, v_inst_5801_, v_cctx_5802_, v_env_5803_, v_act_5804_, v_constantsPerTask_5805_, v_n_5806_, v_ngen_5807_, v_tasks_5808_, v_start_5809_, v_cnt_5810_, v_idx_5811_);
return v___x_5812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_getChildNgen_match__1_splitter___redArg(lean_object* v_x_5813_, lean_object* v_h__1_5814_){
_start:
{
lean_object* v_fst_5815_; lean_object* v_snd_5816_; lean_object* v___x_5817_; 
v_fst_5815_ = lean_ctor_get(v_x_5813_, 0);
lean_inc(v_fst_5815_);
v_snd_5816_ = lean_ctor_get(v_x_5813_, 1);
lean_inc(v_snd_5816_);
lean_dec_ref(v_x_5813_);
v___x_5817_ = lean_apply_2(v_h__1_5814_, v_fst_5815_, v_snd_5816_);
return v___x_5817_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_getChildNgen_match__1_splitter(lean_object* v_motive_5818_, lean_object* v_x_5819_, lean_object* v_h__1_5820_){
_start:
{
lean_object* v_fst_5821_; lean_object* v_snd_5822_; lean_object* v___x_5823_; 
v_fst_5821_ = lean_ctor_get(v_x_5819_, 0);
lean_inc(v_fst_5821_);
v_snd_5822_ = lean_ctor_get(v_x_5819_, 1);
lean_inc(v_snd_5822_);
lean_dec_ref(v_x_5819_);
v___x_5823_ = lean_apply_2(v_h__1_5820_, v_fst_5821_, v_snd_5822_);
return v___x_5823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__0(lean_object* v_inst_5824_, lean_object* v_inst_5825_, lean_object* v_inst_5826_, lean_object* v_inst_5827_, lean_object* v_x_5828_, lean_object* v___y_5829_){
_start:
{
lean_object* v___x_5830_; 
v___x_5830_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg(v_inst_5824_, v_inst_5825_, v_inst_5826_, v_inst_5827_, v___y_5829_);
return v___x_5830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__1(lean_object* v_r_5831_, lean_object* v_toPure_5832_, lean_object* v_____r_5833_){
_start:
{
lean_object* v_tree_5834_; lean_object* v___x_5835_; lean_object* v___x_5836_; 
v_tree_5834_ = lean_ctor_get(v_r_5831_, 0);
lean_inc_ref(v_tree_5834_);
lean_dec_ref(v_r_5831_);
v___x_5835_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_tree_5834_);
v___x_5836_ = lean_apply_2(v_toPure_5832_, lean_box(0), v___x_5835_);
return v___x_5836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__2(lean_object* v___x_5837_, lean_object* v___x_5838_, lean_object* v_toPure_5839_, lean_object* v_toBind_5840_, lean_object* v_inst_5841_, lean_object* v___f_5842_, lean_object* v_tasks_5843_){
_start:
{
lean_object* v___x_5844_; lean_object* v___x_5845_; lean_object* v___x_5846_; lean_object* v___x_5847_; lean_object* v___x_5848_; lean_object* v_r_5849_; lean_object* v_errors_5850_; lean_object* v___f_5851_; lean_object* v___x_5852_; lean_object* v___x_5853_; uint8_t v___x_5854_; 
v___x_5844_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1);
lean_inc(v___x_5837_);
v___x_5845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5845_, 0, v___x_5837_);
lean_ctor_set(v___x_5845_, 1, v___x_5844_);
v___x_5846_ = lean_mk_empty_array_with_capacity(v___x_5837_);
lean_inc_ref(v___x_5846_);
v___x_5847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5847_, 0, v___x_5845_);
lean_ctor_set(v___x_5847_, 1, v___x_5846_);
v___x_5848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5848_, 0, v___x_5847_);
lean_ctor_set(v___x_5848_, 1, v___x_5846_);
v_r_5849_ = l_Lean_Meta_LazyDiscrTree_combineGet___redArg(v___x_5838_, v___x_5848_, v_tasks_5843_);
v_errors_5850_ = lean_ctor_get(v_r_5849_, 1);
lean_inc_ref(v_errors_5850_);
lean_inc(v_toPure_5839_);
v___f_5851_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__1), 3, 2);
lean_closure_set(v___f_5851_, 0, v_r_5849_);
lean_closure_set(v___f_5851_, 1, v_toPure_5839_);
v___x_5852_ = lean_array_get_size(v_errors_5850_);
v___x_5853_ = lean_box(0);
v___x_5854_ = lean_nat_dec_lt(v___x_5837_, v___x_5852_);
lean_dec(v___x_5837_);
if (v___x_5854_ == 0)
{
lean_object* v___x_5855_; lean_object* v___x_5856_; 
lean_dec_ref(v_errors_5850_);
lean_dec(v___f_5842_);
lean_dec_ref(v_inst_5841_);
v___x_5855_ = lean_apply_2(v_toPure_5839_, lean_box(0), v___x_5853_);
v___x_5856_ = lean_apply_4(v_toBind_5840_, lean_box(0), lean_box(0), v___x_5855_, v___f_5851_);
return v___x_5856_;
}
else
{
uint8_t v___x_5857_; 
v___x_5857_ = lean_nat_dec_le(v___x_5852_, v___x_5852_);
if (v___x_5857_ == 0)
{
if (v___x_5854_ == 0)
{
lean_object* v___x_5858_; lean_object* v___x_5859_; 
lean_dec_ref(v_errors_5850_);
lean_dec(v___f_5842_);
lean_dec_ref(v_inst_5841_);
v___x_5858_ = lean_apply_2(v_toPure_5839_, lean_box(0), v___x_5853_);
v___x_5859_ = lean_apply_4(v_toBind_5840_, lean_box(0), lean_box(0), v___x_5858_, v___f_5851_);
return v___x_5859_;
}
else
{
size_t v___x_5860_; size_t v___x_5861_; lean_object* v___x_5862_; lean_object* v___x_5863_; 
lean_dec(v_toPure_5839_);
v___x_5860_ = ((size_t)0ULL);
v___x_5861_ = lean_usize_of_nat(v___x_5852_);
v___x_5862_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_5841_, v___f_5842_, v_errors_5850_, v___x_5860_, v___x_5861_, v___x_5853_);
v___x_5863_ = lean_apply_4(v_toBind_5840_, lean_box(0), lean_box(0), v___x_5862_, v___f_5851_);
return v___x_5863_;
}
}
else
{
size_t v___x_5864_; size_t v___x_5865_; lean_object* v___x_5866_; lean_object* v___x_5867_; 
lean_dec(v_toPure_5839_);
v___x_5864_ = ((size_t)0ULL);
v___x_5865_ = lean_usize_of_nat(v___x_5852_);
v___x_5866_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_5841_, v___f_5842_, v_errors_5850_, v___x_5864_, v___x_5865_, v___x_5853_);
v___x_5867_ = lean_apply_4(v_toBind_5840_, lean_box(0), lean_box(0), v___x_5866_, v___f_5851_);
return v___x_5867_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg(lean_object* v_inst_5870_, lean_object* v_inst_5871_, lean_object* v_inst_5872_, lean_object* v_inst_5873_, lean_object* v_inst_5874_, lean_object* v_cctx_5875_, lean_object* v_ngen_5876_, lean_object* v_env_5877_, lean_object* v_act_5878_, lean_object* v_constantsPerTask_5879_){
_start:
{
lean_object* v___x_5880_; lean_object* v_moduleData_5881_; lean_object* v_toApplicative_5882_; lean_object* v_toBind_5883_; lean_object* v_n_5884_; lean_object* v___x_5885_; lean_object* v___x_5886_; lean_object* v___x_5887_; lean_object* v_toPure_5888_; lean_object* v___f_5889_; lean_object* v___x_5890_; lean_object* v___f_5891_; lean_object* v___x_5892_; 
v___x_5880_ = l_Lean_Environment_header(v_env_5877_);
v_moduleData_5881_ = lean_ctor_get(v___x_5880_, 6);
lean_inc_ref(v_moduleData_5881_);
lean_dec_ref(v___x_5880_);
v_toApplicative_5882_ = lean_ctor_get(v_inst_5870_, 0);
v_toBind_5883_ = lean_ctor_get(v_inst_5870_, 1);
lean_inc_n(v_toBind_5883_, 2);
v_n_5884_ = lean_array_get_size(v_moduleData_5881_);
lean_dec_ref(v_moduleData_5881_);
v___x_5885_ = lean_unsigned_to_nat(0u);
v___x_5886_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
lean_inc_ref_n(v_inst_5870_, 2);
v___x_5887_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(v_inst_5870_, v_inst_5874_, v_cctx_5875_, v_env_5877_, v_act_5878_, v_constantsPerTask_5879_, v_n_5884_, v_ngen_5876_, v___x_5886_, v___x_5885_, v___x_5885_, v___x_5885_);
v_toPure_5888_ = lean_ctor_get(v_toApplicative_5882_, 1);
lean_inc(v_toPure_5888_);
v___f_5889_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__0), 6, 4);
lean_closure_set(v___f_5889_, 0, v_inst_5870_);
lean_closure_set(v___f_5889_, 1, v_inst_5871_);
lean_closure_set(v___f_5889_, 2, v_inst_5872_);
lean_closure_set(v___f_5889_, 3, v_inst_5873_);
v___x_5890_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___closed__0));
v___f_5891_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__2), 7, 6);
lean_closure_set(v___f_5891_, 0, v___x_5885_);
lean_closure_set(v___f_5891_, 1, v___x_5890_);
lean_closure_set(v___f_5891_, 2, v_toPure_5888_);
lean_closure_set(v___f_5891_, 3, v_toBind_5883_);
lean_closure_set(v___f_5891_, 4, v_inst_5870_);
lean_closure_set(v___f_5891_, 5, v___f_5889_);
v___x_5892_ = lean_apply_4(v_toBind_5883_, lean_box(0), lean_box(0), v___x_5887_, v___f_5891_);
return v___x_5892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree(lean_object* v_m_5893_, lean_object* v_00_u03b1_5894_, lean_object* v_inst_5895_, lean_object* v_inst_5896_, lean_object* v_inst_5897_, lean_object* v_inst_5898_, lean_object* v_inst_5899_, lean_object* v_cctx_5900_, lean_object* v_ngen_5901_, lean_object* v_env_5902_, lean_object* v_act_5903_, lean_object* v_constantsPerTask_5904_){
_start:
{
lean_object* v___x_5905_; 
v___x_5905_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg(v_inst_5895_, v_inst_5896_, v_inst_5897_, v_inst_5898_, v_inst_5899_, v_cctx_5900_, v_ngen_5901_, v_env_5902_, v_act_5903_, v_constantsPerTask_5904_);
return v___x_5905_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0(void){
_start:
{
lean_object* v___x_5906_; lean_object* v___x_5907_; lean_object* v___x_5908_; 
v___x_5906_ = lean_box(0);
v___x_5907_ = lean_unsigned_to_nat(16u);
v___x_5908_ = lean_mk_array(v___x_5907_, v___x_5906_);
return v___x_5908_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1(void){
_start:
{
lean_object* v___x_5909_; lean_object* v___x_5910_; lean_object* v___x_5911_; 
v___x_5909_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0, &l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0);
v___x_5910_ = lean_unsigned_to_nat(0u);
v___x_5911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5911_, 0, v___x_5910_);
lean_ctor_set(v___x_5911_, 1, v___x_5909_);
return v___x_5911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createTreeCtx(lean_object* v_ctx_5912_){
_start:
{
lean_object* v_toCold_5913_; lean_object* v_ref_5914_; lean_object* v___x_5916_; uint8_t v_isShared_5917_; uint8_t v_isSharedCheck_5948_; 
v_toCold_5913_ = lean_ctor_get(v_ctx_5912_, 0);
v_ref_5914_ = lean_ctor_get(v_ctx_5912_, 2);
v_isSharedCheck_5948_ = !lean_is_exclusive(v_ctx_5912_);
if (v_isSharedCheck_5948_ == 0)
{
lean_object* v_unused_5949_; 
v_unused_5949_ = lean_ctor_get(v_ctx_5912_, 1);
lean_dec(v_unused_5949_);
v___x_5916_ = v_ctx_5912_;
v_isShared_5917_ = v_isSharedCheck_5948_;
goto v_resetjp_5915_;
}
else
{
lean_inc(v_ref_5914_);
lean_inc(v_toCold_5913_);
lean_dec(v_ctx_5912_);
v___x_5916_ = lean_box(0);
v_isShared_5917_ = v_isSharedCheck_5948_;
goto v_resetjp_5915_;
}
v_resetjp_5915_:
{
lean_object* v_fileName_5918_; lean_object* v_fileMap_5919_; lean_object* v_options_5920_; lean_object* v_maxRecDepth_5921_; lean_object* v___x_5923_; uint8_t v_isShared_5924_; uint8_t v_isSharedCheck_5939_; 
v_fileName_5918_ = lean_ctor_get(v_toCold_5913_, 0);
v_fileMap_5919_ = lean_ctor_get(v_toCold_5913_, 1);
v_options_5920_ = lean_ctor_get(v_toCold_5913_, 2);
v_maxRecDepth_5921_ = lean_ctor_get(v_toCold_5913_, 3);
v_isSharedCheck_5939_ = !lean_is_exclusive(v_toCold_5913_);
if (v_isSharedCheck_5939_ == 0)
{
lean_object* v_unused_5940_; lean_object* v_unused_5941_; lean_object* v_unused_5942_; lean_object* v_unused_5943_; lean_object* v_unused_5944_; lean_object* v_unused_5945_; lean_object* v_unused_5946_; lean_object* v_unused_5947_; 
v_unused_5940_ = lean_ctor_get(v_toCold_5913_, 11);
lean_dec(v_unused_5940_);
v_unused_5941_ = lean_ctor_get(v_toCold_5913_, 10);
lean_dec(v_unused_5941_);
v_unused_5942_ = lean_ctor_get(v_toCold_5913_, 9);
lean_dec(v_unused_5942_);
v_unused_5943_ = lean_ctor_get(v_toCold_5913_, 8);
lean_dec(v_unused_5943_);
v_unused_5944_ = lean_ctor_get(v_toCold_5913_, 7);
lean_dec(v_unused_5944_);
v_unused_5945_ = lean_ctor_get(v_toCold_5913_, 6);
lean_dec(v_unused_5945_);
v_unused_5946_ = lean_ctor_get(v_toCold_5913_, 5);
lean_dec(v_unused_5946_);
v_unused_5947_ = lean_ctor_get(v_toCold_5913_, 4);
lean_dec(v_unused_5947_);
v___x_5923_ = v_toCold_5913_;
v_isShared_5924_ = v_isSharedCheck_5939_;
goto v_resetjp_5922_;
}
else
{
lean_inc(v_maxRecDepth_5921_);
lean_inc(v_options_5920_);
lean_inc(v_fileMap_5919_);
lean_inc(v_fileName_5918_);
lean_dec(v_toCold_5913_);
v___x_5923_ = lean_box(0);
v_isShared_5924_ = v_isSharedCheck_5939_;
goto v_resetjp_5922_;
}
v_resetjp_5922_:
{
lean_object* v___x_5925_; lean_object* v___x_5926_; lean_object* v___x_5927_; lean_object* v___x_5928_; lean_object* v___x_5929_; lean_object* v___x_5930_; lean_object* v___x_5932_; 
v___x_5925_ = lean_box(0);
v___x_5926_ = lean_box(0);
v___x_5927_ = lean_unsigned_to_nat(0u);
v___x_5928_ = l_Lean_firstFrontendMacroScope;
v___x_5929_ = lean_box(0);
v___x_5930_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1, &l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1);
lean_inc_ref(v_options_5920_);
if (v_isShared_5924_ == 0)
{
lean_ctor_set(v___x_5923_, 11, v___x_5930_);
lean_ctor_set(v___x_5923_, 10, v___x_5929_);
lean_ctor_set(v___x_5923_, 9, v___x_5928_);
lean_ctor_set(v___x_5923_, 8, v___x_5925_);
lean_ctor_set(v___x_5923_, 7, v___x_5927_);
lean_ctor_set(v___x_5923_, 6, v___x_5927_);
lean_ctor_set(v___x_5923_, 5, v___x_5926_);
lean_ctor_set(v___x_5923_, 4, v___x_5925_);
v___x_5932_ = v___x_5923_;
goto v_reusejp_5931_;
}
else
{
lean_object* v_reuseFailAlloc_5938_; 
v_reuseFailAlloc_5938_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_5938_, 0, v_fileName_5918_);
lean_ctor_set(v_reuseFailAlloc_5938_, 1, v_fileMap_5919_);
lean_ctor_set(v_reuseFailAlloc_5938_, 2, v_options_5920_);
lean_ctor_set(v_reuseFailAlloc_5938_, 3, v_maxRecDepth_5921_);
lean_ctor_set(v_reuseFailAlloc_5938_, 4, v___x_5925_);
lean_ctor_set(v_reuseFailAlloc_5938_, 5, v___x_5926_);
lean_ctor_set(v_reuseFailAlloc_5938_, 6, v___x_5927_);
lean_ctor_set(v_reuseFailAlloc_5938_, 7, v___x_5927_);
lean_ctor_set(v_reuseFailAlloc_5938_, 8, v___x_5925_);
lean_ctor_set(v_reuseFailAlloc_5938_, 9, v___x_5928_);
lean_ctor_set(v_reuseFailAlloc_5938_, 10, v___x_5929_);
lean_ctor_set(v_reuseFailAlloc_5938_, 11, v___x_5930_);
v___x_5932_ = v_reuseFailAlloc_5938_;
goto v_reusejp_5931_;
}
v_reusejp_5931_:
{
uint8_t v___x_5933_; uint8_t v___x_5934_; lean_object* v___x_5936_; 
v___x_5933_ = l_Lean_getDiag(v_options_5920_);
lean_dec_ref(v_options_5920_);
v___x_5934_ = 0;
if (v_isShared_5917_ == 0)
{
lean_ctor_set(v___x_5916_, 1, v___x_5927_);
lean_ctor_set(v___x_5916_, 0, v___x_5932_);
v___x_5936_ = v___x_5916_;
goto v_reusejp_5935_;
}
else
{
lean_object* v_reuseFailAlloc_5937_; 
v_reuseFailAlloc_5937_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5937_, 0, v___x_5932_);
lean_ctor_set(v_reuseFailAlloc_5937_, 1, v___x_5927_);
lean_ctor_set(v_reuseFailAlloc_5937_, 2, v_ref_5914_);
v___x_5936_ = v_reuseFailAlloc_5937_;
goto v_reusejp_5935_;
}
v_reusejp_5935_:
{
lean_ctor_set_uint8(v___x_5936_, sizeof(void*)*3, v___x_5933_);
lean_ctor_set_uint8(v___x_5936_, sizeof(void*)*3 + 1, v___x_5934_);
return v___x_5936_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(lean_object* v_category_5950_, lean_object* v_opts_5951_, lean_object* v_act_5952_, lean_object* v_decl_5953_, lean_object* v___y_5954_, lean_object* v___y_5955_, lean_object* v___y_5956_, lean_object* v___y_5957_){
_start:
{
lean_object* v___x_5959_; lean_object* v___x_5960_; 
lean_inc(v___y_5957_);
lean_inc_ref(v___y_5956_);
lean_inc(v___y_5955_);
lean_inc_ref(v___y_5954_);
v___x_5959_ = lean_apply_4(v_act_5952_, v___y_5954_, v___y_5955_, v___y_5956_, v___y_5957_);
v___x_5960_ = l_Lean_profileitIOUnsafe___redArg(v_category_5950_, v_opts_5951_, v___x_5959_, v_decl_5953_);
return v___x_5960_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg___boxed(lean_object* v_category_5961_, lean_object* v_opts_5962_, lean_object* v_act_5963_, lean_object* v_decl_5964_, lean_object* v___y_5965_, lean_object* v___y_5966_, lean_object* v___y_5967_, lean_object* v___y_5968_, lean_object* v___y_5969_){
_start:
{
lean_object* v_res_5970_; 
v_res_5970_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v_category_5961_, v_opts_5962_, v_act_5963_, v_decl_5964_, v___y_5965_, v___y_5966_, v___y_5967_, v___y_5968_);
lean_dec(v___y_5968_);
lean_dec_ref(v___y_5967_);
lean_dec(v___y_5966_);
lean_dec_ref(v___y_5965_);
lean_dec_ref(v_opts_5962_);
lean_dec_ref(v_category_5961_);
return v_res_5970_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1(lean_object* v_00_u03b1_5971_, lean_object* v_category_5972_, lean_object* v_opts_5973_, lean_object* v_act_5974_, lean_object* v_decl_5975_, lean_object* v___y_5976_, lean_object* v___y_5977_, lean_object* v___y_5978_, lean_object* v___y_5979_){
_start:
{
lean_object* v___x_5981_; 
v___x_5981_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v_category_5972_, v_opts_5973_, v_act_5974_, v_decl_5975_, v___y_5976_, v___y_5977_, v___y_5978_, v___y_5979_);
return v___x_5981_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___boxed(lean_object* v_00_u03b1_5982_, lean_object* v_category_5983_, lean_object* v_opts_5984_, lean_object* v_act_5985_, lean_object* v_decl_5986_, lean_object* v___y_5987_, lean_object* v___y_5988_, lean_object* v___y_5989_, lean_object* v___y_5990_, lean_object* v___y_5991_){
_start:
{
lean_object* v_res_5992_; 
v_res_5992_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1(v_00_u03b1_5982_, v_category_5983_, v_opts_5984_, v_act_5985_, v_decl_5986_, v___y_5987_, v___y_5988_, v___y_5989_, v___y_5990_);
lean_dec(v___y_5990_);
lean_dec_ref(v___y_5989_);
lean_dec(v___y_5988_);
lean_dec_ref(v___y_5987_);
lean_dec_ref(v_opts_5984_);
lean_dec_ref(v_category_5983_);
return v_res_5992_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(lean_object* v_cctx_5993_, lean_object* v_env_5994_, lean_object* v_act_5995_, lean_object* v_constantsPerTask_5996_, lean_object* v_n_5997_, lean_object* v_ngen_5998_, lean_object* v_tasks_5999_, lean_object* v_start_6000_, lean_object* v_cnt_6001_, lean_object* v_idx_6002_){
_start:
{
lean_object* v___x_6004_; lean_object* v_moduleData_6005_; lean_object* v___x_6006_; uint8_t v___x_6007_; 
v___x_6004_ = l_Lean_Environment_header(v_env_5994_);
v_moduleData_6005_ = lean_ctor_get(v___x_6004_, 6);
lean_inc_ref(v_moduleData_6005_);
lean_dec_ref(v___x_6004_);
v___x_6006_ = lean_array_get_size(v_moduleData_6005_);
v___x_6007_ = lean_nat_dec_lt(v_idx_6002_, v___x_6006_);
if (v___x_6007_ == 0)
{
uint8_t v___x_6008_; 
lean_dec_ref(v_moduleData_6005_);
lean_dec(v_idx_6002_);
lean_dec(v_cnt_6001_);
v___x_6008_ = lean_nat_dec_lt(v_start_6000_, v_n_5997_);
if (v___x_6008_ == 0)
{
lean_object* v___x_6009_; 
lean_dec(v_start_6000_);
lean_dec_ref(v_ngen_5998_);
lean_dec(v_n_5997_);
lean_dec_ref(v_act_5995_);
lean_dec_ref(v_env_5994_);
lean_dec_ref(v_cctx_5993_);
v___x_6009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6009_, 0, v_tasks_5999_);
return v___x_6009_;
}
else
{
lean_object* v_namePrefix_6010_; lean_object* v_idx_6011_; lean_object* v___x_6013_; uint8_t v_isShared_6014_; uint8_t v_isSharedCheck_6025_; 
v_namePrefix_6010_ = lean_ctor_get(v_ngen_5998_, 0);
v_idx_6011_ = lean_ctor_get(v_ngen_5998_, 1);
v_isSharedCheck_6025_ = !lean_is_exclusive(v_ngen_5998_);
if (v_isSharedCheck_6025_ == 0)
{
v___x_6013_ = v_ngen_5998_;
v_isShared_6014_ = v_isSharedCheck_6025_;
goto v_resetjp_6012_;
}
else
{
lean_inc(v_idx_6011_);
lean_inc(v_namePrefix_6010_);
lean_dec(v_ngen_5998_);
v___x_6013_ = lean_box(0);
v_isShared_6014_ = v_isSharedCheck_6025_;
goto v_resetjp_6012_;
}
v_resetjp_6012_:
{
lean_object* v___x_6015_; lean_object* v___x_6016_; lean_object* v___x_6018_; 
v___x_6015_ = l_Lean_Name_num___override(v_namePrefix_6010_, v_idx_6011_);
v___x_6016_ = lean_unsigned_to_nat(1u);
if (v_isShared_6014_ == 0)
{
lean_ctor_set(v___x_6013_, 1, v___x_6016_);
lean_ctor_set(v___x_6013_, 0, v___x_6015_);
v___x_6018_ = v___x_6013_;
goto v_reusejp_6017_;
}
else
{
lean_object* v_reuseFailAlloc_6024_; 
v_reuseFailAlloc_6024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6024_, 0, v___x_6015_);
lean_ctor_set(v_reuseFailAlloc_6024_, 1, v___x_6016_);
v___x_6018_ = v_reuseFailAlloc_6024_;
goto v_reusejp_6017_;
}
v_reusejp_6017_:
{
lean_object* v___x_6019_; lean_object* v___x_6020_; lean_object* v___x_6021_; lean_object* v___x_6022_; lean_object* v___x_6023_; 
v___x_6019_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_6019_, 0, lean_box(0));
lean_closure_set(v___x_6019_, 1, v_cctx_5993_);
lean_closure_set(v___x_6019_, 2, v___x_6018_);
lean_closure_set(v___x_6019_, 3, v_env_5994_);
lean_closure_set(v___x_6019_, 4, v_act_5995_);
lean_closure_set(v___x_6019_, 5, v_start_6000_);
lean_closure_set(v___x_6019_, 6, v_n_5997_);
v___x_6020_ = lean_unsigned_to_nat(0u);
v___x_6021_ = lean_io_as_task(v___x_6019_, v___x_6020_);
v___x_6022_ = lean_array_push(v_tasks_5999_, v___x_6021_);
v___x_6023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6023_, 0, v___x_6022_);
return v___x_6023_;
}
}
}
}
else
{
lean_object* v_mdata_6026_; lean_object* v_constants_6027_; lean_object* v___x_6028_; lean_object* v_cnt_6029_; uint8_t v___x_6030_; 
v_mdata_6026_ = lean_array_fget(v_moduleData_6005_, v_idx_6002_);
lean_dec_ref(v_moduleData_6005_);
v_constants_6027_ = lean_ctor_get(v_mdata_6026_, 2);
lean_inc_ref(v_constants_6027_);
lean_dec(v_mdata_6026_);
v___x_6028_ = lean_array_get_size(v_constants_6027_);
lean_dec_ref(v_constants_6027_);
v_cnt_6029_ = lean_nat_add(v_cnt_6001_, v___x_6028_);
lean_dec(v_cnt_6001_);
v___x_6030_ = lean_nat_dec_lt(v_constantsPerTask_5996_, v_cnt_6029_);
if (v___x_6030_ == 0)
{
lean_object* v___x_6031_; lean_object* v___x_6032_; 
v___x_6031_ = lean_unsigned_to_nat(1u);
v___x_6032_ = lean_nat_add(v_idx_6002_, v___x_6031_);
lean_dec(v_idx_6002_);
v_cnt_6001_ = v_cnt_6029_;
v_idx_6002_ = v___x_6032_;
goto _start;
}
else
{
lean_object* v_namePrefix_6034_; lean_object* v_idx_6035_; lean_object* v___x_6037_; uint8_t v_isShared_6038_; uint8_t v_isSharedCheck_6052_; 
lean_dec(v_cnt_6029_);
v_namePrefix_6034_ = lean_ctor_get(v_ngen_5998_, 0);
v_idx_6035_ = lean_ctor_get(v_ngen_5998_, 1);
v_isSharedCheck_6052_ = !lean_is_exclusive(v_ngen_5998_);
if (v_isSharedCheck_6052_ == 0)
{
v___x_6037_ = v_ngen_5998_;
v_isShared_6038_ = v_isSharedCheck_6052_;
goto v_resetjp_6036_;
}
else
{
lean_inc(v_idx_6035_);
lean_inc(v_namePrefix_6034_);
lean_dec(v_ngen_5998_);
v___x_6037_ = lean_box(0);
v_isShared_6038_ = v_isSharedCheck_6052_;
goto v_resetjp_6036_;
}
v_resetjp_6036_:
{
lean_object* v___x_6039_; lean_object* v___x_6040_; lean_object* v___x_6042_; 
lean_inc(v_idx_6035_);
lean_inc(v_namePrefix_6034_);
v___x_6039_ = l_Lean_Name_num___override(v_namePrefix_6034_, v_idx_6035_);
v___x_6040_ = lean_unsigned_to_nat(1u);
if (v_isShared_6038_ == 0)
{
lean_ctor_set(v___x_6037_, 1, v___x_6040_);
lean_ctor_set(v___x_6037_, 0, v___x_6039_);
v___x_6042_ = v___x_6037_;
goto v_reusejp_6041_;
}
else
{
lean_object* v_reuseFailAlloc_6051_; 
v_reuseFailAlloc_6051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6051_, 0, v___x_6039_);
lean_ctor_set(v_reuseFailAlloc_6051_, 1, v___x_6040_);
v___x_6042_ = v_reuseFailAlloc_6051_;
goto v_reusejp_6041_;
}
v_reusejp_6041_:
{
lean_object* v___x_6043_; lean_object* v___x_6044_; lean_object* v___x_6045_; lean_object* v___x_6046_; lean_object* v___x_6047_; lean_object* v___x_6048_; lean_object* v___x_6049_; 
v___x_6043_ = lean_nat_add(v_idx_6002_, v___x_6040_);
lean_dec(v_idx_6002_);
lean_inc_n(v___x_6043_, 2);
lean_inc_ref(v_act_5995_);
lean_inc_ref(v_env_5994_);
lean_inc_ref(v_cctx_5993_);
v___x_6044_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_6044_, 0, lean_box(0));
lean_closure_set(v___x_6044_, 1, v_cctx_5993_);
lean_closure_set(v___x_6044_, 2, v___x_6042_);
lean_closure_set(v___x_6044_, 3, v_env_5994_);
lean_closure_set(v___x_6044_, 4, v_act_5995_);
lean_closure_set(v___x_6044_, 5, v_start_6000_);
lean_closure_set(v___x_6044_, 6, v___x_6043_);
v___x_6045_ = lean_unsigned_to_nat(0u);
v___x_6046_ = lean_io_as_task(v___x_6044_, v___x_6045_);
v___x_6047_ = lean_nat_add(v_idx_6035_, v___x_6040_);
lean_dec(v_idx_6035_);
v___x_6048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6048_, 0, v_namePrefix_6034_);
lean_ctor_set(v___x_6048_, 1, v___x_6047_);
v___x_6049_ = lean_array_push(v_tasks_5999_, v___x_6046_);
v_ngen_5998_ = v___x_6048_;
v_tasks_5999_ = v___x_6049_;
v_start_6000_ = v___x_6043_;
v_cnt_6001_ = v___x_6045_;
v_idx_6002_ = v___x_6043_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg___boxed(lean_object* v_cctx_6053_, lean_object* v_env_6054_, lean_object* v_act_6055_, lean_object* v_constantsPerTask_6056_, lean_object* v_n_6057_, lean_object* v_ngen_6058_, lean_object* v_tasks_6059_, lean_object* v_start_6060_, lean_object* v_cnt_6061_, lean_object* v_idx_6062_, lean_object* v___y_6063_){
_start:
{
lean_object* v_res_6064_; 
v_res_6064_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(v_cctx_6053_, v_env_6054_, v_act_6055_, v_constantsPerTask_6056_, v_n_6057_, v_ngen_6058_, v_tasks_6059_, v_start_6060_, v_cnt_6061_, v_idx_6062_);
lean_dec(v_constantsPerTask_6056_);
return v_res_6064_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0(uint8_t v_suppressElabErrors_6073_, uint8_t v___y_6074_, lean_object* v_x_6075_){
_start:
{
if (lean_obj_tag(v_x_6075_) == 1)
{
lean_object* v_pre_6076_; 
v_pre_6076_ = lean_ctor_get(v_x_6075_, 0);
switch(lean_obj_tag(v_pre_6076_))
{
case 1:
{
lean_object* v_pre_6077_; 
v_pre_6077_ = lean_ctor_get(v_pre_6076_, 0);
switch(lean_obj_tag(v_pre_6077_))
{
case 0:
{
lean_object* v_str_6078_; lean_object* v_str_6079_; lean_object* v___x_6080_; uint8_t v___x_6081_; 
v_str_6078_ = lean_ctor_get(v_x_6075_, 1);
v_str_6079_ = lean_ctor_get(v_pre_6076_, 1);
v___x_6080_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__0));
v___x_6081_ = lean_string_dec_eq(v_str_6079_, v___x_6080_);
if (v___x_6081_ == 0)
{
lean_object* v___x_6082_; uint8_t v___x_6083_; 
v___x_6082_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__1));
v___x_6083_ = lean_string_dec_eq(v_str_6079_, v___x_6082_);
if (v___x_6083_ == 0)
{
return v___x_6083_;
}
else
{
lean_object* v___x_6084_; uint8_t v___x_6085_; 
v___x_6084_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__2));
v___x_6085_ = lean_string_dec_eq(v_str_6078_, v___x_6084_);
if (v___x_6085_ == 0)
{
return v___x_6085_;
}
else
{
return v_suppressElabErrors_6073_;
}
}
}
else
{
lean_object* v___x_6086_; uint8_t v___x_6087_; 
v___x_6086_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__3));
v___x_6087_ = lean_string_dec_eq(v_str_6078_, v___x_6086_);
if (v___x_6087_ == 0)
{
return v___x_6087_;
}
else
{
return v_suppressElabErrors_6073_;
}
}
}
case 1:
{
lean_object* v_pre_6088_; 
v_pre_6088_ = lean_ctor_get(v_pre_6077_, 0);
if (lean_obj_tag(v_pre_6088_) == 0)
{
lean_object* v_str_6089_; lean_object* v_str_6090_; lean_object* v_str_6091_; lean_object* v___x_6092_; uint8_t v___x_6093_; 
v_str_6089_ = lean_ctor_get(v_x_6075_, 1);
v_str_6090_ = lean_ctor_get(v_pre_6076_, 1);
v_str_6091_ = lean_ctor_get(v_pre_6077_, 1);
v___x_6092_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__4));
v___x_6093_ = lean_string_dec_eq(v_str_6091_, v___x_6092_);
if (v___x_6093_ == 0)
{
return v___x_6093_;
}
else
{
lean_object* v___x_6094_; uint8_t v___x_6095_; 
v___x_6094_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__5));
v___x_6095_ = lean_string_dec_eq(v_str_6090_, v___x_6094_);
if (v___x_6095_ == 0)
{
return v___x_6095_;
}
else
{
lean_object* v___x_6096_; uint8_t v___x_6097_; 
v___x_6096_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__6));
v___x_6097_ = lean_string_dec_eq(v_str_6089_, v___x_6096_);
if (v___x_6097_ == 0)
{
return v___x_6097_;
}
else
{
return v_suppressElabErrors_6073_;
}
}
}
}
else
{
return v___y_6074_;
}
}
default: 
{
return v___y_6074_;
}
}
}
case 0:
{
lean_object* v_str_6098_; lean_object* v___x_6099_; uint8_t v___x_6100_; 
v_str_6098_ = lean_ctor_get(v_x_6075_, 1);
v___x_6099_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__7));
v___x_6100_ = lean_string_dec_eq(v_str_6098_, v___x_6099_);
if (v___x_6100_ == 0)
{
return v___x_6100_;
}
else
{
return v_suppressElabErrors_6073_;
}
}
default: 
{
return v___y_6074_;
}
}
}
else
{
return v___y_6074_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___boxed(lean_object* v_suppressElabErrors_6101_, lean_object* v___y_6102_, lean_object* v_x_6103_){
_start:
{
uint8_t v_suppressElabErrors_boxed_6104_; uint8_t v___y_8081__boxed_6105_; uint8_t v_res_6106_; lean_object* v_r_6107_; 
v_suppressElabErrors_boxed_6104_ = lean_unbox(v_suppressElabErrors_6101_);
v___y_8081__boxed_6105_ = lean_unbox(v___y_6102_);
v_res_6106_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0(v_suppressElabErrors_boxed_6104_, v___y_8081__boxed_6105_, v_x_6103_);
lean_dec(v_x_6103_);
v_r_6107_ = lean_box(v_res_6106_);
return v_r_6107_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7(lean_object* v_ref_6109_, lean_object* v_msgData_6110_, uint8_t v_severity_6111_, uint8_t v_isSilent_6112_, lean_object* v___y_6113_, lean_object* v___y_6114_, lean_object* v___y_6115_, lean_object* v___y_6116_){
_start:
{
lean_object* v___y_6119_; lean_object* v___y_6120_; lean_object* v___y_6121_; lean_object* v___y_6122_; uint8_t v___y_6123_; uint8_t v___y_6124_; lean_object* v___y_6125_; lean_object* v___y_6126_; lean_object* v___y_6127_; lean_object* v___y_6156_; uint8_t v___y_6157_; lean_object* v___y_6158_; uint8_t v___y_6159_; uint8_t v___y_6160_; lean_object* v___y_6161_; lean_object* v___y_6162_; lean_object* v___y_6163_; lean_object* v___y_6181_; lean_object* v___y_6182_; lean_object* v___y_6183_; uint8_t v___y_6184_; lean_object* v___y_6185_; uint8_t v___y_6186_; uint8_t v___y_6187_; lean_object* v___y_6188_; lean_object* v___y_6192_; lean_object* v___y_6193_; uint8_t v___y_6194_; lean_object* v___y_6195_; uint8_t v___y_6196_; lean_object* v___y_6197_; uint8_t v___y_6198_; uint8_t v___x_6203_; lean_object* v___y_6205_; lean_object* v___y_6206_; lean_object* v___y_6207_; lean_object* v___y_6208_; uint8_t v___y_6209_; uint8_t v___y_6210_; uint8_t v___y_6211_; uint8_t v___y_6213_; uint8_t v___x_6229_; 
v___x_6203_ = 2;
v___x_6229_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6111_, v___x_6203_);
if (v___x_6229_ == 0)
{
v___y_6213_ = v___x_6229_;
goto v___jp_6212_;
}
else
{
uint8_t v___x_6230_; 
lean_inc_ref(v_msgData_6110_);
v___x_6230_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_6110_);
v___y_6213_ = v___x_6230_;
goto v___jp_6212_;
}
v___jp_6118_:
{
lean_object* v___x_6128_; lean_object* v_toCold_6129_; lean_object* v_currNamespace_6130_; lean_object* v_openDecls_6131_; lean_object* v_env_6132_; lean_object* v_nextMacroScope_6133_; lean_object* v_ngen_6134_; lean_object* v_auxDeclNGen_6135_; lean_object* v_traceState_6136_; lean_object* v_cache_6137_; lean_object* v_messages_6138_; lean_object* v_infoState_6139_; lean_object* v_snapshotTasks_6140_; lean_object* v___x_6142_; uint8_t v_isShared_6143_; uint8_t v_isSharedCheck_6154_; 
v___x_6128_ = lean_st_ref_take(v___y_6127_);
v_toCold_6129_ = lean_ctor_get(v___y_6126_, 0);
v_currNamespace_6130_ = lean_ctor_get(v_toCold_6129_, 4);
v_openDecls_6131_ = lean_ctor_get(v_toCold_6129_, 5);
v_env_6132_ = lean_ctor_get(v___x_6128_, 0);
v_nextMacroScope_6133_ = lean_ctor_get(v___x_6128_, 1);
v_ngen_6134_ = lean_ctor_get(v___x_6128_, 2);
v_auxDeclNGen_6135_ = lean_ctor_get(v___x_6128_, 3);
v_traceState_6136_ = lean_ctor_get(v___x_6128_, 4);
v_cache_6137_ = lean_ctor_get(v___x_6128_, 5);
v_messages_6138_ = lean_ctor_get(v___x_6128_, 6);
v_infoState_6139_ = lean_ctor_get(v___x_6128_, 7);
v_snapshotTasks_6140_ = lean_ctor_get(v___x_6128_, 8);
v_isSharedCheck_6154_ = !lean_is_exclusive(v___x_6128_);
if (v_isSharedCheck_6154_ == 0)
{
v___x_6142_ = v___x_6128_;
v_isShared_6143_ = v_isSharedCheck_6154_;
goto v_resetjp_6141_;
}
else
{
lean_inc(v_snapshotTasks_6140_);
lean_inc(v_infoState_6139_);
lean_inc(v_messages_6138_);
lean_inc(v_cache_6137_);
lean_inc(v_traceState_6136_);
lean_inc(v_auxDeclNGen_6135_);
lean_inc(v_ngen_6134_);
lean_inc(v_nextMacroScope_6133_);
lean_inc(v_env_6132_);
lean_dec(v___x_6128_);
v___x_6142_ = lean_box(0);
v_isShared_6143_ = v_isSharedCheck_6154_;
goto v_resetjp_6141_;
}
v_resetjp_6141_:
{
lean_object* v___x_6144_; lean_object* v___x_6145_; lean_object* v___x_6146_; lean_object* v___x_6147_; lean_object* v___x_6149_; 
lean_inc(v_openDecls_6131_);
lean_inc(v_currNamespace_6130_);
v___x_6144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6144_, 0, v_currNamespace_6130_);
lean_ctor_set(v___x_6144_, 1, v_openDecls_6131_);
v___x_6145_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6145_, 0, v___x_6144_);
lean_ctor_set(v___x_6145_, 1, v___y_6120_);
lean_inc_ref(v___y_6125_);
lean_inc_ref(v___y_6121_);
v___x_6146_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_6146_, 0, v___y_6121_);
lean_ctor_set(v___x_6146_, 1, v___y_6119_);
lean_ctor_set(v___x_6146_, 2, v___y_6122_);
lean_ctor_set(v___x_6146_, 3, v___y_6125_);
lean_ctor_set(v___x_6146_, 4, v___x_6145_);
lean_ctor_set_uint8(v___x_6146_, sizeof(void*)*5, v___y_6124_);
lean_ctor_set_uint8(v___x_6146_, sizeof(void*)*5 + 1, v___y_6123_);
lean_ctor_set_uint8(v___x_6146_, sizeof(void*)*5 + 2, v_isSilent_6112_);
v___x_6147_ = l_Lean_MessageLog_add(v___x_6146_, v_messages_6138_);
if (v_isShared_6143_ == 0)
{
lean_ctor_set(v___x_6142_, 6, v___x_6147_);
v___x_6149_ = v___x_6142_;
goto v_reusejp_6148_;
}
else
{
lean_object* v_reuseFailAlloc_6153_; 
v_reuseFailAlloc_6153_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6153_, 0, v_env_6132_);
lean_ctor_set(v_reuseFailAlloc_6153_, 1, v_nextMacroScope_6133_);
lean_ctor_set(v_reuseFailAlloc_6153_, 2, v_ngen_6134_);
lean_ctor_set(v_reuseFailAlloc_6153_, 3, v_auxDeclNGen_6135_);
lean_ctor_set(v_reuseFailAlloc_6153_, 4, v_traceState_6136_);
lean_ctor_set(v_reuseFailAlloc_6153_, 5, v_cache_6137_);
lean_ctor_set(v_reuseFailAlloc_6153_, 6, v___x_6147_);
lean_ctor_set(v_reuseFailAlloc_6153_, 7, v_infoState_6139_);
lean_ctor_set(v_reuseFailAlloc_6153_, 8, v_snapshotTasks_6140_);
v___x_6149_ = v_reuseFailAlloc_6153_;
goto v_reusejp_6148_;
}
v_reusejp_6148_:
{
lean_object* v___x_6150_; lean_object* v___x_6151_; lean_object* v___x_6152_; 
v___x_6150_ = lean_st_ref_put(v___y_6127_, v___x_6149_);
v___x_6151_ = lean_box(0);
v___x_6152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6152_, 0, v___x_6151_);
return v___x_6152_;
}
}
}
v___jp_6155_:
{
lean_object* v___x_6164_; lean_object* v___x_6165_; lean_object* v_a_6166_; lean_object* v___x_6168_; uint8_t v_isShared_6169_; uint8_t v_isSharedCheck_6179_; 
v___x_6164_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_6110_);
v___x_6165_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(v___x_6164_, v___y_6113_, v___y_6114_, v___y_6115_, v___y_6116_);
v_a_6166_ = lean_ctor_get(v___x_6165_, 0);
v_isSharedCheck_6179_ = !lean_is_exclusive(v___x_6165_);
if (v_isSharedCheck_6179_ == 0)
{
v___x_6168_ = v___x_6165_;
v_isShared_6169_ = v_isSharedCheck_6179_;
goto v_resetjp_6167_;
}
else
{
lean_inc(v_a_6166_);
lean_dec(v___x_6165_);
v___x_6168_ = lean_box(0);
v_isShared_6169_ = v_isSharedCheck_6179_;
goto v_resetjp_6167_;
}
v_resetjp_6167_:
{
lean_object* v___x_6170_; lean_object* v___x_6171_; lean_object* v___x_6172_; lean_object* v___x_6173_; 
lean_inc_ref_n(v___y_6161_, 2);
v___x_6170_ = l_Lean_FileMap_toPosition(v___y_6161_, v___y_6162_);
lean_dec(v___y_6162_);
v___x_6171_ = l_Lean_FileMap_toPosition(v___y_6161_, v___y_6163_);
lean_dec(v___y_6163_);
v___x_6172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6172_, 0, v___x_6171_);
v___x_6173_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___closed__0));
if (v___y_6157_ == 0)
{
lean_del_object(v___x_6168_);
lean_dec_ref(v___y_6156_);
v___y_6119_ = v___x_6170_;
v___y_6120_ = v_a_6166_;
v___y_6121_ = v___y_6158_;
v___y_6122_ = v___x_6172_;
v___y_6123_ = v___y_6160_;
v___y_6124_ = v___y_6159_;
v___y_6125_ = v___x_6173_;
v___y_6126_ = v___y_6115_;
v___y_6127_ = v___y_6116_;
goto v___jp_6118_;
}
else
{
uint8_t v___x_6174_; 
lean_inc(v_a_6166_);
v___x_6174_ = l_Lean_MessageData_hasTag(v___y_6156_, v_a_6166_);
if (v___x_6174_ == 0)
{
lean_object* v___x_6175_; lean_object* v___x_6177_; 
lean_dec_ref_known(v___x_6172_, 1);
lean_dec_ref(v___x_6170_);
lean_dec(v_a_6166_);
v___x_6175_ = lean_box(0);
if (v_isShared_6169_ == 0)
{
lean_ctor_set(v___x_6168_, 0, v___x_6175_);
v___x_6177_ = v___x_6168_;
goto v_reusejp_6176_;
}
else
{
lean_object* v_reuseFailAlloc_6178_; 
v_reuseFailAlloc_6178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6178_, 0, v___x_6175_);
v___x_6177_ = v_reuseFailAlloc_6178_;
goto v_reusejp_6176_;
}
v_reusejp_6176_:
{
return v___x_6177_;
}
}
else
{
lean_del_object(v___x_6168_);
v___y_6119_ = v___x_6170_;
v___y_6120_ = v_a_6166_;
v___y_6121_ = v___y_6158_;
v___y_6122_ = v___x_6172_;
v___y_6123_ = v___y_6160_;
v___y_6124_ = v___y_6159_;
v___y_6125_ = v___x_6173_;
v___y_6126_ = v___y_6115_;
v___y_6127_ = v___y_6116_;
goto v___jp_6118_;
}
}
}
}
v___jp_6180_:
{
lean_object* v___x_6189_; 
v___x_6189_ = l_Lean_Syntax_getTailPos_x3f(v___y_6182_, v___y_6187_);
lean_dec(v___y_6182_);
if (lean_obj_tag(v___x_6189_) == 0)
{
lean_inc(v___y_6188_);
v___y_6156_ = v___y_6181_;
v___y_6157_ = v___y_6184_;
v___y_6158_ = v___y_6183_;
v___y_6159_ = v___y_6187_;
v___y_6160_ = v___y_6186_;
v___y_6161_ = v___y_6185_;
v___y_6162_ = v___y_6188_;
v___y_6163_ = v___y_6188_;
goto v___jp_6155_;
}
else
{
lean_object* v_val_6190_; 
v_val_6190_ = lean_ctor_get(v___x_6189_, 0);
lean_inc(v_val_6190_);
lean_dec_ref_known(v___x_6189_, 1);
v___y_6156_ = v___y_6181_;
v___y_6157_ = v___y_6184_;
v___y_6158_ = v___y_6183_;
v___y_6159_ = v___y_6187_;
v___y_6160_ = v___y_6186_;
v___y_6161_ = v___y_6185_;
v___y_6162_ = v___y_6188_;
v___y_6163_ = v_val_6190_;
goto v___jp_6155_;
}
}
v___jp_6191_:
{
lean_object* v_ref_6199_; lean_object* v___x_6200_; 
v_ref_6199_ = l_Lean_replaceRef(v_ref_6109_, v___y_6193_);
v___x_6200_ = l_Lean_Syntax_getPos_x3f(v_ref_6199_, v___y_6196_);
if (lean_obj_tag(v___x_6200_) == 0)
{
lean_object* v___x_6201_; 
v___x_6201_ = lean_unsigned_to_nat(0u);
v___y_6181_ = v___y_6192_;
v___y_6182_ = v_ref_6199_;
v___y_6183_ = v___y_6195_;
v___y_6184_ = v___y_6194_;
v___y_6185_ = v___y_6197_;
v___y_6186_ = v___y_6198_;
v___y_6187_ = v___y_6196_;
v___y_6188_ = v___x_6201_;
goto v___jp_6180_;
}
else
{
lean_object* v_val_6202_; 
v_val_6202_ = lean_ctor_get(v___x_6200_, 0);
lean_inc(v_val_6202_);
lean_dec_ref_known(v___x_6200_, 1);
v___y_6181_ = v___y_6192_;
v___y_6182_ = v_ref_6199_;
v___y_6183_ = v___y_6195_;
v___y_6184_ = v___y_6194_;
v___y_6185_ = v___y_6197_;
v___y_6186_ = v___y_6198_;
v___y_6187_ = v___y_6196_;
v___y_6188_ = v_val_6202_;
goto v___jp_6180_;
}
}
v___jp_6204_:
{
if (v___y_6211_ == 0)
{
v___y_6192_ = v___y_6207_;
v___y_6193_ = v___y_6208_;
v___y_6194_ = v___y_6209_;
v___y_6195_ = v___y_6205_;
v___y_6196_ = v___y_6210_;
v___y_6197_ = v___y_6206_;
v___y_6198_ = v_severity_6111_;
goto v___jp_6191_;
}
else
{
v___y_6192_ = v___y_6207_;
v___y_6193_ = v___y_6208_;
v___y_6194_ = v___y_6209_;
v___y_6195_ = v___y_6205_;
v___y_6196_ = v___y_6210_;
v___y_6197_ = v___y_6206_;
v___y_6198_ = v___x_6203_;
goto v___jp_6191_;
}
}
v___jp_6212_:
{
if (v___y_6213_ == 0)
{
lean_object* v_toCold_6214_; lean_object* v_ref_6215_; uint8_t v_suppressElabErrors_6216_; lean_object* v_fileName_6217_; lean_object* v_fileMap_6218_; lean_object* v_options_6219_; lean_object* v___x_6220_; lean_object* v___x_6221_; lean_object* v___f_6222_; uint8_t v___x_6223_; uint8_t v___x_6224_; 
v_toCold_6214_ = lean_ctor_get(v___y_6115_, 0);
v_ref_6215_ = lean_ctor_get(v___y_6115_, 2);
v_suppressElabErrors_6216_ = lean_ctor_get_uint8(v___y_6115_, sizeof(void*)*3 + 1);
v_fileName_6217_ = lean_ctor_get(v_toCold_6214_, 0);
v_fileMap_6218_ = lean_ctor_get(v_toCold_6214_, 1);
v_options_6219_ = lean_ctor_get(v_toCold_6214_, 2);
v___x_6220_ = lean_box(v_suppressElabErrors_6216_);
v___x_6221_ = lean_box(v___y_6213_);
v___f_6222_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_6222_, 0, v___x_6220_);
lean_closure_set(v___f_6222_, 1, v___x_6221_);
v___x_6223_ = 1;
v___x_6224_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6111_, v___x_6223_);
if (v___x_6224_ == 0)
{
v___y_6205_ = v_fileName_6217_;
v___y_6206_ = v_fileMap_6218_;
v___y_6207_ = v___f_6222_;
v___y_6208_ = v_ref_6215_;
v___y_6209_ = v_suppressElabErrors_6216_;
v___y_6210_ = v___y_6213_;
v___y_6211_ = v___x_6224_;
goto v___jp_6204_;
}
else
{
lean_object* v___x_6225_; uint8_t v___x_6226_; 
v___x_6225_ = l_Lean_warningAsError;
v___x_6226_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(v_options_6219_, v___x_6225_);
v___y_6205_ = v_fileName_6217_;
v___y_6206_ = v_fileMap_6218_;
v___y_6207_ = v___f_6222_;
v___y_6208_ = v_ref_6215_;
v___y_6209_ = v_suppressElabErrors_6216_;
v___y_6210_ = v___y_6213_;
v___y_6211_ = v___x_6226_;
goto v___jp_6204_;
}
}
else
{
lean_object* v___x_6227_; lean_object* v___x_6228_; 
lean_dec_ref(v_msgData_6110_);
v___x_6227_ = lean_box(0);
v___x_6228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6228_, 0, v___x_6227_);
return v___x_6228_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___boxed(lean_object* v_ref_6231_, lean_object* v_msgData_6232_, lean_object* v_severity_6233_, lean_object* v_isSilent_6234_, lean_object* v___y_6235_, lean_object* v___y_6236_, lean_object* v___y_6237_, lean_object* v___y_6238_, lean_object* v___y_6239_){
_start:
{
uint8_t v_severity_boxed_6240_; uint8_t v_isSilent_boxed_6241_; lean_object* v_res_6242_; 
v_severity_boxed_6240_ = lean_unbox(v_severity_6233_);
v_isSilent_boxed_6241_ = lean_unbox(v_isSilent_6234_);
v_res_6242_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7(v_ref_6231_, v_msgData_6232_, v_severity_boxed_6240_, v_isSilent_boxed_6241_, v___y_6235_, v___y_6236_, v___y_6237_, v___y_6238_);
lean_dec(v___y_6238_);
lean_dec_ref(v___y_6237_);
lean_dec(v___y_6236_);
lean_dec_ref(v___y_6235_);
lean_dec(v_ref_6231_);
return v_res_6242_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3(lean_object* v_msgData_6243_, uint8_t v_severity_6244_, uint8_t v_isSilent_6245_, lean_object* v___y_6246_, lean_object* v___y_6247_, lean_object* v___y_6248_, lean_object* v___y_6249_){
_start:
{
lean_object* v_ref_6251_; lean_object* v___x_6252_; 
v_ref_6251_ = lean_ctor_get(v___y_6248_, 2);
v___x_6252_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7(v_ref_6251_, v_msgData_6243_, v_severity_6244_, v_isSilent_6245_, v___y_6246_, v___y_6247_, v___y_6248_, v___y_6249_);
return v___x_6252_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_msgData_6253_, lean_object* v_severity_6254_, lean_object* v_isSilent_6255_, lean_object* v___y_6256_, lean_object* v___y_6257_, lean_object* v___y_6258_, lean_object* v___y_6259_, lean_object* v___y_6260_){
_start:
{
uint8_t v_severity_boxed_6261_; uint8_t v_isSilent_boxed_6262_; lean_object* v_res_6263_; 
v_severity_boxed_6261_ = lean_unbox(v_severity_6254_);
v_isSilent_boxed_6262_ = lean_unbox(v_isSilent_6255_);
v_res_6263_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3(v_msgData_6253_, v_severity_boxed_6261_, v_isSilent_boxed_6262_, v___y_6256_, v___y_6257_, v___y_6258_, v___y_6259_);
lean_dec(v___y_6259_);
lean_dec_ref(v___y_6258_);
lean_dec(v___y_6257_);
lean_dec_ref(v___y_6256_);
return v_res_6263_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2(lean_object* v_msgData_6264_, lean_object* v___y_6265_, lean_object* v___y_6266_, lean_object* v___y_6267_, lean_object* v___y_6268_){
_start:
{
uint8_t v___x_6270_; uint8_t v___x_6271_; lean_object* v___x_6272_; 
v___x_6270_ = 2;
v___x_6271_ = 0;
v___x_6272_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3(v_msgData_6264_, v___x_6270_, v___x_6271_, v___y_6265_, v___y_6266_, v___y_6267_, v___y_6268_);
return v___x_6272_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_6273_, lean_object* v___y_6274_, lean_object* v___y_6275_, lean_object* v___y_6276_, lean_object* v___y_6277_, lean_object* v___y_6278_){
_start:
{
lean_object* v_res_6279_; 
v_res_6279_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2(v_msgData_6273_, v___y_6274_, v___y_6275_, v___y_6276_, v___y_6277_);
lean_dec(v___y_6277_);
lean_dec_ref(v___y_6276_);
lean_dec(v___y_6275_);
lean_dec_ref(v___y_6274_);
return v_res_6279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0(lean_object* v_f_6280_, lean_object* v___y_6281_, lean_object* v___y_6282_, lean_object* v___y_6283_, lean_object* v___y_6284_){
_start:
{
lean_object* v_module_6286_; lean_object* v_const_6287_; lean_object* v_exception_6288_; lean_object* v___x_6289_; lean_object* v___x_6290_; lean_object* v___x_6291_; lean_object* v___x_6292_; lean_object* v___x_6293_; lean_object* v___x_6294_; lean_object* v___x_6295_; lean_object* v___x_6296_; lean_object* v___x_6297_; lean_object* v___x_6298_; lean_object* v___x_6299_; lean_object* v___x_6300_; 
v_module_6286_ = lean_ctor_get(v_f_6280_, 0);
lean_inc(v_module_6286_);
v_const_6287_ = lean_ctor_get(v_f_6280_, 1);
lean_inc(v_const_6287_);
v_exception_6288_ = lean_ctor_get(v_f_6280_, 2);
lean_inc_ref(v_exception_6288_);
lean_dec_ref(v_f_6280_);
v___x_6289_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1);
v___x_6290_ = l_Lean_MessageData_ofName(v_const_6287_);
v___x_6291_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6291_, 0, v___x_6289_);
lean_ctor_set(v___x_6291_, 1, v___x_6290_);
v___x_6292_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3);
v___x_6293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6293_, 0, v___x_6291_);
lean_ctor_set(v___x_6293_, 1, v___x_6292_);
v___x_6294_ = l_Lean_MessageData_ofName(v_module_6286_);
v___x_6295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6295_, 0, v___x_6293_);
lean_ctor_set(v___x_6295_, 1, v___x_6294_);
v___x_6296_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5);
v___x_6297_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6297_, 0, v___x_6295_);
lean_ctor_set(v___x_6297_, 1, v___x_6296_);
v___x_6298_ = l_Lean_Exception_toMessageData(v_exception_6288_);
v___x_6299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6299_, 0, v___x_6297_);
lean_ctor_set(v___x_6299_, 1, v___x_6298_);
v___x_6300_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2(v___x_6299_, v___y_6281_, v___y_6282_, v___y_6283_, v___y_6284_);
return v___x_6300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0___boxed(lean_object* v_f_6301_, lean_object* v___y_6302_, lean_object* v___y_6303_, lean_object* v___y_6304_, lean_object* v___y_6305_, lean_object* v___y_6306_){
_start:
{
lean_object* v_res_6307_; 
v_res_6307_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0(v_f_6301_, v___y_6302_, v___y_6303_, v___y_6304_, v___y_6305_);
lean_dec(v___y_6305_);
lean_dec_ref(v___y_6304_);
lean_dec(v___y_6303_);
lean_dec_ref(v___y_6302_);
return v_res_6307_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3(lean_object* v_as_6308_, size_t v_i_6309_, size_t v_stop_6310_, lean_object* v_b_6311_, lean_object* v___y_6312_, lean_object* v___y_6313_, lean_object* v___y_6314_, lean_object* v___y_6315_){
_start:
{
uint8_t v___x_6317_; 
v___x_6317_ = lean_usize_dec_eq(v_i_6309_, v_stop_6310_);
if (v___x_6317_ == 0)
{
lean_object* v___x_6318_; lean_object* v___x_6319_; 
v___x_6318_ = lean_array_uget_borrowed(v_as_6308_, v_i_6309_);
lean_inc(v___x_6318_);
v___x_6319_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0(v___x_6318_, v___y_6312_, v___y_6313_, v___y_6314_, v___y_6315_);
if (lean_obj_tag(v___x_6319_) == 0)
{
lean_object* v_a_6320_; size_t v___x_6321_; size_t v___x_6322_; 
v_a_6320_ = lean_ctor_get(v___x_6319_, 0);
lean_inc(v_a_6320_);
lean_dec_ref_known(v___x_6319_, 1);
v___x_6321_ = ((size_t)1ULL);
v___x_6322_ = lean_usize_add(v_i_6309_, v___x_6321_);
v_i_6309_ = v___x_6322_;
v_b_6311_ = v_a_6320_;
goto _start;
}
else
{
return v___x_6319_;
}
}
else
{
lean_object* v___x_6324_; 
v___x_6324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6324_, 0, v_b_6311_);
return v___x_6324_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3___boxed(lean_object* v_as_6325_, lean_object* v_i_6326_, lean_object* v_stop_6327_, lean_object* v_b_6328_, lean_object* v___y_6329_, lean_object* v___y_6330_, lean_object* v___y_6331_, lean_object* v___y_6332_, lean_object* v___y_6333_){
_start:
{
size_t v_i_boxed_6334_; size_t v_stop_boxed_6335_; lean_object* v_res_6336_; 
v_i_boxed_6334_ = lean_unbox_usize(v_i_6326_);
lean_dec(v_i_6326_);
v_stop_boxed_6335_ = lean_unbox_usize(v_stop_6327_);
lean_dec(v_stop_6327_);
v_res_6336_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3(v_as_6325_, v_i_boxed_6334_, v_stop_boxed_6335_, v_b_6328_, v___y_6329_, v___y_6330_, v___y_6331_, v___y_6332_);
lean_dec(v___y_6332_);
lean_dec_ref(v___y_6331_);
lean_dec(v___y_6330_);
lean_dec_ref(v___y_6329_);
lean_dec_ref(v_as_6325_);
return v_res_6336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(lean_object* v_as_6337_, size_t v_i_6338_, size_t v_stop_6339_, lean_object* v_b_6340_){
_start:
{
uint8_t v___x_6341_; 
v___x_6341_ = lean_usize_dec_eq(v_i_6338_, v_stop_6339_);
if (v___x_6341_ == 0)
{
lean_object* v___x_6342_; lean_object* v___x_6343_; lean_object* v___x_6344_; size_t v___x_6345_; size_t v___x_6346_; 
v___x_6342_ = lean_array_uget_borrowed(v_as_6337_, v_i_6338_);
lean_inc(v___x_6342_);
v___x_6343_ = lean_task_get_own(v___x_6342_);
v___x_6344_ = l_Lean_Meta_LazyDiscrTree_InitResults_append___redArg(v_b_6340_, v___x_6343_);
v___x_6345_ = ((size_t)1ULL);
v___x_6346_ = lean_usize_add(v_i_6338_, v___x_6345_);
v_i_6338_ = v___x_6346_;
v_b_6340_ = v___x_6344_;
goto _start;
}
else
{
return v_b_6340_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_as_6348_, lean_object* v_i_6349_, lean_object* v_stop_6350_, lean_object* v_b_6351_){
_start:
{
size_t v_i_boxed_6352_; size_t v_stop_boxed_6353_; lean_object* v_res_6354_; 
v_i_boxed_6352_ = lean_unbox_usize(v_i_6349_);
lean_dec(v_i_6349_);
v_stop_boxed_6353_ = lean_unbox_usize(v_stop_6350_);
lean_dec(v_stop_6350_);
v_res_6354_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(v_as_6348_, v_i_boxed_6352_, v_stop_boxed_6353_, v_b_6351_);
lean_dec_ref(v_as_6348_);
return v_res_6354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(lean_object* v_z_6355_, lean_object* v_tasks_6356_){
_start:
{
lean_object* v___x_6357_; lean_object* v___x_6358_; uint8_t v___x_6359_; 
v___x_6357_ = lean_unsigned_to_nat(0u);
v___x_6358_ = lean_array_get_size(v_tasks_6356_);
v___x_6359_ = lean_nat_dec_lt(v___x_6357_, v___x_6358_);
if (v___x_6359_ == 0)
{
return v_z_6355_;
}
else
{
size_t v___x_6360_; size_t v___x_6361_; lean_object* v___x_6362_; 
v___x_6360_ = ((size_t)0ULL);
v___x_6361_ = lean_usize_of_nat(v___x_6358_);
v___x_6362_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(v_tasks_6356_, v___x_6360_, v___x_6361_, v_z_6355_);
return v___x_6362_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg___boxed(lean_object* v_z_6363_, lean_object* v_tasks_6364_){
_start:
{
lean_object* v_res_6365_; 
v_res_6365_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(v_z_6363_, v_tasks_6364_);
lean_dec_ref(v_tasks_6364_);
return v_res_6365_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_6366_; lean_object* v___x_6367_; lean_object* v___x_6368_; 
v___x_6366_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
v___x_6367_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_6368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6368_, 0, v___x_6367_);
lean_ctor_set(v___x_6368_, 1, v___x_6366_);
return v___x_6368_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_6369_; lean_object* v___x_6370_; lean_object* v___x_6371_; 
v___x_6369_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
v___x_6370_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0);
v___x_6371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6371_, 0, v___x_6370_);
lean_ctor_set(v___x_6371_, 1, v___x_6369_);
return v___x_6371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(lean_object* v_cctx_6372_, lean_object* v_ngen_6373_, lean_object* v_env_6374_, lean_object* v_act_6375_, lean_object* v_constantsPerTask_6376_, lean_object* v___y_6377_, lean_object* v___y_6378_, lean_object* v___y_6379_, lean_object* v___y_6380_){
_start:
{
lean_object* v___x_6382_; lean_object* v_moduleData_6383_; lean_object* v_n_6384_; lean_object* v___x_6385_; lean_object* v___x_6386_; lean_object* v___x_6387_; lean_object* v_a_6388_; lean_object* v___x_6390_; uint8_t v_isShared_6391_; uint8_t v_isSharedCheck_6423_; 
v___x_6382_ = l_Lean_Environment_header(v_env_6374_);
v_moduleData_6383_ = lean_ctor_get(v___x_6382_, 6);
lean_inc_ref(v_moduleData_6383_);
lean_dec_ref(v___x_6382_);
v_n_6384_ = lean_array_get_size(v_moduleData_6383_);
lean_dec_ref(v_moduleData_6383_);
v___x_6385_ = lean_unsigned_to_nat(0u);
v___x_6386_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
v___x_6387_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(v_cctx_6372_, v_env_6374_, v_act_6375_, v_constantsPerTask_6376_, v_n_6384_, v_ngen_6373_, v___x_6386_, v___x_6385_, v___x_6385_, v___x_6385_);
v_a_6388_ = lean_ctor_get(v___x_6387_, 0);
v_isSharedCheck_6423_ = !lean_is_exclusive(v___x_6387_);
if (v_isSharedCheck_6423_ == 0)
{
v___x_6390_ = v___x_6387_;
v_isShared_6391_ = v_isSharedCheck_6423_;
goto v_resetjp_6389_;
}
else
{
lean_inc(v_a_6388_);
lean_dec(v___x_6387_);
v___x_6390_ = lean_box(0);
v_isShared_6391_ = v_isSharedCheck_6423_;
goto v_resetjp_6389_;
}
v_resetjp_6389_:
{
lean_object* v___x_6392_; lean_object* v_r_6393_; lean_object* v_tree_6394_; lean_object* v_errors_6395_; lean_object* v___x_6396_; uint8_t v___x_6397_; 
v___x_6392_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1);
v_r_6393_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(v___x_6392_, v_a_6388_);
lean_dec(v_a_6388_);
v_tree_6394_ = lean_ctor_get(v_r_6393_, 0);
lean_inc_ref(v_tree_6394_);
v_errors_6395_ = lean_ctor_get(v_r_6393_, 1);
lean_inc_ref(v_errors_6395_);
lean_dec_ref(v_r_6393_);
v___x_6396_ = lean_array_get_size(v_errors_6395_);
v___x_6397_ = lean_nat_dec_lt(v___x_6385_, v___x_6396_);
if (v___x_6397_ == 0)
{
lean_object* v___x_6398_; lean_object* v___x_6400_; 
lean_dec_ref(v_errors_6395_);
v___x_6398_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_tree_6394_);
if (v_isShared_6391_ == 0)
{
lean_ctor_set(v___x_6390_, 0, v___x_6398_);
v___x_6400_ = v___x_6390_;
goto v_reusejp_6399_;
}
else
{
lean_object* v_reuseFailAlloc_6401_; 
v_reuseFailAlloc_6401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6401_, 0, v___x_6398_);
v___x_6400_ = v_reuseFailAlloc_6401_;
goto v_reusejp_6399_;
}
v_reusejp_6399_:
{
return v___x_6400_;
}
}
else
{
lean_object* v___x_6402_; size_t v___x_6403_; size_t v___x_6404_; lean_object* v___x_6405_; 
lean_del_object(v___x_6390_);
v___x_6402_ = lean_box(0);
v___x_6403_ = ((size_t)0ULL);
v___x_6404_ = lean_usize_of_nat(v___x_6396_);
v___x_6405_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3(v_errors_6395_, v___x_6403_, v___x_6404_, v___x_6402_, v___y_6377_, v___y_6378_, v___y_6379_, v___y_6380_);
lean_dec_ref(v_errors_6395_);
if (lean_obj_tag(v___x_6405_) == 0)
{
lean_object* v___x_6407_; uint8_t v_isShared_6408_; uint8_t v_isSharedCheck_6413_; 
v_isSharedCheck_6413_ = !lean_is_exclusive(v___x_6405_);
if (v_isSharedCheck_6413_ == 0)
{
lean_object* v_unused_6414_; 
v_unused_6414_ = lean_ctor_get(v___x_6405_, 0);
lean_dec(v_unused_6414_);
v___x_6407_ = v___x_6405_;
v_isShared_6408_ = v_isSharedCheck_6413_;
goto v_resetjp_6406_;
}
else
{
lean_dec(v___x_6405_);
v___x_6407_ = lean_box(0);
v_isShared_6408_ = v_isSharedCheck_6413_;
goto v_resetjp_6406_;
}
v_resetjp_6406_:
{
lean_object* v___x_6409_; lean_object* v___x_6411_; 
v___x_6409_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_tree_6394_);
if (v_isShared_6408_ == 0)
{
lean_ctor_set(v___x_6407_, 0, v___x_6409_);
v___x_6411_ = v___x_6407_;
goto v_reusejp_6410_;
}
else
{
lean_object* v_reuseFailAlloc_6412_; 
v_reuseFailAlloc_6412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6412_, 0, v___x_6409_);
v___x_6411_ = v_reuseFailAlloc_6412_;
goto v_reusejp_6410_;
}
v_reusejp_6410_:
{
return v___x_6411_;
}
}
}
else
{
lean_object* v_a_6415_; lean_object* v___x_6417_; uint8_t v_isShared_6418_; uint8_t v_isSharedCheck_6422_; 
lean_dec_ref(v_tree_6394_);
v_a_6415_ = lean_ctor_get(v___x_6405_, 0);
v_isSharedCheck_6422_ = !lean_is_exclusive(v___x_6405_);
if (v_isSharedCheck_6422_ == 0)
{
v___x_6417_ = v___x_6405_;
v_isShared_6418_ = v_isSharedCheck_6422_;
goto v_resetjp_6416_;
}
else
{
lean_inc(v_a_6415_);
lean_dec(v___x_6405_);
v___x_6417_ = lean_box(0);
v_isShared_6418_ = v_isSharedCheck_6422_;
goto v_resetjp_6416_;
}
v_resetjp_6416_:
{
lean_object* v___x_6420_; 
if (v_isShared_6418_ == 0)
{
v___x_6420_ = v___x_6417_;
goto v_reusejp_6419_;
}
else
{
lean_object* v_reuseFailAlloc_6421_; 
v_reuseFailAlloc_6421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6421_, 0, v_a_6415_);
v___x_6420_ = v_reuseFailAlloc_6421_;
goto v_reusejp_6419_;
}
v_reusejp_6419_:
{
return v___x_6420_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___boxed(lean_object* v_cctx_6424_, lean_object* v_ngen_6425_, lean_object* v_env_6426_, lean_object* v_act_6427_, lean_object* v_constantsPerTask_6428_, lean_object* v___y_6429_, lean_object* v___y_6430_, lean_object* v___y_6431_, lean_object* v___y_6432_, lean_object* v___y_6433_){
_start:
{
lean_object* v_res_6434_; 
v_res_6434_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(v_cctx_6424_, v_ngen_6425_, v_env_6426_, v_act_6427_, v_constantsPerTask_6428_, v___y_6429_, v___y_6430_, v___y_6431_, v___y_6432_);
lean_dec(v___y_6432_);
lean_dec_ref(v___y_6431_);
lean_dec(v___y_6430_);
lean_dec_ref(v___y_6429_);
lean_dec(v_constantsPerTask_6428_);
return v_res_6434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0(lean_object* v_a_6435_, lean_object* v___x_6436_, lean_object* v_addEntry_6437_, lean_object* v_constantsPerTask_6438_, lean_object* v_droppedEntriesRef_6439_, lean_object* v_droppedKeys_6440_, lean_object* v___y_6441_, lean_object* v___y_6442_, lean_object* v___y_6443_, lean_object* v___y_6444_){
_start:
{
lean_object* v___x_6446_; lean_object* v_env_6447_; lean_object* v___x_6448_; lean_object* v___x_6449_; 
v___x_6446_ = lean_st_ref_get(v___y_6444_);
v_env_6447_ = lean_ctor_get(v___x_6446_, 0);
lean_inc_ref(v_env_6447_);
lean_dec(v___x_6446_);
lean_inc_ref(v_a_6435_);
v___x_6448_ = l_Lean_Meta_LazyDiscrTree_createTreeCtx(v_a_6435_);
v___x_6449_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(v___x_6448_, v___x_6436_, v_env_6447_, v_addEntry_6437_, v_constantsPerTask_6438_, v___y_6441_, v___y_6442_, v___y_6443_, v___y_6444_);
if (lean_obj_tag(v___x_6449_) == 0)
{
if (lean_obj_tag(v_droppedEntriesRef_6439_) == 1)
{
lean_object* v_a_6450_; lean_object* v_val_6451_; lean_object* v___x_6453_; uint8_t v_isShared_6454_; uint8_t v_isSharedCheck_6484_; 
v_a_6450_ = lean_ctor_get(v___x_6449_, 0);
lean_inc(v_a_6450_);
lean_dec_ref_known(v___x_6449_, 1);
v_val_6451_ = lean_ctor_get(v_droppedEntriesRef_6439_, 0);
v_isSharedCheck_6484_ = !lean_is_exclusive(v_droppedEntriesRef_6439_);
if (v_isSharedCheck_6484_ == 0)
{
v___x_6453_ = v_droppedEntriesRef_6439_;
v_isShared_6454_ = v_isSharedCheck_6484_;
goto v_resetjp_6452_;
}
else
{
lean_inc(v_val_6451_);
lean_dec(v_droppedEntriesRef_6439_);
v___x_6453_ = lean_box(0);
v_isShared_6454_ = v_isSharedCheck_6484_;
goto v_resetjp_6452_;
}
v_resetjp_6452_:
{
lean_object* v___x_6455_; 
v___x_6455_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_a_6450_, v_droppedKeys_6440_, v___y_6441_, v___y_6442_, v___y_6443_, v___y_6444_);
lean_dec(v_droppedKeys_6440_);
if (lean_obj_tag(v___x_6455_) == 0)
{
lean_object* v_a_6456_; lean_object* v___x_6458_; uint8_t v_isShared_6459_; uint8_t v_isSharedCheck_6475_; 
v_a_6456_ = lean_ctor_get(v___x_6455_, 0);
v_isSharedCheck_6475_ = !lean_is_exclusive(v___x_6455_);
if (v_isSharedCheck_6475_ == 0)
{
v___x_6458_ = v___x_6455_;
v_isShared_6459_ = v_isSharedCheck_6475_;
goto v_resetjp_6457_;
}
else
{
lean_inc(v_a_6456_);
lean_dec(v___x_6455_);
v___x_6458_ = lean_box(0);
v_isShared_6459_ = v_isSharedCheck_6475_;
goto v_resetjp_6457_;
}
v_resetjp_6457_:
{
lean_object* v_fst_6460_; lean_object* v_snd_6461_; lean_object* v___x_6462_; lean_object* v___y_6464_; 
v_fst_6460_ = lean_ctor_get(v_a_6456_, 0);
lean_inc(v_fst_6460_);
v_snd_6461_ = lean_ctor_get(v_a_6456_, 1);
lean_inc(v_snd_6461_);
lean_dec(v_a_6456_);
v___x_6462_ = lean_st_ref_get(v_val_6451_);
if (lean_obj_tag(v___x_6462_) == 0)
{
lean_object* v___x_6473_; 
v___x_6473_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___y_6464_ = v___x_6473_;
goto v___jp_6463_;
}
else
{
lean_object* v_val_6474_; 
v_val_6474_ = lean_ctor_get(v___x_6462_, 0);
lean_inc(v_val_6474_);
lean_dec_ref_known(v___x_6462_, 1);
v___y_6464_ = v_val_6474_;
goto v___jp_6463_;
}
v___jp_6463_:
{
lean_object* v___x_6465_; lean_object* v___x_6467_; 
v___x_6465_ = l_Array_append___redArg(v___y_6464_, v_fst_6460_);
lean_dec(v_fst_6460_);
if (v_isShared_6454_ == 0)
{
lean_ctor_set(v___x_6453_, 0, v___x_6465_);
v___x_6467_ = v___x_6453_;
goto v_reusejp_6466_;
}
else
{
lean_object* v_reuseFailAlloc_6472_; 
v_reuseFailAlloc_6472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6472_, 0, v___x_6465_);
v___x_6467_ = v_reuseFailAlloc_6472_;
goto v_reusejp_6466_;
}
v_reusejp_6466_:
{
lean_object* v___x_6468_; lean_object* v___x_6470_; 
v___x_6468_ = lean_st_ref_swap(v_val_6451_, v___x_6467_);
lean_dec(v_val_6451_);
lean_dec(v___x_6468_);
if (v_isShared_6459_ == 0)
{
lean_ctor_set(v___x_6458_, 0, v_snd_6461_);
v___x_6470_ = v___x_6458_;
goto v_reusejp_6469_;
}
else
{
lean_object* v_reuseFailAlloc_6471_; 
v_reuseFailAlloc_6471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6471_, 0, v_snd_6461_);
v___x_6470_ = v_reuseFailAlloc_6471_;
goto v_reusejp_6469_;
}
v_reusejp_6469_:
{
return v___x_6470_;
}
}
}
}
}
else
{
lean_object* v_a_6476_; lean_object* v___x_6478_; uint8_t v_isShared_6479_; uint8_t v_isSharedCheck_6483_; 
lean_del_object(v___x_6453_);
lean_dec(v_val_6451_);
v_a_6476_ = lean_ctor_get(v___x_6455_, 0);
v_isSharedCheck_6483_ = !lean_is_exclusive(v___x_6455_);
if (v_isSharedCheck_6483_ == 0)
{
v___x_6478_ = v___x_6455_;
v_isShared_6479_ = v_isSharedCheck_6483_;
goto v_resetjp_6477_;
}
else
{
lean_inc(v_a_6476_);
lean_dec(v___x_6455_);
v___x_6478_ = lean_box(0);
v_isShared_6479_ = v_isSharedCheck_6483_;
goto v_resetjp_6477_;
}
v_resetjp_6477_:
{
lean_object* v___x_6481_; 
if (v_isShared_6479_ == 0)
{
v___x_6481_ = v___x_6478_;
goto v_reusejp_6480_;
}
else
{
lean_object* v_reuseFailAlloc_6482_; 
v_reuseFailAlloc_6482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6482_, 0, v_a_6476_);
v___x_6481_ = v_reuseFailAlloc_6482_;
goto v_reusejp_6480_;
}
v_reusejp_6480_:
{
return v___x_6481_;
}
}
}
}
}
else
{
lean_object* v_a_6485_; lean_object* v___x_6486_; 
lean_dec(v_droppedEntriesRef_6439_);
v_a_6485_ = lean_ctor_get(v___x_6449_, 0);
lean_inc(v_a_6485_);
lean_dec_ref_known(v___x_6449_, 1);
v___x_6486_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_a_6485_, v_droppedKeys_6440_, v___y_6441_, v___y_6442_, v___y_6443_, v___y_6444_);
return v___x_6486_;
}
}
else
{
lean_dec(v_droppedKeys_6440_);
lean_dec(v_droppedEntriesRef_6439_);
return v___x_6449_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0___boxed(lean_object* v_a_6487_, lean_object* v___x_6488_, lean_object* v_addEntry_6489_, lean_object* v_constantsPerTask_6490_, lean_object* v_droppedEntriesRef_6491_, lean_object* v_droppedKeys_6492_, lean_object* v___y_6493_, lean_object* v___y_6494_, lean_object* v___y_6495_, lean_object* v___y_6496_, lean_object* v___y_6497_){
_start:
{
lean_object* v_res_6498_; 
v_res_6498_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0(v_a_6487_, v___x_6488_, v_addEntry_6489_, v_constantsPerTask_6490_, v_droppedEntriesRef_6491_, v_droppedKeys_6492_, v___y_6493_, v___y_6494_, v___y_6495_, v___y_6496_);
lean_dec(v___y_6496_);
lean_dec_ref(v___y_6495_);
lean_dec(v___y_6494_);
lean_dec_ref(v___y_6493_);
lean_dec(v_constantsPerTask_6490_);
lean_dec_ref(v_a_6487_);
return v_res_6498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(lean_object* v_ref_6500_, lean_object* v_addEntry_6501_, lean_object* v_droppedKeys_6502_, lean_object* v_constantsPerTask_6503_, lean_object* v_droppedEntriesRef_6504_, lean_object* v_ty_6505_, lean_object* v_a_6506_, lean_object* v_a_6507_, lean_object* v_a_6508_, lean_object* v_a_6509_){
_start:
{
lean_object* v_a_6512_; lean_object* v___x_6534_; lean_object* v_ngen_6535_; lean_object* v_namePrefix_6536_; lean_object* v_idx_6537_; lean_object* v___x_6539_; uint8_t v_isShared_6540_; uint8_t v_isSharedCheck_6583_; 
v___x_6534_ = lean_st_ref_get(v_a_6509_);
v_ngen_6535_ = lean_ctor_get(v___x_6534_, 2);
lean_inc_ref(v_ngen_6535_);
lean_dec(v___x_6534_);
v_namePrefix_6536_ = lean_ctor_get(v_ngen_6535_, 0);
v_idx_6537_ = lean_ctor_get(v_ngen_6535_, 1);
v_isSharedCheck_6583_ = !lean_is_exclusive(v_ngen_6535_);
if (v_isSharedCheck_6583_ == 0)
{
v___x_6539_ = v_ngen_6535_;
v_isShared_6540_ = v_isSharedCheck_6583_;
goto v_resetjp_6538_;
}
else
{
lean_inc(v_idx_6537_);
lean_inc(v_namePrefix_6536_);
lean_dec(v_ngen_6535_);
v___x_6539_ = lean_box(0);
v_isShared_6540_ = v_isSharedCheck_6583_;
goto v_resetjp_6538_;
}
v___jp_6511_:
{
lean_object* v___x_6513_; 
v___x_6513_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v_a_6512_, v_ty_6505_, v_a_6506_, v_a_6507_, v_a_6508_, v_a_6509_);
if (lean_obj_tag(v___x_6513_) == 0)
{
lean_object* v_a_6514_; lean_object* v___x_6516_; uint8_t v_isShared_6517_; uint8_t v_isSharedCheck_6525_; 
v_a_6514_ = lean_ctor_get(v___x_6513_, 0);
v_isSharedCheck_6525_ = !lean_is_exclusive(v___x_6513_);
if (v_isSharedCheck_6525_ == 0)
{
v___x_6516_ = v___x_6513_;
v_isShared_6517_ = v_isSharedCheck_6525_;
goto v_resetjp_6515_;
}
else
{
lean_inc(v_a_6514_);
lean_dec(v___x_6513_);
v___x_6516_ = lean_box(0);
v_isShared_6517_ = v_isSharedCheck_6525_;
goto v_resetjp_6515_;
}
v_resetjp_6515_:
{
lean_object* v_fst_6518_; lean_object* v_snd_6519_; lean_object* v___x_6520_; lean_object* v___x_6521_; lean_object* v___x_6523_; 
v_fst_6518_ = lean_ctor_get(v_a_6514_, 0);
lean_inc(v_fst_6518_);
v_snd_6519_ = lean_ctor_get(v_a_6514_, 1);
lean_inc(v_snd_6519_);
lean_dec(v_a_6514_);
v___x_6520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6520_, 0, v_snd_6519_);
v___x_6521_ = lean_st_ref_swap(v_ref_6500_, v___x_6520_);
lean_dec(v___x_6521_);
if (v_isShared_6517_ == 0)
{
lean_ctor_set(v___x_6516_, 0, v_fst_6518_);
v___x_6523_ = v___x_6516_;
goto v_reusejp_6522_;
}
else
{
lean_object* v_reuseFailAlloc_6524_; 
v_reuseFailAlloc_6524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6524_, 0, v_fst_6518_);
v___x_6523_ = v_reuseFailAlloc_6524_;
goto v_reusejp_6522_;
}
v_reusejp_6522_:
{
return v___x_6523_;
}
}
}
else
{
lean_object* v_a_6526_; lean_object* v___x_6528_; uint8_t v_isShared_6529_; uint8_t v_isSharedCheck_6533_; 
v_a_6526_ = lean_ctor_get(v___x_6513_, 0);
v_isSharedCheck_6533_ = !lean_is_exclusive(v___x_6513_);
if (v_isSharedCheck_6533_ == 0)
{
v___x_6528_ = v___x_6513_;
v_isShared_6529_ = v_isSharedCheck_6533_;
goto v_resetjp_6527_;
}
else
{
lean_inc(v_a_6526_);
lean_dec(v___x_6513_);
v___x_6528_ = lean_box(0);
v_isShared_6529_ = v_isSharedCheck_6533_;
goto v_resetjp_6527_;
}
v_resetjp_6527_:
{
lean_object* v___x_6531_; 
if (v_isShared_6529_ == 0)
{
v___x_6531_ = v___x_6528_;
goto v_reusejp_6530_;
}
else
{
lean_object* v_reuseFailAlloc_6532_; 
v_reuseFailAlloc_6532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6532_, 0, v_a_6526_);
v___x_6531_ = v_reuseFailAlloc_6532_;
goto v_reusejp_6530_;
}
v_reusejp_6530_:
{
return v___x_6531_;
}
}
}
}
v_resetjp_6538_:
{
lean_object* v___x_6541_; lean_object* v_env_6542_; lean_object* v_nextMacroScope_6543_; lean_object* v_auxDeclNGen_6544_; lean_object* v_traceState_6545_; lean_object* v_cache_6546_; lean_object* v_messages_6547_; lean_object* v_infoState_6548_; lean_object* v_snapshotTasks_6549_; lean_object* v___x_6551_; uint8_t v_isShared_6552_; uint8_t v_isSharedCheck_6581_; 
v___x_6541_ = lean_st_ref_take(v_a_6509_);
v_env_6542_ = lean_ctor_get(v___x_6541_, 0);
v_nextMacroScope_6543_ = lean_ctor_get(v___x_6541_, 1);
v_auxDeclNGen_6544_ = lean_ctor_get(v___x_6541_, 3);
v_traceState_6545_ = lean_ctor_get(v___x_6541_, 4);
v_cache_6546_ = lean_ctor_get(v___x_6541_, 5);
v_messages_6547_ = lean_ctor_get(v___x_6541_, 6);
v_infoState_6548_ = lean_ctor_get(v___x_6541_, 7);
v_snapshotTasks_6549_ = lean_ctor_get(v___x_6541_, 8);
v_isSharedCheck_6581_ = !lean_is_exclusive(v___x_6541_);
if (v_isSharedCheck_6581_ == 0)
{
lean_object* v_unused_6582_; 
v_unused_6582_ = lean_ctor_get(v___x_6541_, 2);
lean_dec(v_unused_6582_);
v___x_6551_ = v___x_6541_;
v_isShared_6552_ = v_isSharedCheck_6581_;
goto v_resetjp_6550_;
}
else
{
lean_inc(v_snapshotTasks_6549_);
lean_inc(v_infoState_6548_);
lean_inc(v_messages_6547_);
lean_inc(v_cache_6546_);
lean_inc(v_traceState_6545_);
lean_inc(v_auxDeclNGen_6544_);
lean_inc(v_nextMacroScope_6543_);
lean_inc(v_env_6542_);
lean_dec(v___x_6541_);
v___x_6551_ = lean_box(0);
v_isShared_6552_ = v_isSharedCheck_6581_;
goto v_resetjp_6550_;
}
v_resetjp_6550_:
{
lean_object* v___x_6553_; lean_object* v___x_6554_; lean_object* v___x_6555_; lean_object* v___x_6557_; 
lean_inc(v_idx_6537_);
lean_inc(v_namePrefix_6536_);
v___x_6553_ = l_Lean_Name_num___override(v_namePrefix_6536_, v_idx_6537_);
v___x_6554_ = lean_unsigned_to_nat(1u);
v___x_6555_ = lean_nat_add(v_idx_6537_, v___x_6554_);
lean_dec(v_idx_6537_);
if (v_isShared_6540_ == 0)
{
lean_ctor_set(v___x_6539_, 1, v___x_6555_);
v___x_6557_ = v___x_6539_;
goto v_reusejp_6556_;
}
else
{
lean_object* v_reuseFailAlloc_6580_; 
v_reuseFailAlloc_6580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6580_, 0, v_namePrefix_6536_);
lean_ctor_set(v_reuseFailAlloc_6580_, 1, v___x_6555_);
v___x_6557_ = v_reuseFailAlloc_6580_;
goto v_reusejp_6556_;
}
v_reusejp_6556_:
{
lean_object* v___x_6559_; 
if (v_isShared_6552_ == 0)
{
lean_ctor_set(v___x_6551_, 2, v___x_6557_);
v___x_6559_ = v___x_6551_;
goto v_reusejp_6558_;
}
else
{
lean_object* v_reuseFailAlloc_6579_; 
v_reuseFailAlloc_6579_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6579_, 0, v_env_6542_);
lean_ctor_set(v_reuseFailAlloc_6579_, 1, v_nextMacroScope_6543_);
lean_ctor_set(v_reuseFailAlloc_6579_, 2, v___x_6557_);
lean_ctor_set(v_reuseFailAlloc_6579_, 3, v_auxDeclNGen_6544_);
lean_ctor_set(v_reuseFailAlloc_6579_, 4, v_traceState_6545_);
lean_ctor_set(v_reuseFailAlloc_6579_, 5, v_cache_6546_);
lean_ctor_set(v_reuseFailAlloc_6579_, 6, v_messages_6547_);
lean_ctor_set(v_reuseFailAlloc_6579_, 7, v_infoState_6548_);
lean_ctor_set(v_reuseFailAlloc_6579_, 8, v_snapshotTasks_6549_);
v___x_6559_ = v_reuseFailAlloc_6579_;
goto v_reusejp_6558_;
}
v_reusejp_6558_:
{
lean_object* v___x_6560_; lean_object* v___x_6561_; 
v___x_6560_ = lean_st_ref_put(v_a_6509_, v___x_6559_);
v___x_6561_ = lean_st_ref_get(v_ref_6500_);
if (lean_obj_tag(v___x_6561_) == 0)
{
lean_object* v_toCold_6562_; lean_object* v_options_6563_; lean_object* v___x_6564_; lean_object* v___f_6565_; lean_object* v___x_6566_; lean_object* v___x_6567_; lean_object* v___x_6568_; 
v_toCold_6562_ = lean_ctor_get(v_a_6508_, 0);
v_options_6563_ = lean_ctor_get(v_toCold_6562_, 2);
v___x_6564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6564_, 0, v___x_6553_);
lean_ctor_set(v___x_6564_, 1, v___x_6554_);
lean_inc_ref(v_a_6508_);
v___f_6565_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_6565_, 0, v_a_6508_);
lean_closure_set(v___f_6565_, 1, v___x_6564_);
lean_closure_set(v___f_6565_, 2, v_addEntry_6501_);
lean_closure_set(v___f_6565_, 3, v_constantsPerTask_6503_);
lean_closure_set(v___f_6565_, 4, v_droppedEntriesRef_6504_);
lean_closure_set(v___f_6565_, 5, v_droppedKeys_6502_);
v___x_6566_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___closed__0));
v___x_6567_ = lean_box(0);
v___x_6568_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v___x_6566_, v_options_6563_, v___f_6565_, v___x_6567_, v_a_6506_, v_a_6507_, v_a_6508_, v_a_6509_);
if (lean_obj_tag(v___x_6568_) == 0)
{
lean_object* v_a_6569_; 
v_a_6569_ = lean_ctor_get(v___x_6568_, 0);
lean_inc(v_a_6569_);
lean_dec_ref_known(v___x_6568_, 1);
v_a_6512_ = v_a_6569_;
goto v___jp_6511_;
}
else
{
lean_object* v_a_6570_; lean_object* v___x_6572_; uint8_t v_isShared_6573_; uint8_t v_isSharedCheck_6577_; 
lean_dec_ref(v_ty_6505_);
v_a_6570_ = lean_ctor_get(v___x_6568_, 0);
v_isSharedCheck_6577_ = !lean_is_exclusive(v___x_6568_);
if (v_isSharedCheck_6577_ == 0)
{
v___x_6572_ = v___x_6568_;
v_isShared_6573_ = v_isSharedCheck_6577_;
goto v_resetjp_6571_;
}
else
{
lean_inc(v_a_6570_);
lean_dec(v___x_6568_);
v___x_6572_ = lean_box(0);
v_isShared_6573_ = v_isSharedCheck_6577_;
goto v_resetjp_6571_;
}
v_resetjp_6571_:
{
lean_object* v___x_6575_; 
if (v_isShared_6573_ == 0)
{
v___x_6575_ = v___x_6572_;
goto v_reusejp_6574_;
}
else
{
lean_object* v_reuseFailAlloc_6576_; 
v_reuseFailAlloc_6576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6576_, 0, v_a_6570_);
v___x_6575_ = v_reuseFailAlloc_6576_;
goto v_reusejp_6574_;
}
v_reusejp_6574_:
{
return v___x_6575_;
}
}
}
}
else
{
lean_object* v_val_6578_; 
lean_dec(v___x_6553_);
lean_dec(v_droppedEntriesRef_6504_);
lean_dec(v_constantsPerTask_6503_);
lean_dec(v_droppedKeys_6502_);
lean_dec_ref(v_addEntry_6501_);
v_val_6578_ = lean_ctor_get(v___x_6561_, 0);
lean_inc(v_val_6578_);
lean_dec_ref_known(v___x_6561_, 1);
v_a_6512_ = v_val_6578_;
goto v___jp_6511_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___boxed(lean_object* v_ref_6584_, lean_object* v_addEntry_6585_, lean_object* v_droppedKeys_6586_, lean_object* v_constantsPerTask_6587_, lean_object* v_droppedEntriesRef_6588_, lean_object* v_ty_6589_, lean_object* v_a_6590_, lean_object* v_a_6591_, lean_object* v_a_6592_, lean_object* v_a_6593_, lean_object* v_a_6594_){
_start:
{
lean_object* v_res_6595_; 
v_res_6595_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(v_ref_6584_, v_addEntry_6585_, v_droppedKeys_6586_, v_constantsPerTask_6587_, v_droppedEntriesRef_6588_, v_ty_6589_, v_a_6590_, v_a_6591_, v_a_6592_, v_a_6593_);
lean_dec(v_a_6593_);
lean_dec_ref(v_a_6592_);
lean_dec(v_a_6591_);
lean_dec_ref(v_a_6590_);
lean_dec(v_ref_6584_);
return v_res_6595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches(lean_object* v_00_u03b1_6596_, lean_object* v_ref_6597_, lean_object* v_addEntry_6598_, lean_object* v_droppedKeys_6599_, lean_object* v_constantsPerTask_6600_, lean_object* v_droppedEntriesRef_6601_, lean_object* v_ty_6602_, lean_object* v_a_6603_, lean_object* v_a_6604_, lean_object* v_a_6605_, lean_object* v_a_6606_){
_start:
{
lean_object* v___x_6608_; 
v___x_6608_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(v_ref_6597_, v_addEntry_6598_, v_droppedKeys_6599_, v_constantsPerTask_6600_, v_droppedEntriesRef_6601_, v_ty_6602_, v_a_6603_, v_a_6604_, v_a_6605_, v_a_6606_);
return v___x_6608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___boxed(lean_object* v_00_u03b1_6609_, lean_object* v_ref_6610_, lean_object* v_addEntry_6611_, lean_object* v_droppedKeys_6612_, lean_object* v_constantsPerTask_6613_, lean_object* v_droppedEntriesRef_6614_, lean_object* v_ty_6615_, lean_object* v_a_6616_, lean_object* v_a_6617_, lean_object* v_a_6618_, lean_object* v_a_6619_, lean_object* v_a_6620_){
_start:
{
lean_object* v_res_6621_; 
v_res_6621_ = l_Lean_Meta_LazyDiscrTree_findImportMatches(v_00_u03b1_6609_, v_ref_6610_, v_addEntry_6611_, v_droppedKeys_6612_, v_constantsPerTask_6613_, v_droppedEntriesRef_6614_, v_ty_6615_, v_a_6616_, v_a_6617_, v_a_6618_, v_a_6619_);
lean_dec(v_a_6619_);
lean_dec_ref(v_a_6618_);
lean_dec(v_a_6617_);
lean_dec_ref(v_a_6616_);
lean_dec(v_ref_6610_);
return v_res_6621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0(lean_object* v_00_u03b1_6622_, lean_object* v_cctx_6623_, lean_object* v_ngen_6624_, lean_object* v_env_6625_, lean_object* v_act_6626_, lean_object* v_constantsPerTask_6627_, lean_object* v___y_6628_, lean_object* v___y_6629_, lean_object* v___y_6630_, lean_object* v___y_6631_){
_start:
{
lean_object* v___x_6633_; 
v___x_6633_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(v_cctx_6623_, v_ngen_6624_, v_env_6625_, v_act_6626_, v_constantsPerTask_6627_, v___y_6628_, v___y_6629_, v___y_6630_, v___y_6631_);
return v___x_6633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___boxed(lean_object* v_00_u03b1_6634_, lean_object* v_cctx_6635_, lean_object* v_ngen_6636_, lean_object* v_env_6637_, lean_object* v_act_6638_, lean_object* v_constantsPerTask_6639_, lean_object* v___y_6640_, lean_object* v___y_6641_, lean_object* v___y_6642_, lean_object* v___y_6643_, lean_object* v___y_6644_){
_start:
{
lean_object* v_res_6645_; 
v_res_6645_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0(v_00_u03b1_6634_, v_cctx_6635_, v_ngen_6636_, v_env_6637_, v_act_6638_, v_constantsPerTask_6639_, v___y_6640_, v___y_6641_, v___y_6642_, v___y_6643_);
lean_dec(v___y_6643_);
lean_dec_ref(v___y_6642_);
lean_dec(v___y_6641_);
lean_dec_ref(v___y_6640_);
lean_dec(v_constantsPerTask_6639_);
return v_res_6645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1(lean_object* v_00_u03b1_6646_, lean_object* v_cctx_6647_, lean_object* v_env_6648_, lean_object* v_act_6649_, lean_object* v_constantsPerTask_6650_, lean_object* v_n_6651_, lean_object* v_ngen_6652_, lean_object* v_tasks_6653_, lean_object* v_start_6654_, lean_object* v_cnt_6655_, lean_object* v_idx_6656_, lean_object* v___y_6657_, lean_object* v___y_6658_, lean_object* v___y_6659_, lean_object* v___y_6660_){
_start:
{
lean_object* v___x_6662_; 
v___x_6662_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(v_cctx_6647_, v_env_6648_, v_act_6649_, v_constantsPerTask_6650_, v_n_6651_, v_ngen_6652_, v_tasks_6653_, v_start_6654_, v_cnt_6655_, v_idx_6656_);
return v___x_6662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___boxed(lean_object* v_00_u03b1_6663_, lean_object* v_cctx_6664_, lean_object* v_env_6665_, lean_object* v_act_6666_, lean_object* v_constantsPerTask_6667_, lean_object* v_n_6668_, lean_object* v_ngen_6669_, lean_object* v_tasks_6670_, lean_object* v_start_6671_, lean_object* v_cnt_6672_, lean_object* v_idx_6673_, lean_object* v___y_6674_, lean_object* v___y_6675_, lean_object* v___y_6676_, lean_object* v___y_6677_, lean_object* v___y_6678_){
_start:
{
lean_object* v_res_6679_; 
v_res_6679_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1(v_00_u03b1_6663_, v_cctx_6664_, v_env_6665_, v_act_6666_, v_constantsPerTask_6667_, v_n_6668_, v_ngen_6669_, v_tasks_6670_, v_start_6671_, v_cnt_6672_, v_idx_6673_, v___y_6674_, v___y_6675_, v___y_6676_, v___y_6677_);
lean_dec(v___y_6677_);
lean_dec_ref(v___y_6676_);
lean_dec(v___y_6675_);
lean_dec_ref(v___y_6674_);
lean_dec(v_constantsPerTask_6667_);
return v_res_6679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2(lean_object* v_00_u03b1_6680_, lean_object* v_z_6681_, lean_object* v_tasks_6682_){
_start:
{
lean_object* v___x_6683_; 
v___x_6683_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(v_z_6681_, v_tasks_6682_);
return v___x_6683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___boxed(lean_object* v_00_u03b1_6684_, lean_object* v_z_6685_, lean_object* v_tasks_6686_){
_start:
{
lean_object* v_res_6687_; 
v_res_6687_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2(v_00_u03b1_6684_, v_z_6685_, v_tasks_6686_);
lean_dec_ref(v_tasks_6686_);
return v_res_6687_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5(lean_object* v_00_u03b1_6688_, lean_object* v_as_6689_, size_t v_i_6690_, size_t v_stop_6691_, lean_object* v_b_6692_){
_start:
{
lean_object* v___x_6693_; 
v___x_6693_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(v_as_6689_, v_i_6690_, v_stop_6691_, v_b_6692_);
return v___x_6693_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b1_6694_, lean_object* v_as_6695_, lean_object* v_i_6696_, lean_object* v_stop_6697_, lean_object* v_b_6698_){
_start:
{
size_t v_i_boxed_6699_; size_t v_stop_boxed_6700_; lean_object* v_res_6701_; 
v_i_boxed_6699_ = lean_unbox_usize(v_i_6696_);
lean_dec(v_i_6696_);
v_stop_boxed_6700_ = lean_unbox_usize(v_stop_6697_);
lean_dec(v_stop_6697_);
v_res_6701_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5(v_00_u03b1_6694_, v_as_6695_, v_i_boxed_6699_, v_stop_boxed_6700_, v_b_6698_);
lean_dec_ref(v_as_6695_);
return v_res_6701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(lean_object* v___y_6702_){
_start:
{
lean_object* v___x_6704_; lean_object* v_ngen_6705_; lean_object* v_namePrefix_6706_; lean_object* v_idx_6707_; lean_object* v___x_6709_; uint8_t v_isShared_6710_; uint8_t v_isSharedCheck_6737_; 
v___x_6704_ = lean_st_ref_get(v___y_6702_);
v_ngen_6705_ = lean_ctor_get(v___x_6704_, 2);
lean_inc_ref(v_ngen_6705_);
lean_dec(v___x_6704_);
v_namePrefix_6706_ = lean_ctor_get(v_ngen_6705_, 0);
v_idx_6707_ = lean_ctor_get(v_ngen_6705_, 1);
v_isSharedCheck_6737_ = !lean_is_exclusive(v_ngen_6705_);
if (v_isSharedCheck_6737_ == 0)
{
v___x_6709_ = v_ngen_6705_;
v_isShared_6710_ = v_isSharedCheck_6737_;
goto v_resetjp_6708_;
}
else
{
lean_inc(v_idx_6707_);
lean_inc(v_namePrefix_6706_);
lean_dec(v_ngen_6705_);
v___x_6709_ = lean_box(0);
v_isShared_6710_ = v_isSharedCheck_6737_;
goto v_resetjp_6708_;
}
v_resetjp_6708_:
{
lean_object* v___x_6711_; lean_object* v_env_6712_; lean_object* v_nextMacroScope_6713_; lean_object* v_auxDeclNGen_6714_; lean_object* v_traceState_6715_; lean_object* v_cache_6716_; lean_object* v_messages_6717_; lean_object* v_infoState_6718_; lean_object* v_snapshotTasks_6719_; lean_object* v___x_6721_; uint8_t v_isShared_6722_; uint8_t v_isSharedCheck_6735_; 
v___x_6711_ = lean_st_ref_take(v___y_6702_);
v_env_6712_ = lean_ctor_get(v___x_6711_, 0);
v_nextMacroScope_6713_ = lean_ctor_get(v___x_6711_, 1);
v_auxDeclNGen_6714_ = lean_ctor_get(v___x_6711_, 3);
v_traceState_6715_ = lean_ctor_get(v___x_6711_, 4);
v_cache_6716_ = lean_ctor_get(v___x_6711_, 5);
v_messages_6717_ = lean_ctor_get(v___x_6711_, 6);
v_infoState_6718_ = lean_ctor_get(v___x_6711_, 7);
v_snapshotTasks_6719_ = lean_ctor_get(v___x_6711_, 8);
v_isSharedCheck_6735_ = !lean_is_exclusive(v___x_6711_);
if (v_isSharedCheck_6735_ == 0)
{
lean_object* v_unused_6736_; 
v_unused_6736_ = lean_ctor_get(v___x_6711_, 2);
lean_dec(v_unused_6736_);
v___x_6721_ = v___x_6711_;
v_isShared_6722_ = v_isSharedCheck_6735_;
goto v_resetjp_6720_;
}
else
{
lean_inc(v_snapshotTasks_6719_);
lean_inc(v_infoState_6718_);
lean_inc(v_messages_6717_);
lean_inc(v_cache_6716_);
lean_inc(v_traceState_6715_);
lean_inc(v_auxDeclNGen_6714_);
lean_inc(v_nextMacroScope_6713_);
lean_inc(v_env_6712_);
lean_dec(v___x_6711_);
v___x_6721_ = lean_box(0);
v_isShared_6722_ = v_isSharedCheck_6735_;
goto v_resetjp_6720_;
}
v_resetjp_6720_:
{
lean_object* v___x_6723_; lean_object* v___x_6724_; lean_object* v___x_6725_; lean_object* v___x_6727_; 
lean_inc(v_idx_6707_);
lean_inc(v_namePrefix_6706_);
v___x_6723_ = l_Lean_Name_num___override(v_namePrefix_6706_, v_idx_6707_);
v___x_6724_ = lean_unsigned_to_nat(1u);
v___x_6725_ = lean_nat_add(v_idx_6707_, v___x_6724_);
lean_dec(v_idx_6707_);
if (v_isShared_6710_ == 0)
{
lean_ctor_set(v___x_6709_, 1, v___x_6725_);
v___x_6727_ = v___x_6709_;
goto v_reusejp_6726_;
}
else
{
lean_object* v_reuseFailAlloc_6734_; 
v_reuseFailAlloc_6734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6734_, 0, v_namePrefix_6706_);
lean_ctor_set(v_reuseFailAlloc_6734_, 1, v___x_6725_);
v___x_6727_ = v_reuseFailAlloc_6734_;
goto v_reusejp_6726_;
}
v_reusejp_6726_:
{
lean_object* v___x_6729_; 
if (v_isShared_6722_ == 0)
{
lean_ctor_set(v___x_6721_, 2, v___x_6727_);
v___x_6729_ = v___x_6721_;
goto v_reusejp_6728_;
}
else
{
lean_object* v_reuseFailAlloc_6733_; 
v_reuseFailAlloc_6733_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6733_, 0, v_env_6712_);
lean_ctor_set(v_reuseFailAlloc_6733_, 1, v_nextMacroScope_6713_);
lean_ctor_set(v_reuseFailAlloc_6733_, 2, v___x_6727_);
lean_ctor_set(v_reuseFailAlloc_6733_, 3, v_auxDeclNGen_6714_);
lean_ctor_set(v_reuseFailAlloc_6733_, 4, v_traceState_6715_);
lean_ctor_set(v_reuseFailAlloc_6733_, 5, v_cache_6716_);
lean_ctor_set(v_reuseFailAlloc_6733_, 6, v_messages_6717_);
lean_ctor_set(v_reuseFailAlloc_6733_, 7, v_infoState_6718_);
lean_ctor_set(v_reuseFailAlloc_6733_, 8, v_snapshotTasks_6719_);
v___x_6729_ = v_reuseFailAlloc_6733_;
goto v_reusejp_6728_;
}
v_reusejp_6728_:
{
lean_object* v___x_6730_; lean_object* v___x_6731_; lean_object* v___x_6732_; 
v___x_6730_ = lean_st_ref_put(v___y_6702_, v___x_6729_);
v___x_6731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6731_, 0, v___x_6723_);
lean_ctor_set(v___x_6731_, 1, v___x_6724_);
v___x_6732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6732_, 0, v___x_6731_);
return v___x_6732_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg___boxed(lean_object* v___y_6738_, lean_object* v___y_6739_){
_start:
{
lean_object* v_res_6740_; 
v_res_6740_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(v___y_6738_);
lean_dec(v___y_6738_);
return v_res_6740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1(lean_object* v___y_6741_, lean_object* v___y_6742_){
_start:
{
lean_object* v___x_6744_; 
v___x_6744_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(v___y_6742_);
return v___x_6744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___boxed(lean_object* v___y_6745_, lean_object* v___y_6746_, lean_object* v___y_6747_){
_start:
{
lean_object* v_res_6748_; 
v_res_6748_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1(v___y_6745_, v___y_6746_);
lean_dec(v___y_6746_);
lean_dec_ref(v___y_6745_);
return v_res_6748_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0(void){
_start:
{
lean_object* v___x_6749_; lean_object* v___x_6750_; lean_object* v___x_6751_; 
v___x_6749_ = lean_unsigned_to_nat(32u);
v___x_6750_ = lean_mk_empty_array_with_capacity(v___x_6749_);
v___x_6751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6751_, 0, v___x_6750_);
return v___x_6751_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1(void){
_start:
{
size_t v___x_6752_; lean_object* v___x_6753_; lean_object* v___x_6754_; lean_object* v___x_6755_; lean_object* v___x_6756_; lean_object* v___x_6757_; 
v___x_6752_ = ((size_t)5ULL);
v___x_6753_ = lean_unsigned_to_nat(0u);
v___x_6754_ = lean_unsigned_to_nat(32u);
v___x_6755_ = lean_mk_empty_array_with_capacity(v___x_6754_);
v___x_6756_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0);
v___x_6757_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_6757_, 0, v___x_6756_);
lean_ctor_set(v___x_6757_, 1, v___x_6755_);
lean_ctor_set(v___x_6757_, 2, v___x_6753_);
lean_ctor_set(v___x_6757_, 3, v___x_6753_);
lean_ctor_set_usize(v___x_6757_, 4, v___x_6752_);
return v___x_6757_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2(void){
_start:
{
lean_object* v___x_6758_; lean_object* v___x_6759_; lean_object* v___x_6760_; lean_object* v___x_6761_; 
v___x_6758_ = lean_box(1);
v___x_6759_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1);
v___x_6760_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_6761_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6761_, 0, v___x_6760_);
lean_ctor_set(v___x_6761_, 1, v___x_6759_);
lean_ctor_set(v___x_6761_, 2, v___x_6758_);
return v___x_6761_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_msgData_6762_, lean_object* v___y_6763_, lean_object* v___y_6764_){
_start:
{
lean_object* v___x_6766_; lean_object* v_toCold_6767_; lean_object* v_env_6768_; lean_object* v_options_6769_; lean_object* v___x_6770_; lean_object* v___x_6771_; lean_object* v___x_6772_; lean_object* v___x_6773_; lean_object* v___x_6774_; 
v___x_6766_ = lean_st_ref_get(v___y_6764_);
v_toCold_6767_ = lean_ctor_get(v___y_6763_, 0);
v_env_6768_ = lean_ctor_get(v___x_6766_, 0);
lean_inc_ref(v_env_6768_);
lean_dec(v___x_6766_);
v_options_6769_ = lean_ctor_get(v_toCold_6767_, 2);
v___x_6770_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2);
v___x_6771_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2);
lean_inc_ref(v_options_6769_);
v___x_6772_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6772_, 0, v_env_6768_);
lean_ctor_set(v___x_6772_, 1, v___x_6770_);
lean_ctor_set(v___x_6772_, 2, v___x_6771_);
lean_ctor_set(v___x_6772_, 3, v_options_6769_);
v___x_6773_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_6773_, 0, v___x_6772_);
lean_ctor_set(v___x_6773_, 1, v_msgData_6762_);
v___x_6774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6774_, 0, v___x_6773_);
return v___x_6774_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(lean_object* v_msgData_6775_, lean_object* v___y_6776_, lean_object* v___y_6777_, lean_object* v___y_6778_){
_start:
{
lean_object* v_res_6779_; 
v_res_6779_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5(v_msgData_6775_, v___y_6776_, v___y_6777_);
lean_dec(v___y_6777_);
lean_dec_ref(v___y_6776_);
return v_res_6779_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4(lean_object* v_ref_6780_, lean_object* v_msgData_6781_, uint8_t v_severity_6782_, uint8_t v_isSilent_6783_, lean_object* v___y_6784_, lean_object* v___y_6785_){
_start:
{
uint8_t v___y_6788_; lean_object* v___y_6789_; lean_object* v___y_6790_; lean_object* v___y_6791_; uint8_t v___y_6792_; lean_object* v___y_6793_; lean_object* v___y_6794_; lean_object* v___y_6795_; lean_object* v___y_6796_; lean_object* v___y_6825_; uint8_t v___y_6826_; uint8_t v___y_6827_; lean_object* v___y_6828_; lean_object* v___y_6829_; lean_object* v___y_6830_; uint8_t v___y_6831_; lean_object* v___y_6832_; lean_object* v___y_6850_; uint8_t v___y_6851_; uint8_t v___y_6852_; lean_object* v___y_6853_; lean_object* v___y_6854_; uint8_t v___y_6855_; lean_object* v___y_6856_; lean_object* v___y_6857_; lean_object* v___y_6861_; uint8_t v___y_6862_; uint8_t v___y_6863_; lean_object* v___y_6864_; lean_object* v___y_6865_; lean_object* v___y_6866_; uint8_t v___y_6867_; uint8_t v___x_6872_; lean_object* v___y_6874_; lean_object* v___y_6875_; lean_object* v___y_6876_; uint8_t v___y_6877_; uint8_t v___y_6878_; lean_object* v___y_6879_; uint8_t v___y_6880_; uint8_t v___y_6882_; uint8_t v___x_6898_; 
v___x_6872_ = 2;
v___x_6898_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6782_, v___x_6872_);
if (v___x_6898_ == 0)
{
v___y_6882_ = v___x_6898_;
goto v___jp_6881_;
}
else
{
uint8_t v___x_6899_; 
lean_inc_ref(v_msgData_6781_);
v___x_6899_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_6781_);
v___y_6882_ = v___x_6899_;
goto v___jp_6881_;
}
v___jp_6787_:
{
lean_object* v___x_6797_; lean_object* v_toCold_6798_; lean_object* v_currNamespace_6799_; lean_object* v_openDecls_6800_; lean_object* v_env_6801_; lean_object* v_nextMacroScope_6802_; lean_object* v_ngen_6803_; lean_object* v_auxDeclNGen_6804_; lean_object* v_traceState_6805_; lean_object* v_cache_6806_; lean_object* v_messages_6807_; lean_object* v_infoState_6808_; lean_object* v_snapshotTasks_6809_; lean_object* v___x_6811_; uint8_t v_isShared_6812_; uint8_t v_isSharedCheck_6823_; 
v___x_6797_ = lean_st_ref_take(v___y_6796_);
v_toCold_6798_ = lean_ctor_get(v___y_6795_, 0);
v_currNamespace_6799_ = lean_ctor_get(v_toCold_6798_, 4);
v_openDecls_6800_ = lean_ctor_get(v_toCold_6798_, 5);
v_env_6801_ = lean_ctor_get(v___x_6797_, 0);
v_nextMacroScope_6802_ = lean_ctor_get(v___x_6797_, 1);
v_ngen_6803_ = lean_ctor_get(v___x_6797_, 2);
v_auxDeclNGen_6804_ = lean_ctor_get(v___x_6797_, 3);
v_traceState_6805_ = lean_ctor_get(v___x_6797_, 4);
v_cache_6806_ = lean_ctor_get(v___x_6797_, 5);
v_messages_6807_ = lean_ctor_get(v___x_6797_, 6);
v_infoState_6808_ = lean_ctor_get(v___x_6797_, 7);
v_snapshotTasks_6809_ = lean_ctor_get(v___x_6797_, 8);
v_isSharedCheck_6823_ = !lean_is_exclusive(v___x_6797_);
if (v_isSharedCheck_6823_ == 0)
{
v___x_6811_ = v___x_6797_;
v_isShared_6812_ = v_isSharedCheck_6823_;
goto v_resetjp_6810_;
}
else
{
lean_inc(v_snapshotTasks_6809_);
lean_inc(v_infoState_6808_);
lean_inc(v_messages_6807_);
lean_inc(v_cache_6806_);
lean_inc(v_traceState_6805_);
lean_inc(v_auxDeclNGen_6804_);
lean_inc(v_ngen_6803_);
lean_inc(v_nextMacroScope_6802_);
lean_inc(v_env_6801_);
lean_dec(v___x_6797_);
v___x_6811_ = lean_box(0);
v_isShared_6812_ = v_isSharedCheck_6823_;
goto v_resetjp_6810_;
}
v_resetjp_6810_:
{
lean_object* v___x_6813_; lean_object* v___x_6814_; lean_object* v___x_6815_; lean_object* v___x_6816_; lean_object* v___x_6818_; 
lean_inc(v_openDecls_6800_);
lean_inc(v_currNamespace_6799_);
v___x_6813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6813_, 0, v_currNamespace_6799_);
lean_ctor_set(v___x_6813_, 1, v_openDecls_6800_);
v___x_6814_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6814_, 0, v___x_6813_);
lean_ctor_set(v___x_6814_, 1, v___y_6789_);
lean_inc_ref(v___y_6791_);
lean_inc_ref(v___y_6793_);
v___x_6815_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_6815_, 0, v___y_6793_);
lean_ctor_set(v___x_6815_, 1, v___y_6794_);
lean_ctor_set(v___x_6815_, 2, v___y_6790_);
lean_ctor_set(v___x_6815_, 3, v___y_6791_);
lean_ctor_set(v___x_6815_, 4, v___x_6814_);
lean_ctor_set_uint8(v___x_6815_, sizeof(void*)*5, v___y_6788_);
lean_ctor_set_uint8(v___x_6815_, sizeof(void*)*5 + 1, v___y_6792_);
lean_ctor_set_uint8(v___x_6815_, sizeof(void*)*5 + 2, v_isSilent_6783_);
v___x_6816_ = l_Lean_MessageLog_add(v___x_6815_, v_messages_6807_);
if (v_isShared_6812_ == 0)
{
lean_ctor_set(v___x_6811_, 6, v___x_6816_);
v___x_6818_ = v___x_6811_;
goto v_reusejp_6817_;
}
else
{
lean_object* v_reuseFailAlloc_6822_; 
v_reuseFailAlloc_6822_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6822_, 0, v_env_6801_);
lean_ctor_set(v_reuseFailAlloc_6822_, 1, v_nextMacroScope_6802_);
lean_ctor_set(v_reuseFailAlloc_6822_, 2, v_ngen_6803_);
lean_ctor_set(v_reuseFailAlloc_6822_, 3, v_auxDeclNGen_6804_);
lean_ctor_set(v_reuseFailAlloc_6822_, 4, v_traceState_6805_);
lean_ctor_set(v_reuseFailAlloc_6822_, 5, v_cache_6806_);
lean_ctor_set(v_reuseFailAlloc_6822_, 6, v___x_6816_);
lean_ctor_set(v_reuseFailAlloc_6822_, 7, v_infoState_6808_);
lean_ctor_set(v_reuseFailAlloc_6822_, 8, v_snapshotTasks_6809_);
v___x_6818_ = v_reuseFailAlloc_6822_;
goto v_reusejp_6817_;
}
v_reusejp_6817_:
{
lean_object* v___x_6819_; lean_object* v___x_6820_; lean_object* v___x_6821_; 
v___x_6819_ = lean_st_ref_put(v___y_6796_, v___x_6818_);
v___x_6820_ = lean_box(0);
v___x_6821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6821_, 0, v___x_6820_);
return v___x_6821_;
}
}
}
v___jp_6824_:
{
lean_object* v___x_6833_; lean_object* v___x_6834_; lean_object* v_a_6835_; lean_object* v___x_6837_; uint8_t v_isShared_6838_; uint8_t v_isSharedCheck_6848_; 
v___x_6833_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_6781_);
v___x_6834_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5(v___x_6833_, v___y_6784_, v___y_6785_);
v_a_6835_ = lean_ctor_get(v___x_6834_, 0);
v_isSharedCheck_6848_ = !lean_is_exclusive(v___x_6834_);
if (v_isSharedCheck_6848_ == 0)
{
v___x_6837_ = v___x_6834_;
v_isShared_6838_ = v_isSharedCheck_6848_;
goto v_resetjp_6836_;
}
else
{
lean_inc(v_a_6835_);
lean_dec(v___x_6834_);
v___x_6837_ = lean_box(0);
v_isShared_6838_ = v_isSharedCheck_6848_;
goto v_resetjp_6836_;
}
v_resetjp_6836_:
{
lean_object* v___x_6839_; lean_object* v___x_6840_; lean_object* v___x_6841_; lean_object* v___x_6842_; 
lean_inc_ref_n(v___y_6829_, 2);
v___x_6839_ = l_Lean_FileMap_toPosition(v___y_6829_, v___y_6828_);
lean_dec(v___y_6828_);
v___x_6840_ = l_Lean_FileMap_toPosition(v___y_6829_, v___y_6832_);
lean_dec(v___y_6832_);
v___x_6841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6841_, 0, v___x_6840_);
v___x_6842_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___closed__0));
if (v___y_6827_ == 0)
{
lean_del_object(v___x_6837_);
lean_dec_ref(v___y_6825_);
v___y_6788_ = v___y_6826_;
v___y_6789_ = v_a_6835_;
v___y_6790_ = v___x_6841_;
v___y_6791_ = v___x_6842_;
v___y_6792_ = v___y_6831_;
v___y_6793_ = v___y_6830_;
v___y_6794_ = v___x_6839_;
v___y_6795_ = v___y_6784_;
v___y_6796_ = v___y_6785_;
goto v___jp_6787_;
}
else
{
uint8_t v___x_6843_; 
lean_inc(v_a_6835_);
v___x_6843_ = l_Lean_MessageData_hasTag(v___y_6825_, v_a_6835_);
if (v___x_6843_ == 0)
{
lean_object* v___x_6844_; lean_object* v___x_6846_; 
lean_dec_ref_known(v___x_6841_, 1);
lean_dec_ref(v___x_6839_);
lean_dec(v_a_6835_);
v___x_6844_ = lean_box(0);
if (v_isShared_6838_ == 0)
{
lean_ctor_set(v___x_6837_, 0, v___x_6844_);
v___x_6846_ = v___x_6837_;
goto v_reusejp_6845_;
}
else
{
lean_object* v_reuseFailAlloc_6847_; 
v_reuseFailAlloc_6847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6847_, 0, v___x_6844_);
v___x_6846_ = v_reuseFailAlloc_6847_;
goto v_reusejp_6845_;
}
v_reusejp_6845_:
{
return v___x_6846_;
}
}
else
{
lean_del_object(v___x_6837_);
v___y_6788_ = v___y_6826_;
v___y_6789_ = v_a_6835_;
v___y_6790_ = v___x_6841_;
v___y_6791_ = v___x_6842_;
v___y_6792_ = v___y_6831_;
v___y_6793_ = v___y_6830_;
v___y_6794_ = v___x_6839_;
v___y_6795_ = v___y_6784_;
v___y_6796_ = v___y_6785_;
goto v___jp_6787_;
}
}
}
}
v___jp_6849_:
{
lean_object* v___x_6858_; 
v___x_6858_ = l_Lean_Syntax_getTailPos_x3f(v___y_6853_, v___y_6851_);
lean_dec(v___y_6853_);
if (lean_obj_tag(v___x_6858_) == 0)
{
lean_inc(v___y_6857_);
v___y_6825_ = v___y_6850_;
v___y_6826_ = v___y_6851_;
v___y_6827_ = v___y_6852_;
v___y_6828_ = v___y_6857_;
v___y_6829_ = v___y_6854_;
v___y_6830_ = v___y_6856_;
v___y_6831_ = v___y_6855_;
v___y_6832_ = v___y_6857_;
goto v___jp_6824_;
}
else
{
lean_object* v_val_6859_; 
v_val_6859_ = lean_ctor_get(v___x_6858_, 0);
lean_inc(v_val_6859_);
lean_dec_ref_known(v___x_6858_, 1);
v___y_6825_ = v___y_6850_;
v___y_6826_ = v___y_6851_;
v___y_6827_ = v___y_6852_;
v___y_6828_ = v___y_6857_;
v___y_6829_ = v___y_6854_;
v___y_6830_ = v___y_6856_;
v___y_6831_ = v___y_6855_;
v___y_6832_ = v_val_6859_;
goto v___jp_6824_;
}
}
v___jp_6860_:
{
lean_object* v_ref_6868_; lean_object* v___x_6869_; 
v_ref_6868_ = l_Lean_replaceRef(v_ref_6780_, v___y_6865_);
v___x_6869_ = l_Lean_Syntax_getPos_x3f(v_ref_6868_, v___y_6862_);
if (lean_obj_tag(v___x_6869_) == 0)
{
lean_object* v___x_6870_; 
v___x_6870_ = lean_unsigned_to_nat(0u);
v___y_6850_ = v___y_6861_;
v___y_6851_ = v___y_6862_;
v___y_6852_ = v___y_6863_;
v___y_6853_ = v_ref_6868_;
v___y_6854_ = v___y_6864_;
v___y_6855_ = v___y_6867_;
v___y_6856_ = v___y_6866_;
v___y_6857_ = v___x_6870_;
goto v___jp_6849_;
}
else
{
lean_object* v_val_6871_; 
v_val_6871_ = lean_ctor_get(v___x_6869_, 0);
lean_inc(v_val_6871_);
lean_dec_ref_known(v___x_6869_, 1);
v___y_6850_ = v___y_6861_;
v___y_6851_ = v___y_6862_;
v___y_6852_ = v___y_6863_;
v___y_6853_ = v_ref_6868_;
v___y_6854_ = v___y_6864_;
v___y_6855_ = v___y_6867_;
v___y_6856_ = v___y_6866_;
v___y_6857_ = v_val_6871_;
goto v___jp_6849_;
}
}
v___jp_6873_:
{
if (v___y_6880_ == 0)
{
v___y_6861_ = v___y_6876_;
v___y_6862_ = v___y_6877_;
v___y_6863_ = v___y_6878_;
v___y_6864_ = v___y_6874_;
v___y_6865_ = v___y_6879_;
v___y_6866_ = v___y_6875_;
v___y_6867_ = v_severity_6782_;
goto v___jp_6860_;
}
else
{
v___y_6861_ = v___y_6876_;
v___y_6862_ = v___y_6877_;
v___y_6863_ = v___y_6878_;
v___y_6864_ = v___y_6874_;
v___y_6865_ = v___y_6879_;
v___y_6866_ = v___y_6875_;
v___y_6867_ = v___x_6872_;
goto v___jp_6860_;
}
}
v___jp_6881_:
{
if (v___y_6882_ == 0)
{
lean_object* v_toCold_6883_; lean_object* v_ref_6884_; uint8_t v_suppressElabErrors_6885_; lean_object* v_fileName_6886_; lean_object* v_fileMap_6887_; lean_object* v_options_6888_; lean_object* v___x_6889_; lean_object* v___x_6890_; lean_object* v___f_6891_; uint8_t v___x_6892_; uint8_t v___x_6893_; 
v_toCold_6883_ = lean_ctor_get(v___y_6784_, 0);
v_ref_6884_ = lean_ctor_get(v___y_6784_, 2);
v_suppressElabErrors_6885_ = lean_ctor_get_uint8(v___y_6784_, sizeof(void*)*3 + 1);
v_fileName_6886_ = lean_ctor_get(v_toCold_6883_, 0);
v_fileMap_6887_ = lean_ctor_get(v_toCold_6883_, 1);
v_options_6888_ = lean_ctor_get(v_toCold_6883_, 2);
v___x_6889_ = lean_box(v_suppressElabErrors_6885_);
v___x_6890_ = lean_box(v___y_6882_);
v___f_6891_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_6891_, 0, v___x_6889_);
lean_closure_set(v___f_6891_, 1, v___x_6890_);
v___x_6892_ = 1;
v___x_6893_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6782_, v___x_6892_);
if (v___x_6893_ == 0)
{
v___y_6874_ = v_fileMap_6887_;
v___y_6875_ = v_fileName_6886_;
v___y_6876_ = v___f_6891_;
v___y_6877_ = v___y_6882_;
v___y_6878_ = v_suppressElabErrors_6885_;
v___y_6879_ = v_ref_6884_;
v___y_6880_ = v___x_6893_;
goto v___jp_6873_;
}
else
{
lean_object* v___x_6894_; uint8_t v___x_6895_; 
v___x_6894_ = l_Lean_warningAsError;
v___x_6895_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(v_options_6888_, v___x_6894_);
v___y_6874_ = v_fileMap_6887_;
v___y_6875_ = v_fileName_6886_;
v___y_6876_ = v___f_6891_;
v___y_6877_ = v___y_6882_;
v___y_6878_ = v_suppressElabErrors_6885_;
v___y_6879_ = v_ref_6884_;
v___y_6880_ = v___x_6895_;
goto v___jp_6873_;
}
}
else
{
lean_object* v___x_6896_; lean_object* v___x_6897_; 
lean_dec_ref(v_msgData_6781_);
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
v_ref_6916_ = lean_ctor_get(v___y_6913_, 2);
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
v___x_7074_ = lean_st_ref_swap(v_val_7060_, v___x_7073_);
lean_dec(v_val_7060_);
lean_dec(v___x_7074_);
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
lean_object* v_toCold_7124_; lean_object* v_options_7125_; lean_object* v___f_7126_; lean_object* v___x_7127_; lean_object* v___x_7128_; lean_object* v___x_7129_; 
v_toCold_7124_ = lean_ctor_get(v_a_7121_, 0);
v_options_7125_ = lean_ctor_get(v_toCold_7124_, 2);
v___f_7126_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_7126_, 0, v_entriesForConst_7116_);
lean_closure_set(v___f_7126_, 1, v_droppedEntriesRef_7118_);
lean_closure_set(v___f_7126_, 2, v_droppedKeys_7117_);
v___x_7127_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___closed__0));
v___x_7128_ = lean_box(0);
v___x_7129_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v___x_7127_, v_options_7125_, v___f_7126_, v___x_7128_, v_a_7119_, v_a_7120_, v_a_7121_, v_a_7122_);
return v___x_7129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___boxed(lean_object* v_entriesForConst_7130_, lean_object* v_droppedKeys_7131_, lean_object* v_droppedEntriesRef_7132_, lean_object* v_a_7133_, lean_object* v_a_7134_, lean_object* v_a_7135_, lean_object* v_a_7136_, lean_object* v_a_7137_){
_start:
{
lean_object* v_res_7138_; 
v_res_7138_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v_entriesForConst_7130_, v_droppedKeys_7131_, v_droppedEntriesRef_7132_, v_a_7133_, v_a_7134_, v_a_7135_, v_a_7136_);
lean_dec(v_a_7136_);
lean_dec_ref(v_a_7135_);
lean_dec(v_a_7134_);
lean_dec_ref(v_a_7133_);
return v_res_7138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef(lean_object* v_00_u03b1_7139_, lean_object* v_entriesForConst_7140_, lean_object* v_droppedKeys_7141_, lean_object* v_droppedEntriesRef_7142_, lean_object* v_a_7143_, lean_object* v_a_7144_, lean_object* v_a_7145_, lean_object* v_a_7146_){
_start:
{
lean_object* v___x_7148_; 
v___x_7148_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v_entriesForConst_7140_, v_droppedKeys_7141_, v_droppedEntriesRef_7142_, v_a_7143_, v_a_7144_, v_a_7145_, v_a_7146_);
return v___x_7148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___boxed(lean_object* v_00_u03b1_7149_, lean_object* v_entriesForConst_7150_, lean_object* v_droppedKeys_7151_, lean_object* v_droppedEntriesRef_7152_, lean_object* v_a_7153_, lean_object* v_a_7154_, lean_object* v_a_7155_, lean_object* v_a_7156_, lean_object* v_a_7157_){
_start:
{
lean_object* v_res_7158_; 
v_res_7158_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef(v_00_u03b1_7149_, v_entriesForConst_7150_, v_droppedKeys_7151_, v_droppedEntriesRef_7152_, v_a_7153_, v_a_7154_, v_a_7155_, v_a_7156_);
lean_dec(v_a_7156_);
lean_dec_ref(v_a_7155_);
lean_dec(v_a_7154_);
lean_dec_ref(v_a_7153_);
return v_res_7158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0(lean_object* v_moduleRef_7159_, lean_object* v_ty_7160_, lean_object* v___y_7161_, lean_object* v___y_7162_, lean_object* v___y_7163_, lean_object* v___y_7164_){
_start:
{
lean_object* v___x_7166_; lean_object* v___x_7167_; 
v___x_7166_ = lean_st_ref_get(v_moduleRef_7159_);
v___x_7167_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v___x_7166_, v_ty_7160_, v___y_7161_, v___y_7162_, v___y_7163_, v___y_7164_);
if (lean_obj_tag(v___x_7167_) == 0)
{
lean_object* v_a_7168_; lean_object* v___x_7170_; uint8_t v_isShared_7171_; uint8_t v_isSharedCheck_7178_; 
v_a_7168_ = lean_ctor_get(v___x_7167_, 0);
v_isSharedCheck_7178_ = !lean_is_exclusive(v___x_7167_);
if (v_isSharedCheck_7178_ == 0)
{
v___x_7170_ = v___x_7167_;
v_isShared_7171_ = v_isSharedCheck_7178_;
goto v_resetjp_7169_;
}
else
{
lean_inc(v_a_7168_);
lean_dec(v___x_7167_);
v___x_7170_ = lean_box(0);
v_isShared_7171_ = v_isSharedCheck_7178_;
goto v_resetjp_7169_;
}
v_resetjp_7169_:
{
lean_object* v_fst_7172_; lean_object* v_snd_7173_; lean_object* v___x_7174_; lean_object* v___x_7176_; 
v_fst_7172_ = lean_ctor_get(v_a_7168_, 0);
lean_inc(v_fst_7172_);
v_snd_7173_ = lean_ctor_get(v_a_7168_, 1);
lean_inc(v_snd_7173_);
lean_dec(v_a_7168_);
v___x_7174_ = lean_st_ref_swap(v_moduleRef_7159_, v_snd_7173_);
lean_dec(v___x_7174_);
if (v_isShared_7171_ == 0)
{
lean_ctor_set(v___x_7170_, 0, v_fst_7172_);
v___x_7176_ = v___x_7170_;
goto v_reusejp_7175_;
}
else
{
lean_object* v_reuseFailAlloc_7177_; 
v_reuseFailAlloc_7177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7177_, 0, v_fst_7172_);
v___x_7176_ = v_reuseFailAlloc_7177_;
goto v_reusejp_7175_;
}
v_reusejp_7175_:
{
return v___x_7176_;
}
}
}
else
{
lean_object* v_a_7179_; lean_object* v___x_7181_; uint8_t v_isShared_7182_; uint8_t v_isSharedCheck_7186_; 
v_a_7179_ = lean_ctor_get(v___x_7167_, 0);
v_isSharedCheck_7186_ = !lean_is_exclusive(v___x_7167_);
if (v_isSharedCheck_7186_ == 0)
{
v___x_7181_ = v___x_7167_;
v_isShared_7182_ = v_isSharedCheck_7186_;
goto v_resetjp_7180_;
}
else
{
lean_inc(v_a_7179_);
lean_dec(v___x_7167_);
v___x_7181_ = lean_box(0);
v_isShared_7182_ = v_isSharedCheck_7186_;
goto v_resetjp_7180_;
}
v_resetjp_7180_:
{
lean_object* v___x_7184_; 
if (v_isShared_7182_ == 0)
{
v___x_7184_ = v___x_7181_;
goto v_reusejp_7183_;
}
else
{
lean_object* v_reuseFailAlloc_7185_; 
v_reuseFailAlloc_7185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7185_, 0, v_a_7179_);
v___x_7184_ = v_reuseFailAlloc_7185_;
goto v_reusejp_7183_;
}
v_reusejp_7183_:
{
return v___x_7184_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0___boxed(lean_object* v_moduleRef_7187_, lean_object* v_ty_7188_, lean_object* v___y_7189_, lean_object* v___y_7190_, lean_object* v___y_7191_, lean_object* v___y_7192_, lean_object* v___y_7193_){
_start:
{
lean_object* v_res_7194_; 
v_res_7194_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0(v_moduleRef_7187_, v_ty_7188_, v___y_7189_, v___y_7190_, v___y_7191_, v___y_7192_);
lean_dec(v___y_7192_);
lean_dec_ref(v___y_7191_);
lean_dec(v___y_7190_);
lean_dec_ref(v___y_7189_);
lean_dec(v_moduleRef_7187_);
return v_res_7194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(lean_object* v_moduleRef_7196_, lean_object* v_ty_7197_, lean_object* v_a_7198_, lean_object* v_a_7199_, lean_object* v_a_7200_, lean_object* v_a_7201_){
_start:
{
lean_object* v_toCold_7203_; lean_object* v_options_7204_; lean_object* v___f_7205_; lean_object* v___x_7206_; lean_object* v___x_7207_; lean_object* v___x_7208_; 
v_toCold_7203_ = lean_ctor_get(v_a_7200_, 0);
v_options_7204_ = lean_ctor_get(v_toCold_7203_, 2);
v___f_7205_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_7205_, 0, v_moduleRef_7196_);
lean_closure_set(v___f_7205_, 1, v_ty_7197_);
v___x_7206_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___closed__0));
v___x_7207_ = lean_box(0);
v___x_7208_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v___x_7206_, v_options_7204_, v___f_7205_, v___x_7207_, v_a_7198_, v_a_7199_, v_a_7200_, v_a_7201_);
return v___x_7208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___boxed(lean_object* v_moduleRef_7209_, lean_object* v_ty_7210_, lean_object* v_a_7211_, lean_object* v_a_7212_, lean_object* v_a_7213_, lean_object* v_a_7214_, lean_object* v_a_7215_){
_start:
{
lean_object* v_res_7216_; 
v_res_7216_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(v_moduleRef_7209_, v_ty_7210_, v_a_7211_, v_a_7212_, v_a_7213_, v_a_7214_);
lean_dec(v_a_7214_);
lean_dec_ref(v_a_7213_);
lean_dec(v_a_7212_);
lean_dec_ref(v_a_7211_);
return v_res_7216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches(lean_object* v_00_u03b1_7217_, lean_object* v_moduleRef_7218_, lean_object* v_ty_7219_, lean_object* v_a_7220_, lean_object* v_a_7221_, lean_object* v_a_7222_, lean_object* v_a_7223_){
_start:
{
lean_object* v___x_7225_; 
v___x_7225_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(v_moduleRef_7218_, v_ty_7219_, v_a_7220_, v_a_7221_, v_a_7222_, v_a_7223_);
return v___x_7225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___boxed(lean_object* v_00_u03b1_7226_, lean_object* v_moduleRef_7227_, lean_object* v_ty_7228_, lean_object* v_a_7229_, lean_object* v_a_7230_, lean_object* v_a_7231_, lean_object* v_a_7232_, lean_object* v_a_7233_){
_start:
{
lean_object* v_res_7234_; 
v_res_7234_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches(v_00_u03b1_7226_, v_moduleRef_7227_, v_ty_7228_, v_a_7229_, v_a_7230_, v_a_7231_, v_a_7232_);
lean_dec(v_a_7232_);
lean_dec_ref(v_a_7231_);
lean_dec(v_a_7230_);
lean_dec_ref(v_a_7229_);
return v_res_7234_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(lean_object* v_adjustResult_7235_, lean_object* v_j_7236_, size_t v_sz_7237_, size_t v_i_7238_, lean_object* v_bs_7239_){
_start:
{
uint8_t v___x_7240_; 
v___x_7240_ = lean_usize_dec_lt(v_i_7238_, v_sz_7237_);
if (v___x_7240_ == 0)
{
lean_dec(v_j_7236_);
lean_dec(v_adjustResult_7235_);
return v_bs_7239_;
}
else
{
lean_object* v_v_7241_; lean_object* v___x_7242_; lean_object* v_bs_x27_7243_; lean_object* v___x_7244_; size_t v___x_7245_; size_t v___x_7246_; lean_object* v___x_7247_; 
v_v_7241_ = lean_array_uget(v_bs_7239_, v_i_7238_);
v___x_7242_ = lean_unsigned_to_nat(0u);
v_bs_x27_7243_ = lean_array_uset(v_bs_7239_, v_i_7238_, v___x_7242_);
lean_inc(v_adjustResult_7235_);
lean_inc(v_j_7236_);
v___x_7244_ = lean_apply_2(v_adjustResult_7235_, v_j_7236_, v_v_7241_);
v___x_7245_ = ((size_t)1ULL);
v___x_7246_ = lean_usize_add(v_i_7238_, v___x_7245_);
v___x_7247_ = lean_array_uset(v_bs_x27_7243_, v_i_7238_, v___x_7244_);
v_i_7238_ = v___x_7246_;
v_bs_7239_ = v___x_7247_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg___boxed(lean_object* v_adjustResult_7249_, lean_object* v_j_7250_, lean_object* v_sz_7251_, lean_object* v_i_7252_, lean_object* v_bs_7253_){
_start:
{
size_t v_sz_boxed_7254_; size_t v_i_boxed_7255_; lean_object* v_res_7256_; 
v_sz_boxed_7254_ = lean_unbox_usize(v_sz_7251_);
lean_dec(v_sz_7251_);
v_i_boxed_7255_ = lean_unbox_usize(v_i_7252_);
lean_dec(v_i_7252_);
v_res_7256_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(v_adjustResult_7249_, v_j_7250_, v_sz_boxed_7254_, v_i_boxed_7255_, v_bs_7253_);
return v_res_7256_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(lean_object* v_adjustResult_7257_, lean_object* v_j_7258_, lean_object* v_as_7259_, size_t v_i_7260_, size_t v_stop_7261_, lean_object* v_b_7262_){
_start:
{
uint8_t v___x_7263_; 
v___x_7263_ = lean_usize_dec_eq(v_i_7260_, v_stop_7261_);
if (v___x_7263_ == 0)
{
lean_object* v___x_7264_; size_t v_sz_7265_; size_t v___x_7266_; lean_object* v___x_7267_; lean_object* v___x_7268_; size_t v___x_7269_; size_t v___x_7270_; 
v___x_7264_ = lean_array_uget_borrowed(v_as_7259_, v_i_7260_);
v_sz_7265_ = lean_array_size(v___x_7264_);
v___x_7266_ = ((size_t)0ULL);
lean_inc(v___x_7264_);
lean_inc(v_j_7258_);
lean_inc(v_adjustResult_7257_);
v___x_7267_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(v_adjustResult_7257_, v_j_7258_, v_sz_7265_, v___x_7266_, v___x_7264_);
v___x_7268_ = l_Array_append___redArg(v_b_7262_, v___x_7267_);
lean_dec_ref(v___x_7267_);
v___x_7269_ = ((size_t)1ULL);
v___x_7270_ = lean_usize_add(v_i_7260_, v___x_7269_);
v_i_7260_ = v___x_7270_;
v_b_7262_ = v___x_7268_;
goto _start;
}
else
{
lean_dec(v_j_7258_);
lean_dec(v_adjustResult_7257_);
return v_b_7262_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg___boxed(lean_object* v_adjustResult_7272_, lean_object* v_j_7273_, lean_object* v_as_7274_, lean_object* v_i_7275_, lean_object* v_stop_7276_, lean_object* v_b_7277_){
_start:
{
size_t v_i_boxed_7278_; size_t v_stop_boxed_7279_; lean_object* v_res_7280_; 
v_i_boxed_7278_ = lean_unbox_usize(v_i_7275_);
lean_dec(v_i_7275_);
v_stop_boxed_7279_ = lean_unbox_usize(v_stop_7276_);
lean_dec(v_stop_7276_);
v_res_7280_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7272_, v_j_7273_, v_as_7274_, v_i_boxed_7278_, v_stop_boxed_7279_, v_b_7277_);
lean_dec_ref(v_as_7274_);
return v_res_7280_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(lean_object* v_n_7281_, lean_object* v_aa_7282_, lean_object* v_adjustResult_7283_, lean_object* v_n_7284_, lean_object* v_j_7285_, lean_object* v_a_7286_){
_start:
{
lean_object* v_zero_7287_; uint8_t v_isZero_7288_; 
v_zero_7287_ = lean_unsigned_to_nat(0u);
v_isZero_7288_ = lean_nat_dec_eq(v_j_7285_, v_zero_7287_);
if (v_isZero_7288_ == 1)
{
lean_dec(v_j_7285_);
lean_dec(v_adjustResult_7283_);
return v_a_7286_;
}
else
{
lean_object* v_one_7289_; lean_object* v_n_7290_; lean_object* v___x_7291_; lean_object* v___x_7292_; lean_object* v_j_7293_; lean_object* v_b_7294_; lean_object* v___x_7295_; uint8_t v___x_7296_; 
v_one_7289_ = lean_unsigned_to_nat(1u);
v_n_7290_ = lean_nat_sub(v_j_7285_, v_one_7289_);
v___x_7291_ = lean_nat_sub(v_n_7284_, v_j_7285_);
lean_dec(v_j_7285_);
v___x_7292_ = lean_nat_sub(v_n_7281_, v_one_7289_);
v_j_7293_ = lean_nat_sub(v___x_7292_, v___x_7291_);
lean_dec(v___x_7291_);
lean_dec(v___x_7292_);
v_b_7294_ = lean_array_fget_borrowed(v_aa_7282_, v_j_7293_);
v___x_7295_ = lean_array_get_size(v_b_7294_);
v___x_7296_ = lean_nat_dec_lt(v_zero_7287_, v___x_7295_);
if (v___x_7296_ == 0)
{
lean_dec(v_j_7293_);
v_j_7285_ = v_n_7290_;
goto _start;
}
else
{
size_t v___x_7298_; size_t v___x_7299_; lean_object* v___x_7300_; 
v___x_7298_ = ((size_t)0ULL);
v___x_7299_ = lean_usize_of_nat(v___x_7295_);
lean_inc(v_adjustResult_7283_);
v___x_7300_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7283_, v_j_7293_, v_b_7294_, v___x_7298_, v___x_7299_, v_a_7286_);
v_j_7285_ = v_n_7290_;
v_a_7286_ = v___x_7300_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_n_7302_, lean_object* v_aa_7303_, lean_object* v_adjustResult_7304_, lean_object* v_n_7305_, lean_object* v_j_7306_, lean_object* v_a_7307_){
_start:
{
lean_object* v_res_7308_; 
v_res_7308_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7302_, v_aa_7303_, v_adjustResult_7304_, v_n_7305_, v_j_7306_, v_a_7307_);
lean_dec(v_n_7305_);
lean_dec_ref(v_aa_7303_);
lean_dec(v_n_7302_);
return v_res_7308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(lean_object* v_n_7309_, lean_object* v_adjustResult_7310_, lean_object* v_aa_7311_, lean_object* v_n_7312_, lean_object* v_j_7313_, lean_object* v_a_7314_){
_start:
{
lean_object* v_zero_7315_; uint8_t v_isZero_7316_; 
v_zero_7315_ = lean_unsigned_to_nat(0u);
v_isZero_7316_ = lean_nat_dec_eq(v_j_7313_, v_zero_7315_);
if (v_isZero_7316_ == 1)
{
lean_dec(v_adjustResult_7310_);
return v_a_7314_;
}
else
{
lean_object* v_one_7317_; lean_object* v_n_7318_; lean_object* v___x_7319_; lean_object* v___x_7320_; lean_object* v_j_7321_; lean_object* v_b_7322_; lean_object* v___x_7323_; uint8_t v___x_7324_; 
v_one_7317_ = lean_unsigned_to_nat(1u);
v_n_7318_ = lean_nat_sub(v_j_7313_, v_one_7317_);
v___x_7319_ = lean_nat_sub(v_n_7312_, v_j_7313_);
v___x_7320_ = lean_nat_sub(v_n_7309_, v_one_7317_);
v_j_7321_ = lean_nat_sub(v___x_7320_, v___x_7319_);
lean_dec(v___x_7319_);
lean_dec(v___x_7320_);
v_b_7322_ = lean_array_fget_borrowed(v_aa_7311_, v_j_7321_);
v___x_7323_ = lean_array_get_size(v_b_7322_);
v___x_7324_ = lean_nat_dec_lt(v_zero_7315_, v___x_7323_);
if (v___x_7324_ == 0)
{
lean_object* v___x_7325_; 
lean_dec(v_j_7321_);
v___x_7325_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7309_, v_aa_7311_, v_adjustResult_7310_, v_n_7312_, v_n_7318_, v_a_7314_);
return v___x_7325_;
}
else
{
size_t v___x_7326_; size_t v___x_7327_; lean_object* v___x_7328_; lean_object* v___x_7329_; 
v___x_7326_ = ((size_t)0ULL);
v___x_7327_ = lean_usize_of_nat(v___x_7323_);
lean_inc(v_adjustResult_7310_);
v___x_7328_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7310_, v_j_7321_, v_b_7322_, v___x_7326_, v___x_7327_, v_a_7314_);
v___x_7329_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7309_, v_aa_7311_, v_adjustResult_7310_, v_n_7312_, v_n_7318_, v___x_7328_);
return v___x_7329_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg___boxed(lean_object* v_n_7330_, lean_object* v_adjustResult_7331_, lean_object* v_aa_7332_, lean_object* v_n_7333_, lean_object* v_j_7334_, lean_object* v_a_7335_){
_start:
{
lean_object* v_res_7336_; 
v_res_7336_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(v_n_7330_, v_adjustResult_7331_, v_aa_7332_, v_n_7333_, v_j_7334_, v_a_7335_);
lean_dec(v_j_7334_);
lean_dec(v_n_7333_);
lean_dec_ref(v_aa_7332_);
lean_dec(v_n_7330_);
return v_res_7336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(lean_object* v_adjustResult_7337_, lean_object* v_mr_7338_, lean_object* v_a_7339_){
_start:
{
lean_object* v_n_7340_; lean_object* v___x_7341_; 
v_n_7340_ = lean_array_get_size(v_mr_7338_);
v___x_7341_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(v_n_7340_, v_adjustResult_7337_, v_mr_7338_, v_n_7340_, v_n_7340_, v_a_7339_);
return v___x_7341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg___boxed(lean_object* v_adjustResult_7342_, lean_object* v_mr_7343_, lean_object* v_a_7344_){
_start:
{
lean_object* v_res_7345_; 
v_res_7345_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7342_, v_mr_7343_, v_a_7344_);
lean_dec_ref(v_mr_7343_);
return v_res_7345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(lean_object* v_moduleTreeRef_7346_, lean_object* v_ref_7347_, lean_object* v_addEntry_7348_, lean_object* v_droppedKeys_7349_, lean_object* v_constantsPerTask_7350_, lean_object* v_droppedEntriesRef_7351_, lean_object* v_adjustResult_7352_, lean_object* v_ty_7353_, lean_object* v_a_7354_, lean_object* v_a_7355_, lean_object* v_a_7356_, lean_object* v_a_7357_){
_start:
{
lean_object* v___x_7359_; 
lean_inc_ref(v_ty_7353_);
v___x_7359_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(v_moduleTreeRef_7346_, v_ty_7353_, v_a_7354_, v_a_7355_, v_a_7356_, v_a_7357_);
if (lean_obj_tag(v___x_7359_) == 0)
{
lean_object* v_a_7360_; lean_object* v___x_7361_; 
v_a_7360_ = lean_ctor_get(v___x_7359_, 0);
lean_inc(v_a_7360_);
lean_dec_ref_known(v___x_7359_, 1);
v___x_7361_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(v_ref_7347_, v_addEntry_7348_, v_droppedKeys_7349_, v_constantsPerTask_7350_, v_droppedEntriesRef_7351_, v_ty_7353_, v_a_7354_, v_a_7355_, v_a_7356_, v_a_7357_);
if (lean_obj_tag(v___x_7361_) == 0)
{
lean_object* v_a_7362_; lean_object* v___x_7364_; uint8_t v_isShared_7365_; uint8_t v_isSharedCheck_7375_; 
v_a_7362_ = lean_ctor_get(v___x_7361_, 0);
v_isSharedCheck_7375_ = !lean_is_exclusive(v___x_7361_);
if (v_isSharedCheck_7375_ == 0)
{
v___x_7364_ = v___x_7361_;
v_isShared_7365_ = v_isSharedCheck_7375_;
goto v_resetjp_7363_;
}
else
{
lean_inc(v_a_7362_);
lean_dec(v___x_7361_);
v___x_7364_ = lean_box(0);
v_isShared_7365_ = v_isSharedCheck_7375_;
goto v_resetjp_7363_;
}
v_resetjp_7363_:
{
lean_object* v___x_7366_; lean_object* v___x_7367_; lean_object* v___x_7368_; lean_object* v___x_7369_; lean_object* v___x_7370_; lean_object* v___x_7371_; lean_object* v___x_7373_; 
v___x_7366_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_a_7360_);
v___x_7367_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_a_7362_);
v___x_7368_ = lean_nat_add(v___x_7366_, v___x_7367_);
lean_dec(v___x_7367_);
lean_dec(v___x_7366_);
v___x_7369_ = lean_mk_empty_array_with_capacity(v___x_7368_);
lean_dec(v___x_7368_);
lean_inc(v_adjustResult_7352_);
v___x_7370_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7352_, v_a_7360_, v___x_7369_);
lean_dec(v_a_7360_);
v___x_7371_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7352_, v_a_7362_, v___x_7370_);
lean_dec(v_a_7362_);
if (v_isShared_7365_ == 0)
{
lean_ctor_set(v___x_7364_, 0, v___x_7371_);
v___x_7373_ = v___x_7364_;
goto v_reusejp_7372_;
}
else
{
lean_object* v_reuseFailAlloc_7374_; 
v_reuseFailAlloc_7374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7374_, 0, v___x_7371_);
v___x_7373_ = v_reuseFailAlloc_7374_;
goto v_reusejp_7372_;
}
v_reusejp_7372_:
{
return v___x_7373_;
}
}
}
else
{
lean_object* v_a_7376_; lean_object* v___x_7378_; uint8_t v_isShared_7379_; uint8_t v_isSharedCheck_7383_; 
lean_dec(v_a_7360_);
lean_dec(v_adjustResult_7352_);
v_a_7376_ = lean_ctor_get(v___x_7361_, 0);
v_isSharedCheck_7383_ = !lean_is_exclusive(v___x_7361_);
if (v_isSharedCheck_7383_ == 0)
{
v___x_7378_ = v___x_7361_;
v_isShared_7379_ = v_isSharedCheck_7383_;
goto v_resetjp_7377_;
}
else
{
lean_inc(v_a_7376_);
lean_dec(v___x_7361_);
v___x_7378_ = lean_box(0);
v_isShared_7379_ = v_isSharedCheck_7383_;
goto v_resetjp_7377_;
}
v_resetjp_7377_:
{
lean_object* v___x_7381_; 
if (v_isShared_7379_ == 0)
{
v___x_7381_ = v___x_7378_;
goto v_reusejp_7380_;
}
else
{
lean_object* v_reuseFailAlloc_7382_; 
v_reuseFailAlloc_7382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7382_, 0, v_a_7376_);
v___x_7381_ = v_reuseFailAlloc_7382_;
goto v_reusejp_7380_;
}
v_reusejp_7380_:
{
return v___x_7381_;
}
}
}
}
else
{
lean_object* v_a_7384_; lean_object* v___x_7386_; uint8_t v_isShared_7387_; uint8_t v_isSharedCheck_7391_; 
lean_dec_ref(v_ty_7353_);
lean_dec(v_adjustResult_7352_);
lean_dec(v_droppedEntriesRef_7351_);
lean_dec(v_constantsPerTask_7350_);
lean_dec(v_droppedKeys_7349_);
lean_dec_ref(v_addEntry_7348_);
v_a_7384_ = lean_ctor_get(v___x_7359_, 0);
v_isSharedCheck_7391_ = !lean_is_exclusive(v___x_7359_);
if (v_isSharedCheck_7391_ == 0)
{
v___x_7386_ = v___x_7359_;
v_isShared_7387_ = v_isSharedCheck_7391_;
goto v_resetjp_7385_;
}
else
{
lean_inc(v_a_7384_);
lean_dec(v___x_7359_);
v___x_7386_ = lean_box(0);
v_isShared_7387_ = v_isSharedCheck_7391_;
goto v_resetjp_7385_;
}
v_resetjp_7385_:
{
lean_object* v___x_7389_; 
if (v_isShared_7387_ == 0)
{
v___x_7389_ = v___x_7386_;
goto v_reusejp_7388_;
}
else
{
lean_object* v_reuseFailAlloc_7390_; 
v_reuseFailAlloc_7390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7390_, 0, v_a_7384_);
v___x_7389_ = v_reuseFailAlloc_7390_;
goto v_reusejp_7388_;
}
v_reusejp_7388_:
{
return v___x_7389_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg___boxed(lean_object* v_moduleTreeRef_7392_, lean_object* v_ref_7393_, lean_object* v_addEntry_7394_, lean_object* v_droppedKeys_7395_, lean_object* v_constantsPerTask_7396_, lean_object* v_droppedEntriesRef_7397_, lean_object* v_adjustResult_7398_, lean_object* v_ty_7399_, lean_object* v_a_7400_, lean_object* v_a_7401_, lean_object* v_a_7402_, lean_object* v_a_7403_, lean_object* v_a_7404_){
_start:
{
lean_object* v_res_7405_; 
v_res_7405_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_moduleTreeRef_7392_, v_ref_7393_, v_addEntry_7394_, v_droppedKeys_7395_, v_constantsPerTask_7396_, v_droppedEntriesRef_7397_, v_adjustResult_7398_, v_ty_7399_, v_a_7400_, v_a_7401_, v_a_7402_, v_a_7403_);
lean_dec(v_a_7403_);
lean_dec_ref(v_a_7402_);
lean_dec(v_a_7401_);
lean_dec_ref(v_a_7400_);
lean_dec(v_ref_7393_);
return v_res_7405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt(lean_object* v_00_u03b1_7406_, lean_object* v_00_u03b2_7407_, lean_object* v_moduleTreeRef_7408_, lean_object* v_ref_7409_, lean_object* v_addEntry_7410_, lean_object* v_droppedKeys_7411_, lean_object* v_constantsPerTask_7412_, lean_object* v_droppedEntriesRef_7413_, lean_object* v_adjustResult_7414_, lean_object* v_ty_7415_, lean_object* v_a_7416_, lean_object* v_a_7417_, lean_object* v_a_7418_, lean_object* v_a_7419_){
_start:
{
lean_object* v___x_7421_; 
v___x_7421_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_moduleTreeRef_7408_, v_ref_7409_, v_addEntry_7410_, v_droppedKeys_7411_, v_constantsPerTask_7412_, v_droppedEntriesRef_7413_, v_adjustResult_7414_, v_ty_7415_, v_a_7416_, v_a_7417_, v_a_7418_, v_a_7419_);
return v___x_7421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___boxed(lean_object* v_00_u03b1_7422_, lean_object* v_00_u03b2_7423_, lean_object* v_moduleTreeRef_7424_, lean_object* v_ref_7425_, lean_object* v_addEntry_7426_, lean_object* v_droppedKeys_7427_, lean_object* v_constantsPerTask_7428_, lean_object* v_droppedEntriesRef_7429_, lean_object* v_adjustResult_7430_, lean_object* v_ty_7431_, lean_object* v_a_7432_, lean_object* v_a_7433_, lean_object* v_a_7434_, lean_object* v_a_7435_, lean_object* v_a_7436_){
_start:
{
lean_object* v_res_7437_; 
v_res_7437_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt(v_00_u03b1_7422_, v_00_u03b2_7423_, v_moduleTreeRef_7424_, v_ref_7425_, v_addEntry_7426_, v_droppedKeys_7427_, v_constantsPerTask_7428_, v_droppedEntriesRef_7429_, v_adjustResult_7430_, v_ty_7431_, v_a_7432_, v_a_7433_, v_a_7434_, v_a_7435_);
lean_dec(v_a_7435_);
lean_dec_ref(v_a_7434_);
lean_dec(v_a_7433_);
lean_dec_ref(v_a_7432_);
lean_dec(v_ref_7425_);
return v_res_7437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0(lean_object* v_00_u03b1_7438_, lean_object* v_00_u03b2_7439_, lean_object* v_adjustResult_7440_, lean_object* v_mr_7441_, lean_object* v_a_7442_){
_start:
{
lean_object* v___x_7443_; 
v___x_7443_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7440_, v_mr_7441_, v_a_7442_);
return v___x_7443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___boxed(lean_object* v_00_u03b1_7444_, lean_object* v_00_u03b2_7445_, lean_object* v_adjustResult_7446_, lean_object* v_mr_7447_, lean_object* v_a_7448_){
_start:
{
lean_object* v_res_7449_; 
v_res_7449_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0(v_00_u03b1_7444_, v_00_u03b2_7445_, v_adjustResult_7446_, v_mr_7447_, v_a_7448_);
lean_dec_ref(v_mr_7447_);
return v_res_7449_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0(lean_object* v_00_u03b1_7450_, lean_object* v_00_u03b2_7451_, lean_object* v_adjustResult_7452_, lean_object* v_j_7453_, size_t v_sz_7454_, size_t v_i_7455_, lean_object* v_bs_7456_){
_start:
{
lean_object* v___x_7457_; 
v___x_7457_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(v_adjustResult_7452_, v_j_7453_, v_sz_7454_, v_i_7455_, v_bs_7456_);
return v___x_7457_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___boxed(lean_object* v_00_u03b1_7458_, lean_object* v_00_u03b2_7459_, lean_object* v_adjustResult_7460_, lean_object* v_j_7461_, lean_object* v_sz_7462_, lean_object* v_i_7463_, lean_object* v_bs_7464_){
_start:
{
size_t v_sz_boxed_7465_; size_t v_i_boxed_7466_; lean_object* v_res_7467_; 
v_sz_boxed_7465_ = lean_unbox_usize(v_sz_7462_);
lean_dec(v_sz_7462_);
v_i_boxed_7466_ = lean_unbox_usize(v_i_7463_);
lean_dec(v_i_7463_);
v_res_7467_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0(v_00_u03b1_7458_, v_00_u03b2_7459_, v_adjustResult_7460_, v_j_7461_, v_sz_boxed_7465_, v_i_boxed_7466_, v_bs_7464_);
return v_res_7467_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1(lean_object* v_00_u03b1_7468_, lean_object* v_00_u03b2_7469_, lean_object* v_adjustResult_7470_, lean_object* v_j_7471_, lean_object* v_as_7472_, size_t v_i_7473_, size_t v_stop_7474_, lean_object* v_b_7475_){
_start:
{
lean_object* v___x_7476_; 
v___x_7476_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7470_, v_j_7471_, v_as_7472_, v_i_7473_, v_stop_7474_, v_b_7475_);
return v___x_7476_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___boxed(lean_object* v_00_u03b1_7477_, lean_object* v_00_u03b2_7478_, lean_object* v_adjustResult_7479_, lean_object* v_j_7480_, lean_object* v_as_7481_, lean_object* v_i_7482_, lean_object* v_stop_7483_, lean_object* v_b_7484_){
_start:
{
size_t v_i_boxed_7485_; size_t v_stop_boxed_7486_; lean_object* v_res_7487_; 
v_i_boxed_7485_ = lean_unbox_usize(v_i_7482_);
lean_dec(v_i_7482_);
v_stop_boxed_7486_ = lean_unbox_usize(v_stop_7483_);
lean_dec(v_stop_7483_);
v_res_7487_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1(v_00_u03b1_7477_, v_00_u03b2_7478_, v_adjustResult_7479_, v_j_7480_, v_as_7481_, v_i_boxed_7485_, v_stop_boxed_7486_, v_b_7484_);
lean_dec_ref(v_as_7481_);
return v_res_7487_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2(lean_object* v_00_u03b2_7488_, lean_object* v_n_7489_, lean_object* v_00_u03b1_7490_, lean_object* v_adjustResult_7491_, lean_object* v_aa_7492_, lean_object* v_n_7493_, lean_object* v_j_7494_, lean_object* v_a_7495_, lean_object* v_a_7496_){
_start:
{
lean_object* v___x_7497_; 
v___x_7497_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(v_n_7489_, v_adjustResult_7491_, v_aa_7492_, v_n_7493_, v_j_7494_, v_a_7496_);
return v___x_7497_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___boxed(lean_object* v_00_u03b2_7498_, lean_object* v_n_7499_, lean_object* v_00_u03b1_7500_, lean_object* v_adjustResult_7501_, lean_object* v_aa_7502_, lean_object* v_n_7503_, lean_object* v_j_7504_, lean_object* v_a_7505_, lean_object* v_a_7506_){
_start:
{
lean_object* v_res_7507_; 
v_res_7507_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2(v_00_u03b2_7498_, v_n_7499_, v_00_u03b1_7500_, v_adjustResult_7501_, v_aa_7502_, v_n_7503_, v_j_7504_, v_a_7505_, v_a_7506_);
lean_dec(v_j_7504_);
lean_dec(v_n_7503_);
lean_dec_ref(v_aa_7502_);
lean_dec(v_n_7499_);
return v_res_7507_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_7508_, lean_object* v_n_7509_, lean_object* v_00_u03b1_7510_, lean_object* v_aa_7511_, lean_object* v_adjustResult_7512_, lean_object* v_n_7513_, lean_object* v_j_7514_, lean_object* v_a_7515_, lean_object* v_a_7516_){
_start:
{
lean_object* v___x_7517_; 
v___x_7517_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7509_, v_aa_7511_, v_adjustResult_7512_, v_n_7513_, v_j_7514_, v_a_7516_);
return v___x_7517_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b2_7518_, lean_object* v_n_7519_, lean_object* v_00_u03b1_7520_, lean_object* v_aa_7521_, lean_object* v_adjustResult_7522_, lean_object* v_n_7523_, lean_object* v_j_7524_, lean_object* v_a_7525_, lean_object* v_a_7526_){
_start:
{
lean_object* v_res_7527_; 
v_res_7527_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3(v_00_u03b2_7518_, v_n_7519_, v_00_u03b1_7520_, v_aa_7521_, v_adjustResult_7522_, v_n_7523_, v_j_7524_, v_a_7525_, v_a_7526_);
lean_dec(v_n_7523_);
lean_dec_ref(v_aa_7521_);
lean_dec(v_n_7519_);
return v_res_7527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg___lam__0(lean_object* v_x_7528_, lean_object* v_v_7529_){
_start:
{
lean_inc(v_v_7529_);
return v_v_7529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg___lam__0___boxed(lean_object* v_x_7530_, lean_object* v_v_7531_){
_start:
{
lean_object* v_res_7532_; 
v_res_7532_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg___lam__0(v_x_7530_, v_v_7531_);
lean_dec(v_v_7531_);
lean_dec(v_x_7530_);
return v_res_7532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg(lean_object* v_ref_7534_, lean_object* v_addEntry_7535_, lean_object* v_droppedKeys_7536_, lean_object* v_constantsPerTask_7537_, lean_object* v_droppedEntriesRef_7538_, lean_object* v_ty_7539_, lean_object* v_a_7540_, lean_object* v_a_7541_, lean_object* v_a_7542_, lean_object* v_a_7543_){
_start:
{
lean_object* v___x_7545_; 
lean_inc(v_droppedEntriesRef_7538_);
lean_inc(v_droppedKeys_7536_);
lean_inc_ref(v_addEntry_7535_);
v___x_7545_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v_addEntry_7535_, v_droppedKeys_7536_, v_droppedEntriesRef_7538_, v_a_7540_, v_a_7541_, v_a_7542_, v_a_7543_);
if (lean_obj_tag(v___x_7545_) == 0)
{
lean_object* v_a_7546_; lean_object* v___f_7547_; lean_object* v___x_7548_; 
v_a_7546_ = lean_ctor_get(v___x_7545_, 0);
lean_inc(v_a_7546_);
lean_dec_ref_known(v___x_7545_, 1);
v___f_7547_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_findMatches___redArg___closed__0));
v___x_7548_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_a_7546_, v_ref_7534_, v_addEntry_7535_, v_droppedKeys_7536_, v_constantsPerTask_7537_, v_droppedEntriesRef_7538_, v___f_7547_, v_ty_7539_, v_a_7540_, v_a_7541_, v_a_7542_, v_a_7543_);
return v___x_7548_;
}
else
{
lean_object* v_a_7549_; lean_object* v___x_7551_; uint8_t v_isShared_7552_; uint8_t v_isSharedCheck_7556_; 
lean_dec_ref(v_ty_7539_);
lean_dec(v_droppedEntriesRef_7538_);
lean_dec(v_constantsPerTask_7537_);
lean_dec(v_droppedKeys_7536_);
lean_dec_ref(v_addEntry_7535_);
v_a_7549_ = lean_ctor_get(v___x_7545_, 0);
v_isSharedCheck_7556_ = !lean_is_exclusive(v___x_7545_);
if (v_isSharedCheck_7556_ == 0)
{
v___x_7551_ = v___x_7545_;
v_isShared_7552_ = v_isSharedCheck_7556_;
goto v_resetjp_7550_;
}
else
{
lean_inc(v_a_7549_);
lean_dec(v___x_7545_);
v___x_7551_ = lean_box(0);
v_isShared_7552_ = v_isSharedCheck_7556_;
goto v_resetjp_7550_;
}
v_resetjp_7550_:
{
lean_object* v___x_7554_; 
if (v_isShared_7552_ == 0)
{
v___x_7554_ = v___x_7551_;
goto v_reusejp_7553_;
}
else
{
lean_object* v_reuseFailAlloc_7555_; 
v_reuseFailAlloc_7555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7555_, 0, v_a_7549_);
v___x_7554_ = v_reuseFailAlloc_7555_;
goto v_reusejp_7553_;
}
v_reusejp_7553_:
{
return v___x_7554_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg___boxed(lean_object* v_ref_7557_, lean_object* v_addEntry_7558_, lean_object* v_droppedKeys_7559_, lean_object* v_constantsPerTask_7560_, lean_object* v_droppedEntriesRef_7561_, lean_object* v_ty_7562_, lean_object* v_a_7563_, lean_object* v_a_7564_, lean_object* v_a_7565_, lean_object* v_a_7566_, lean_object* v_a_7567_){
_start:
{
lean_object* v_res_7568_; 
v_res_7568_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg(v_ref_7557_, v_addEntry_7558_, v_droppedKeys_7559_, v_constantsPerTask_7560_, v_droppedEntriesRef_7561_, v_ty_7562_, v_a_7563_, v_a_7564_, v_a_7565_, v_a_7566_);
lean_dec(v_a_7566_);
lean_dec_ref(v_a_7565_);
lean_dec(v_a_7564_);
lean_dec_ref(v_a_7563_);
lean_dec(v_ref_7557_);
return v_res_7568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches(lean_object* v_00_u03b1_7569_, lean_object* v_ref_7570_, lean_object* v_addEntry_7571_, lean_object* v_droppedKeys_7572_, lean_object* v_constantsPerTask_7573_, lean_object* v_droppedEntriesRef_7574_, lean_object* v_ty_7575_, lean_object* v_a_7576_, lean_object* v_a_7577_, lean_object* v_a_7578_, lean_object* v_a_7579_){
_start:
{
lean_object* v___x_7581_; 
v___x_7581_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg(v_ref_7570_, v_addEntry_7571_, v_droppedKeys_7572_, v_constantsPerTask_7573_, v_droppedEntriesRef_7574_, v_ty_7575_, v_a_7576_, v_a_7577_, v_a_7578_, v_a_7579_);
return v___x_7581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___boxed(lean_object* v_00_u03b1_7582_, lean_object* v_ref_7583_, lean_object* v_addEntry_7584_, lean_object* v_droppedKeys_7585_, lean_object* v_constantsPerTask_7586_, lean_object* v_droppedEntriesRef_7587_, lean_object* v_ty_7588_, lean_object* v_a_7589_, lean_object* v_a_7590_, lean_object* v_a_7591_, lean_object* v_a_7592_, lean_object* v_a_7593_){
_start:
{
lean_object* v_res_7594_; 
v_res_7594_ = l_Lean_Meta_LazyDiscrTree_findMatches(v_00_u03b1_7582_, v_ref_7583_, v_addEntry_7584_, v_droppedKeys_7585_, v_constantsPerTask_7586_, v_droppedEntriesRef_7587_, v_ty_7588_, v_a_7589_, v_a_7590_, v_a_7591_, v_a_7592_);
lean_dec(v_a_7592_);
lean_dec_ref(v_a_7591_);
lean_dec(v_a_7590_);
lean_dec_ref(v_a_7589_);
lean_dec(v_ref_7583_);
return v_res_7594_;
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
