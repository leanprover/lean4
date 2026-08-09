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
lean_object* v_fName_465_; uint8_t v___y_467_; uint8_t v___y_480_; lean_object* v___x_488_; uint8_t v___x_489_; 
v_fName_465_ = l_Lean_Expr_constName_x21(v_f_463_);
lean_dec_ref(v_f_463_);
v___x_488_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__7));
v___x_489_ = lean_name_eq(v_fName_465_, v___x_488_);
if (v___x_489_ == 0)
{
v___y_480_ = v___x_489_;
goto v___jp_479_;
}
else
{
lean_object* v___x_490_; lean_object* v___x_491_; uint8_t v___x_492_; 
v___x_490_ = l_Lean_Expr_getAppNumArgs(v_e_460_);
v___x_491_ = lean_unsigned_to_nat(1u);
v___x_492_ = lean_nat_dec_eq(v___x_490_, v___x_491_);
lean_dec(v___x_490_);
v___y_480_ = v___x_492_;
goto v___jp_479_;
}
v___jp_466_:
{
if (v___y_467_ == 0)
{
lean_object* v___x_468_; uint8_t v___x_469_; 
v___x_468_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__2));
v___x_469_ = lean_name_eq(v_fName_465_, v___x_468_);
lean_dec(v_fName_465_);
if (v___x_469_ == 0)
{
lean_dec_ref(v_e_460_);
if (v___x_469_ == 0)
{
return v___x_469_;
}
else
{
return v___x_462_;
}
}
else
{
lean_object* v___x_470_; lean_object* v___x_471_; uint8_t v___x_472_; 
v___x_470_ = l_Lean_Expr_getAppNumArgs(v_e_460_);
lean_dec_ref(v_e_460_);
v___x_471_ = lean_unsigned_to_nat(0u);
v___x_472_ = lean_nat_dec_eq(v___x_470_, v___x_471_);
lean_dec(v___x_470_);
if (v___x_472_ == 0)
{
return v___x_472_;
}
else
{
return v___x_462_;
}
}
}
else
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
lean_dec(v_fName_465_);
v___x_473_ = lean_unsigned_to_nat(1u);
v___x_474_ = l_Lean_Expr_getAppNumArgs(v_e_460_);
v___x_475_ = lean_nat_sub(v___x_474_, v___x_473_);
lean_dec(v___x_474_);
v___x_476_ = lean_nat_sub(v___x_475_, v___x_473_);
lean_dec(v___x_475_);
v___x_477_ = l_Lean_Expr_getRevArg_x21(v_e_460_, v___x_476_);
lean_dec_ref(v_e_460_);
v_e_460_ = v___x_477_;
goto _start;
}
}
v___jp_479_:
{
if (v___y_480_ == 0)
{
lean_object* v___x_481_; uint8_t v___x_482_; 
v___x_481_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__5));
v___x_482_ = lean_name_eq(v_fName_465_, v___x_481_);
if (v___x_482_ == 0)
{
v___y_467_ = v___x_482_;
goto v___jp_466_;
}
else
{
lean_object* v___x_483_; lean_object* v___x_484_; uint8_t v___x_485_; 
v___x_483_ = l_Lean_Expr_getAppNumArgs(v_e_460_);
v___x_484_ = lean_unsigned_to_nat(3u);
v___x_485_ = lean_nat_dec_eq(v___x_483_, v___x_484_);
lean_dec(v___x_483_);
v___y_467_ = v___x_485_;
goto v___jp_466_;
}
}
else
{
lean_object* v___x_486_; 
lean_dec(v_fName_465_);
v___x_486_ = l_Lean_Expr_appArg_x21(v_e_460_);
lean_dec_ref(v_e_460_);
v_e_460_ = v___x_486_;
goto _start;
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
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___boxed(lean_object* v_e_493_){
_start:
{
uint8_t v_res_494_; lean_object* v_r_495_; 
v_res_494_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral(v_e_493_);
v_r_495_ = lean_box(v_res_494_);
return v_r_495_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f_loop(lean_object* v_e_498_){
_start:
{
uint8_t v___y_500_; lean_object* v_f_503_; 
v_f_503_ = l_Lean_Expr_getAppFn(v_e_498_);
switch(lean_obj_tag(v_f_503_))
{
case 9:
{
lean_object* v_a_504_; 
lean_dec_ref(v_e_498_);
v_a_504_ = lean_ctor_get(v_f_503_, 0);
lean_inc_ref(v_a_504_);
lean_dec_ref_known(v_f_503_, 1);
if (lean_obj_tag(v_a_504_) == 0)
{
lean_object* v_val_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_512_; 
v_val_505_ = lean_ctor_get(v_a_504_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v_a_504_);
if (v_isSharedCheck_512_ == 0)
{
v___x_507_ = v_a_504_;
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_val_505_);
lean_dec(v_a_504_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_510_; 
if (v_isShared_508_ == 0)
{
lean_ctor_set_tag(v___x_507_, 1);
v___x_510_ = v___x_507_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_val_505_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
else
{
lean_object* v___x_513_; 
lean_dec_ref(v_a_504_);
v___x_513_ = lean_box(0);
return v___x_513_;
}
}
case 4:
{
lean_object* v_declName_514_; uint8_t v___y_516_; uint8_t v___y_529_; lean_object* v___x_547_; uint8_t v___x_548_; 
v_declName_514_ = lean_ctor_get(v_f_503_, 0);
lean_inc(v_declName_514_);
lean_dec_ref_known(v_f_503_, 2);
v___x_547_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__7));
v___x_548_ = lean_name_eq(v_declName_514_, v___x_547_);
if (v___x_548_ == 0)
{
v___y_529_ = v___x_548_;
goto v___jp_528_;
}
else
{
lean_object* v___x_549_; lean_object* v___x_550_; uint8_t v___x_551_; 
v___x_549_ = l_Lean_Expr_getAppNumArgs(v_e_498_);
v___x_550_ = lean_unsigned_to_nat(1u);
v___x_551_ = lean_nat_dec_eq(v___x_549_, v___x_550_);
lean_dec(v___x_549_);
v___y_529_ = v___x_551_;
goto v___jp_528_;
}
v___jp_515_:
{
if (v___y_516_ == 0)
{
lean_object* v___x_517_; uint8_t v___x_518_; 
v___x_517_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__2));
v___x_518_ = lean_name_eq(v_declName_514_, v___x_517_);
lean_dec(v_declName_514_);
if (v___x_518_ == 0)
{
lean_dec_ref(v_e_498_);
v___y_500_ = v___x_518_;
goto v___jp_499_;
}
else
{
lean_object* v___x_519_; lean_object* v___x_520_; uint8_t v___x_521_; 
v___x_519_ = l_Lean_Expr_getAppNumArgs(v_e_498_);
lean_dec_ref(v_e_498_);
v___x_520_ = lean_unsigned_to_nat(0u);
v___x_521_ = lean_nat_dec_eq(v___x_519_, v___x_520_);
lean_dec(v___x_519_);
v___y_500_ = v___x_521_;
goto v___jp_499_;
}
}
else
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
lean_dec(v_declName_514_);
v___x_522_ = lean_unsigned_to_nat(1u);
v___x_523_ = l_Lean_Expr_getAppNumArgs(v_e_498_);
v___x_524_ = lean_nat_sub(v___x_523_, v___x_522_);
lean_dec(v___x_523_);
v___x_525_ = lean_nat_sub(v___x_524_, v___x_522_);
lean_dec(v___x_524_);
v___x_526_ = l_Lean_Expr_getRevArg_x21(v_e_498_, v___x_525_);
lean_dec_ref(v_e_498_);
v_e_498_ = v___x_526_;
goto _start;
}
}
v___jp_528_:
{
if (v___y_529_ == 0)
{
lean_object* v___x_530_; uint8_t v___x_531_; 
v___x_530_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__5));
v___x_531_ = lean_name_eq(v_declName_514_, v___x_530_);
if (v___x_531_ == 0)
{
v___y_516_ = v___x_531_;
goto v___jp_515_;
}
else
{
lean_object* v___x_532_; lean_object* v___x_533_; uint8_t v___x_534_; 
v___x_532_ = l_Lean_Expr_getAppNumArgs(v_e_498_);
v___x_533_ = lean_unsigned_to_nat(3u);
v___x_534_ = lean_nat_dec_eq(v___x_532_, v___x_533_);
lean_dec(v___x_532_);
v___y_516_ = v___x_534_;
goto v___jp_515_;
}
}
else
{
lean_object* v___x_535_; lean_object* v___x_536_; 
lean_dec(v_declName_514_);
v___x_535_ = l_Lean_Expr_appArg_x21(v_e_498_);
lean_dec_ref(v_e_498_);
v___x_536_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f_loop(v___x_535_);
if (lean_obj_tag(v___x_536_) == 0)
{
return v___x_536_;
}
else
{
lean_object* v_val_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_546_; 
v_val_537_ = lean_ctor_get(v___x_536_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_546_ == 0)
{
v___x_539_ = v___x_536_;
v_isShared_540_ = v_isSharedCheck_546_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_val_537_);
lean_dec(v___x_536_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_546_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_544_; 
v___x_541_ = lean_unsigned_to_nat(1u);
v___x_542_ = lean_nat_add(v_val_537_, v___x_541_);
lean_dec(v_val_537_);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 0, v___x_542_);
v___x_544_ = v___x_539_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v___x_542_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_552_; 
lean_dec_ref(v_f_503_);
lean_dec_ref(v_e_498_);
v___x_552_ = lean_box(0);
return v___x_552_;
}
}
v___jp_499_:
{
if (v___y_500_ == 0)
{
lean_object* v___x_501_; 
v___x_501_ = lean_box(0);
return v___x_501_;
}
else
{
lean_object* v___x_502_; 
v___x_502_ = ((lean_object*)(l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f_loop___closed__0));
return v___x_502_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f(lean_object* v_e_553_){
_start:
{
uint8_t v___x_554_; 
lean_inc_ref(v_e_553_);
v___x_554_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral(v_e_553_);
if (v___x_554_ == 0)
{
lean_object* v___x_555_; 
lean_dec_ref(v_e_553_);
v___x_555_ = lean_box(0);
return v___x_555_;
}
else
{
lean_object* v___x_556_; 
v___x_556_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f_loop(v_e_553_);
if (lean_obj_tag(v___x_556_) == 1)
{
lean_object* v_val_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_565_; 
v_val_557_ = lean_ctor_get(v___x_556_, 0);
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_565_ == 0)
{
v___x_559_ = v___x_556_;
v_isShared_560_ = v_isSharedCheck_565_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_val_557_);
lean_dec(v___x_556_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_565_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_561_; lean_object* v___x_563_; 
v___x_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_561_, 0, v_val_557_);
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 0, v___x_561_);
v___x_563_ = v___x_559_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v___x_561_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
}
else
{
lean_object* v___x_566_; 
lean_dec(v___x_556_);
v___x_566_ = lean_box(0);
return v___x_566_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNatType(lean_object* v_e_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_){
_start:
{
lean_object* v___x_575_; 
lean_inc(v_a_573_);
lean_inc_ref(v_a_572_);
lean_inc(v_a_571_);
lean_inc_ref(v_a_570_);
v___x_575_ = lean_whnf(v_e_569_, v_a_570_, v_a_571_, v_a_572_, v_a_573_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v_a_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_586_; 
v_a_576_ = lean_ctor_get(v___x_575_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_586_ == 0)
{
v___x_578_ = v___x_575_;
v_isShared_579_ = v_isSharedCheck_586_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_a_576_);
lean_dec(v___x_575_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_586_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_580_; uint8_t v___x_581_; lean_object* v___x_582_; lean_object* v___x_584_; 
v___x_580_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNatType___closed__0));
v___x_581_ = l_Lean_Expr_isConstOf(v_a_576_, v___x_580_);
lean_dec(v_a_576_);
v___x_582_ = lean_box(v___x_581_);
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 0, v___x_582_);
v___x_584_ = v___x_578_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v___x_582_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
}
else
{
lean_object* v_a_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_594_; 
v_a_587_ = lean_ctor_get(v___x_575_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_594_ == 0)
{
v___x_589_ = v___x_575_;
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_a_587_);
lean_dec(v___x_575_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_592_; 
if (v_isShared_590_ == 0)
{
v___x_592_ = v___x_589_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_a_587_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNatType___boxed(lean_object* v_e_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNatType(v_e_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_);
lean_dec(v_a_599_);
lean_dec_ref(v_a_598_);
lean_dec(v_a_597_);
lean_dec_ref(v_a_596_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset(lean_object* v_fName_615_, lean_object* v_e_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_){
_start:
{
uint8_t v___y_623_; uint8_t v___y_653_; uint8_t v___y_678_; lean_object* v___x_688_; uint8_t v___x_689_; 
v___x_688_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___closed__6));
v___x_689_ = lean_name_eq(v_fName_615_, v___x_688_);
if (v___x_689_ == 0)
{
v___y_678_ = v___x_689_;
goto v___jp_677_;
}
else
{
lean_object* v___x_690_; lean_object* v___x_691_; uint8_t v___x_692_; 
v___x_690_ = l_Lean_Expr_getAppNumArgs(v_e_616_);
v___x_691_ = lean_unsigned_to_nat(2u);
v___x_692_ = lean_nat_dec_eq(v___x_690_, v___x_691_);
lean_dec(v___x_690_);
v___y_678_ = v___x_692_;
goto v___jp_677_;
}
v___jp_622_:
{
if (v___y_623_ == 0)
{
lean_object* v___x_624_; uint8_t v___x_625_; 
v___x_624_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__7));
v___x_625_ = lean_name_eq(v_fName_615_, v___x_624_);
if (v___x_625_ == 0)
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = lean_box(v___x_625_);
v___x_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
return v___x_627_;
}
else
{
lean_object* v___x_628_; lean_object* v___x_629_; uint8_t v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_628_ = l_Lean_Expr_getAppNumArgs(v_e_616_);
v___x_629_ = lean_unsigned_to_nat(1u);
v___x_630_ = lean_nat_dec_eq(v___x_628_, v___x_629_);
lean_dec(v___x_628_);
v___x_631_ = lean_box(v___x_630_);
v___x_632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_632_, 0, v___x_631_);
return v___x_632_;
}
}
else
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_633_ = lean_unsigned_to_nat(1u);
v___x_634_ = l_Lean_Expr_getAppNumArgs(v_e_616_);
v___x_635_ = lean_nat_sub(v___x_634_, v___x_633_);
lean_dec(v___x_634_);
v___x_636_ = lean_nat_sub(v___x_635_, v___x_633_);
lean_dec(v___x_635_);
v___x_637_ = l_Lean_Expr_getRevArg_x21(v_e_616_, v___x_636_);
v___x_638_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNatType(v___x_637_, v_a_617_, v_a_618_, v_a_619_, v_a_620_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v_a_639_; uint8_t v___x_640_; 
v_a_639_ = lean_ctor_get(v___x_638_, 0);
lean_inc(v_a_639_);
v___x_640_ = lean_unbox(v_a_639_);
lean_dec(v_a_639_);
if (v___x_640_ == 0)
{
return v___x_638_;
}
else
{
lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_650_; 
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_650_ == 0)
{
lean_object* v_unused_651_; 
v_unused_651_ = lean_ctor_get(v___x_638_, 0);
lean_dec(v_unused_651_);
v___x_642_ = v___x_638_;
v_isShared_643_ = v_isSharedCheck_650_;
goto v_resetjp_641_;
}
else
{
lean_dec(v___x_638_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_650_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_644_; uint8_t v___x_645_; lean_object* v___x_646_; lean_object* v___x_648_; 
v___x_644_ = l_Lean_Expr_appArg_x21(v_e_616_);
v___x_645_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral(v___x_644_);
v___x_646_ = lean_box(v___x_645_);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 0, v___x_646_);
v___x_648_ = v___x_642_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v___x_646_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
else
{
return v___x_638_;
}
}
}
v___jp_652_:
{
if (v___y_653_ == 0)
{
lean_object* v___x_654_; uint8_t v___x_655_; 
v___x_654_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___closed__2));
v___x_655_ = lean_name_eq(v_fName_615_, v___x_654_);
if (v___x_655_ == 0)
{
v___y_623_ = v___x_655_;
goto v___jp_622_;
}
else
{
lean_object* v___x_656_; lean_object* v___x_657_; uint8_t v___x_658_; 
v___x_656_ = l_Lean_Expr_getAppNumArgs(v_e_616_);
v___x_657_ = lean_unsigned_to_nat(6u);
v___x_658_ = lean_nat_dec_eq(v___x_656_, v___x_657_);
lean_dec(v___x_656_);
v___y_623_ = v___x_658_;
goto v___jp_622_;
}
}
else
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_659_ = l_Lean_Expr_getAppNumArgs(v_e_616_);
v___x_660_ = lean_unsigned_to_nat(1u);
v___x_661_ = lean_nat_sub(v___x_659_, v___x_660_);
lean_dec(v___x_659_);
v___x_662_ = l_Lean_Expr_getRevArg_x21(v_e_616_, v___x_661_);
v___x_663_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNatType(v___x_662_, v_a_617_, v_a_618_, v_a_619_, v_a_620_);
if (lean_obj_tag(v___x_663_) == 0)
{
lean_object* v_a_664_; uint8_t v___x_665_; 
v_a_664_ = lean_ctor_get(v___x_663_, 0);
lean_inc(v_a_664_);
v___x_665_ = lean_unbox(v_a_664_);
lean_dec(v_a_664_);
if (v___x_665_ == 0)
{
return v___x_663_;
}
else
{
lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_675_; 
v_isSharedCheck_675_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_675_ == 0)
{
lean_object* v_unused_676_; 
v_unused_676_ = lean_ctor_get(v___x_663_, 0);
lean_dec(v_unused_676_);
v___x_667_ = v___x_663_;
v_isShared_668_ = v_isSharedCheck_675_;
goto v_resetjp_666_;
}
else
{
lean_dec(v___x_663_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_675_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_669_; uint8_t v___x_670_; lean_object* v___x_671_; lean_object* v___x_673_; 
v___x_669_ = l_Lean_Expr_appArg_x21(v_e_616_);
v___x_670_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral(v___x_669_);
v___x_671_ = lean_box(v___x_670_);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v___x_671_);
v___x_673_ = v___x_667_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v___x_671_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
}
else
{
return v___x_663_;
}
}
}
v___jp_677_:
{
if (v___y_678_ == 0)
{
lean_object* v___x_679_; uint8_t v___x_680_; 
v___x_679_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___closed__5));
v___x_680_ = lean_name_eq(v_fName_615_, v___x_679_);
if (v___x_680_ == 0)
{
v___y_653_ = v___x_680_;
goto v___jp_652_;
}
else
{
lean_object* v___x_681_; lean_object* v___x_682_; uint8_t v___x_683_; 
v___x_681_ = l_Lean_Expr_getAppNumArgs(v_e_616_);
v___x_682_ = lean_unsigned_to_nat(4u);
v___x_683_ = lean_nat_dec_eq(v___x_681_, v___x_682_);
lean_dec(v___x_681_);
v___y_653_ = v___x_683_;
goto v___jp_652_;
}
}
else
{
lean_object* v___x_684_; uint8_t v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_684_ = l_Lean_Expr_appArg_x21(v_e_616_);
v___x_685_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral(v___x_684_);
v___x_686_ = lean_box(v___x_685_);
v___x_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
return v___x_687_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___boxed(lean_object* v_fName_693_, lean_object* v_e_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset(v_fName_693_, v_e_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_);
lean_dec(v_a_698_);
lean_dec_ref(v_a_697_);
lean_dec(v_a_696_);
lean_dec_ref(v_a_695_);
lean_dec_ref(v_e_694_);
lean_dec(v_fName_693_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_shouldAddAsStar(lean_object* v_fName_701_, lean_object* v_e_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset(v_fName_701_, v_e_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_shouldAddAsStar___boxed(lean_object* v_fName_709_, lean_object* v_e_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_Lean_Meta_LazyDiscrTree_MatchClone_shouldAddAsStar(v_fName_709_, v_e_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_);
lean_dec(v_a_714_);
lean_dec_ref(v_a_713_);
lean_dec(v_a_712_);
lean_dec_ref(v_a_711_);
lean_dec_ref(v_e_710_);
lean_dec(v_fName_709_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__0(lean_object* v_e_719_, lean_object* v___y_720_, lean_object* v___y_721_){
_start:
{
uint8_t v___x_723_; 
v___x_723_ = l_Lean_Expr_hasLooseBVars(v_e_719_);
if (v___x_723_ == 0)
{
lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_724_, 0, v_e_719_);
v___x_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_725_, 0, v___x_724_);
return v___x_725_;
}
else
{
uint8_t v___x_726_; uint8_t v___x_727_; 
v___x_726_ = 0;
v___x_727_ = l_Lean_Expr_isHeadBetaTarget(v_e_719_, v___x_726_);
if (v___x_727_ == 0)
{
lean_object* v___x_728_; lean_object* v___x_729_; 
lean_dec_ref(v_e_719_);
v___x_728_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__0___closed__0));
v___x_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_729_, 0, v___x_728_);
return v___x_729_;
}
else
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_730_ = l_Lean_Expr_headBeta(v_e_719_);
v___x_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
v___x_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_732_, 0, v___x_731_);
return v___x_732_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__0___boxed(lean_object* v_e_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__0(v_e_733_, v___y_734_, v___y_735_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__1(lean_object* v_e_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_742_, 0, v_e_738_);
v___x_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_743_, 0, v___x_742_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__1___boxed(lean_object* v_e_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__1(v_e_744_, v___y_745_, v___y_746_);
lean_dec(v___y_746_);
lean_dec_ref(v___y_745_);
return v_res_748_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_749_ = lean_box(0);
v___x_750_ = l_Lean_interruptExceptionId;
v___x_751_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_751_, 0, v___x_750_);
lean_ctor_set(v___x_751_, 1, v___x_749_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg(){
_start:
{
lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_753_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg___closed__0);
v___x_754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg___boxed(lean_object* v___y_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg();
return v_res_756_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_762_ = l_Lean_maxRecDepthErrorMessage;
v___x_763_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_763_, 0, v___x_762_);
return v___x_763_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_764_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__3);
v___x_765_ = l_Lean_MessageData_ofFormat(v___x_764_);
return v___x_765_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_766_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__4);
v___x_767_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__2));
v___x_768_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_768_, 0, v___x_767_);
lean_ctor_set(v___x_768_, 1, v___x_766_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_ref_769_){
_start:
{
lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_771_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_772_, 0, v_ref_769_);
lean_ctor_set(v___x_772_, 1, v___x_771_);
v___x_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_773_, 0, v___x_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_ref_774_, lean_object* v___y_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_774_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg(lean_object* v_x_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_){
_start:
{
lean_object* v___y_783_; lean_object* v___y_793_; lean_object* v___y_794_; lean_object* v___y_795_; lean_object* v___y_796_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v___y_799_; uint8_t v___y_800_; lean_object* v___y_801_; lean_object* v___y_802_; lean_object* v___y_803_; lean_object* v___y_804_; uint8_t v___y_805_; lean_object* v___y_806_; lean_object* v___y_807_; lean_object* v___y_808_; lean_object* v_fileName_813_; lean_object* v_fileMap_814_; lean_object* v_options_815_; lean_object* v_currRecDepth_816_; lean_object* v_maxRecDepth_817_; lean_object* v_ref_818_; lean_object* v_currNamespace_819_; lean_object* v_openDecls_820_; lean_object* v_initHeartbeats_821_; lean_object* v_maxHeartbeats_822_; lean_object* v_quotContext_823_; lean_object* v_currMacroScope_824_; uint8_t v_diag_825_; lean_object* v_cancelTk_x3f_826_; uint8_t v_suppressElabErrors_827_; lean_object* v_inheritedTraceOptions_828_; 
v_fileName_813_ = lean_ctor_get(v___y_779_, 0);
v_fileMap_814_ = lean_ctor_get(v___y_779_, 1);
v_options_815_ = lean_ctor_get(v___y_779_, 2);
v_currRecDepth_816_ = lean_ctor_get(v___y_779_, 3);
v_maxRecDepth_817_ = lean_ctor_get(v___y_779_, 4);
v_ref_818_ = lean_ctor_get(v___y_779_, 5);
v_currNamespace_819_ = lean_ctor_get(v___y_779_, 6);
v_openDecls_820_ = lean_ctor_get(v___y_779_, 7);
v_initHeartbeats_821_ = lean_ctor_get(v___y_779_, 8);
v_maxHeartbeats_822_ = lean_ctor_get(v___y_779_, 9);
v_quotContext_823_ = lean_ctor_get(v___y_779_, 10);
v_currMacroScope_824_ = lean_ctor_get(v___y_779_, 11);
v_diag_825_ = lean_ctor_get_uint8(v___y_779_, sizeof(void*)*14);
v_cancelTk_x3f_826_ = lean_ctor_get(v___y_779_, 12);
v_suppressElabErrors_827_ = lean_ctor_get_uint8(v___y_779_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_828_ = lean_ctor_get(v___y_779_, 13);
if (lean_obj_tag(v_cancelTk_x3f_826_) == 1)
{
lean_object* v_val_834_; uint8_t v___x_835_; 
v_val_834_ = lean_ctor_get(v_cancelTk_x3f_826_, 0);
v___x_835_ = l_IO_CancelToken_isSet(v_val_834_);
if (v___x_835_ == 0)
{
goto v___jp_829_;
}
else
{
lean_object* v___x_836_; lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_844_; 
lean_dec_ref(v_x_777_);
v___x_836_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg();
v_a_837_ = lean_ctor_get(v___x_836_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_844_ == 0)
{
v___x_839_ = v___x_836_;
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_dec(v___x_836_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_842_; 
if (v_isShared_840_ == 0)
{
v___x_842_ = v___x_839_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_a_837_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
}
else
{
goto v___jp_829_;
}
v___jp_782_:
{
if (lean_obj_tag(v___y_783_) == 0)
{
return v___y_783_;
}
else
{
lean_object* v_a_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_791_; 
v_a_784_ = lean_ctor_get(v___y_783_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___y_783_);
if (v_isSharedCheck_791_ == 0)
{
v___x_786_ = v___y_783_;
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_a_784_);
lean_dec(v___y_783_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_789_; 
if (v_isShared_787_ == 0)
{
v___x_789_ = v___x_786_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_a_784_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
}
v___jp_792_:
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_809_ = lean_unsigned_to_nat(1u);
v___x_810_ = lean_nat_add(v___y_797_, v___x_809_);
lean_inc_ref(v___y_804_);
lean_inc(v___y_808_);
lean_inc(v___y_793_);
lean_inc(v___y_802_);
lean_inc(v___y_799_);
lean_inc(v___y_798_);
lean_inc(v___y_795_);
lean_inc(v___y_794_);
lean_inc(v___y_796_);
lean_inc_ref(v___y_807_);
lean_inc_ref(v___y_806_);
lean_inc_ref(v___y_801_);
v___x_811_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_811_, 0, v___y_801_);
lean_ctor_set(v___x_811_, 1, v___y_806_);
lean_ctor_set(v___x_811_, 2, v___y_807_);
lean_ctor_set(v___x_811_, 3, v___x_810_);
lean_ctor_set(v___x_811_, 4, v___y_796_);
lean_ctor_set(v___x_811_, 5, v___y_803_);
lean_ctor_set(v___x_811_, 6, v___y_794_);
lean_ctor_set(v___x_811_, 7, v___y_795_);
lean_ctor_set(v___x_811_, 8, v___y_798_);
lean_ctor_set(v___x_811_, 9, v___y_799_);
lean_ctor_set(v___x_811_, 10, v___y_802_);
lean_ctor_set(v___x_811_, 11, v___y_793_);
lean_ctor_set(v___x_811_, 12, v___y_808_);
lean_ctor_set(v___x_811_, 13, v___y_804_);
lean_ctor_set_uint8(v___x_811_, sizeof(void*)*14, v___y_800_);
lean_ctor_set_uint8(v___x_811_, sizeof(void*)*14 + 1, v___y_805_);
lean_inc(v___y_780_);
lean_inc(v___y_778_);
v___x_812_ = lean_apply_4(v_x_777_, v___y_778_, v___x_811_, v___y_780_, lean_box(0));
v___y_783_ = v___x_812_;
goto v___jp_782_;
}
v___jp_829_:
{
lean_object* v___x_830_; uint8_t v___x_831_; 
v___x_830_ = lean_unsigned_to_nat(0u);
v___x_831_ = lean_nat_dec_eq(v_maxRecDepth_817_, v___x_830_);
if (v___x_831_ == 0)
{
uint8_t v___x_832_; 
v___x_832_ = lean_nat_dec_eq(v_currRecDepth_816_, v_maxRecDepth_817_);
if (v___x_832_ == 0)
{
lean_inc(v_ref_818_);
v___y_793_ = v_currMacroScope_824_;
v___y_794_ = v_currNamespace_819_;
v___y_795_ = v_openDecls_820_;
v___y_796_ = v_maxRecDepth_817_;
v___y_797_ = v_currRecDepth_816_;
v___y_798_ = v_initHeartbeats_821_;
v___y_799_ = v_maxHeartbeats_822_;
v___y_800_ = v_diag_825_;
v___y_801_ = v_fileName_813_;
v___y_802_ = v_quotContext_823_;
v___y_803_ = v_ref_818_;
v___y_804_ = v_inheritedTraceOptions_828_;
v___y_805_ = v_suppressElabErrors_827_;
v___y_806_ = v_fileMap_814_;
v___y_807_ = v_options_815_;
v___y_808_ = v_cancelTk_x3f_826_;
goto v___jp_792_;
}
else
{
lean_object* v___x_833_; 
lean_dec_ref(v_x_777_);
lean_inc(v_ref_818_);
v___x_833_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_818_);
v___y_783_ = v___x_833_;
goto v___jp_782_;
}
}
else
{
lean_inc(v_ref_818_);
v___y_793_ = v_currMacroScope_824_;
v___y_794_ = v_currNamespace_819_;
v___y_795_ = v_openDecls_820_;
v___y_796_ = v_maxRecDepth_817_;
v___y_797_ = v_currRecDepth_816_;
v___y_798_ = v_initHeartbeats_821_;
v___y_799_ = v_maxHeartbeats_822_;
v___y_800_ = v_diag_825_;
v___y_801_ = v_fileName_813_;
v___y_802_ = v_quotContext_823_;
v___y_803_ = v_ref_818_;
v___y_804_ = v_inheritedTraceOptions_828_;
v___y_805_ = v_suppressElabErrors_827_;
v___y_806_ = v_fileMap_814_;
v___y_807_ = v_options_815_;
v___y_808_ = v_cancelTk_x3f_826_;
goto v___jp_792_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg(v_x_845_, v___y_846_, v___y_847_, v___y_848_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_a_851_, lean_object* v_x_852_){
_start:
{
if (lean_obj_tag(v_x_852_) == 0)
{
lean_object* v___x_853_; 
v___x_853_ = lean_box(0);
return v___x_853_;
}
else
{
lean_object* v_key_854_; lean_object* v_value_855_; lean_object* v_tail_856_; uint8_t v___x_857_; 
v_key_854_ = lean_ctor_get(v_x_852_, 0);
v_value_855_ = lean_ctor_get(v_x_852_, 1);
v_tail_856_ = lean_ctor_get(v_x_852_, 2);
v___x_857_ = l_Lean_ExprStructEq_beq(v_key_854_, v_a_851_);
if (v___x_857_ == 0)
{
v_x_852_ = v_tail_856_;
goto _start;
}
else
{
lean_object* v___x_859_; 
lean_inc(v_value_855_);
v___x_859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_859_, 0, v_value_855_);
return v___x_859_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_a_860_, lean_object* v_x_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg(v_a_860_, v_x_861_);
lean_dec(v_x_861_);
lean_dec_ref(v_a_860_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg(lean_object* v_m_863_, lean_object* v_a_864_){
_start:
{
lean_object* v_buckets_865_; lean_object* v___x_866_; uint64_t v___x_867_; uint64_t v___x_868_; uint64_t v___x_869_; uint64_t v_fold_870_; uint64_t v___x_871_; uint64_t v___x_872_; uint64_t v___x_873_; size_t v___x_874_; size_t v___x_875_; size_t v___x_876_; size_t v___x_877_; size_t v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v_buckets_865_ = lean_ctor_get(v_m_863_, 1);
v___x_866_ = lean_array_get_size(v_buckets_865_);
v___x_867_ = l_Lean_ExprStructEq_hash(v_a_864_);
v___x_868_ = 32ULL;
v___x_869_ = lean_uint64_shift_right(v___x_867_, v___x_868_);
v_fold_870_ = lean_uint64_xor(v___x_867_, v___x_869_);
v___x_871_ = 16ULL;
v___x_872_ = lean_uint64_shift_right(v_fold_870_, v___x_871_);
v___x_873_ = lean_uint64_xor(v_fold_870_, v___x_872_);
v___x_874_ = lean_uint64_to_usize(v___x_873_);
v___x_875_ = lean_usize_of_nat(v___x_866_);
v___x_876_ = ((size_t)1ULL);
v___x_877_ = lean_usize_sub(v___x_875_, v___x_876_);
v___x_878_ = lean_usize_land(v___x_874_, v___x_877_);
v___x_879_ = lean_array_uget_borrowed(v_buckets_865_, v___x_878_);
v___x_880_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg(v_a_864_, v___x_879_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_m_881_, lean_object* v_a_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg(v_m_881_, v_a_882_);
lean_dec_ref(v_a_882_);
lean_dec_ref(v_m_881_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12___redArg(lean_object* v_a_884_, lean_object* v_b_885_, lean_object* v_x_886_){
_start:
{
if (lean_obj_tag(v_x_886_) == 0)
{
lean_dec(v_b_885_);
lean_dec_ref(v_a_884_);
return v_x_886_;
}
else
{
lean_object* v_key_887_; lean_object* v_value_888_; lean_object* v_tail_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_901_; 
v_key_887_ = lean_ctor_get(v_x_886_, 0);
v_value_888_ = lean_ctor_get(v_x_886_, 1);
v_tail_889_ = lean_ctor_get(v_x_886_, 2);
v_isSharedCheck_901_ = !lean_is_exclusive(v_x_886_);
if (v_isSharedCheck_901_ == 0)
{
v___x_891_ = v_x_886_;
v_isShared_892_ = v_isSharedCheck_901_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_tail_889_);
lean_inc(v_value_888_);
lean_inc(v_key_887_);
lean_dec(v_x_886_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_901_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
uint8_t v___x_893_; 
v___x_893_ = l_Lean_ExprStructEq_beq(v_key_887_, v_a_884_);
if (v___x_893_ == 0)
{
lean_object* v___x_894_; lean_object* v___x_896_; 
v___x_894_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12___redArg(v_a_884_, v_b_885_, v_tail_889_);
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 2, v___x_894_);
v___x_896_ = v___x_891_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_key_887_);
lean_ctor_set(v_reuseFailAlloc_897_, 1, v_value_888_);
lean_ctor_set(v_reuseFailAlloc_897_, 2, v___x_894_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
else
{
lean_object* v___x_899_; 
lean_dec(v_value_888_);
lean_dec(v_key_887_);
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 1, v_b_885_);
lean_ctor_set(v___x_891_, 0, v_a_884_);
v___x_899_ = v___x_891_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_a_884_);
lean_ctor_set(v_reuseFailAlloc_900_, 1, v_b_885_);
lean_ctor_set(v_reuseFailAlloc_900_, 2, v_tail_889_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(lean_object* v_x_902_, lean_object* v_x_903_){
_start:
{
if (lean_obj_tag(v_x_903_) == 0)
{
return v_x_902_;
}
else
{
lean_object* v_key_904_; lean_object* v_value_905_; lean_object* v_tail_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_929_; 
v_key_904_ = lean_ctor_get(v_x_903_, 0);
v_value_905_ = lean_ctor_get(v_x_903_, 1);
v_tail_906_ = lean_ctor_get(v_x_903_, 2);
v_isSharedCheck_929_ = !lean_is_exclusive(v_x_903_);
if (v_isSharedCheck_929_ == 0)
{
v___x_908_ = v_x_903_;
v_isShared_909_ = v_isSharedCheck_929_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_tail_906_);
lean_inc(v_value_905_);
lean_inc(v_key_904_);
lean_dec(v_x_903_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_929_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_910_; uint64_t v___x_911_; uint64_t v___x_912_; uint64_t v___x_913_; uint64_t v_fold_914_; uint64_t v___x_915_; uint64_t v___x_916_; uint64_t v___x_917_; size_t v___x_918_; size_t v___x_919_; size_t v___x_920_; size_t v___x_921_; size_t v___x_922_; lean_object* v___x_923_; lean_object* v___x_925_; 
v___x_910_ = lean_array_get_size(v_x_902_);
v___x_911_ = l_Lean_ExprStructEq_hash(v_key_904_);
v___x_912_ = 32ULL;
v___x_913_ = lean_uint64_shift_right(v___x_911_, v___x_912_);
v_fold_914_ = lean_uint64_xor(v___x_911_, v___x_913_);
v___x_915_ = 16ULL;
v___x_916_ = lean_uint64_shift_right(v_fold_914_, v___x_915_);
v___x_917_ = lean_uint64_xor(v_fold_914_, v___x_916_);
v___x_918_ = lean_uint64_to_usize(v___x_917_);
v___x_919_ = lean_usize_of_nat(v___x_910_);
v___x_920_ = ((size_t)1ULL);
v___x_921_ = lean_usize_sub(v___x_919_, v___x_920_);
v___x_922_ = lean_usize_land(v___x_918_, v___x_921_);
v___x_923_ = lean_array_uget_borrowed(v_x_902_, v___x_922_);
lean_inc(v___x_923_);
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 2, v___x_923_);
v___x_925_ = v___x_908_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_key_904_);
lean_ctor_set(v_reuseFailAlloc_928_, 1, v_value_905_);
lean_ctor_set(v_reuseFailAlloc_928_, 2, v___x_923_);
v___x_925_ = v_reuseFailAlloc_928_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
lean_object* v___x_926_; 
v___x_926_ = lean_array_uset(v_x_902_, v___x_922_, v___x_925_);
v_x_902_ = v___x_926_;
v_x_903_ = v_tail_906_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(lean_object* v_i_930_, lean_object* v_source_931_, lean_object* v_target_932_){
_start:
{
lean_object* v___x_933_; uint8_t v___x_934_; 
v___x_933_ = lean_array_get_size(v_source_931_);
v___x_934_ = lean_nat_dec_lt(v_i_930_, v___x_933_);
if (v___x_934_ == 0)
{
lean_dec_ref(v_source_931_);
lean_dec(v_i_930_);
return v_target_932_;
}
else
{
lean_object* v_es_935_; lean_object* v___x_936_; lean_object* v_source_937_; lean_object* v_target_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v_es_935_ = lean_array_fget(v_source_931_, v_i_930_);
v___x_936_ = lean_box(0);
v_source_937_ = lean_array_fset(v_source_931_, v_i_930_, v___x_936_);
v_target_938_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_target_932_, v_es_935_);
v___x_939_ = lean_unsigned_to_nat(1u);
v___x_940_ = lean_nat_add(v_i_930_, v___x_939_);
lean_dec(v_i_930_);
v_i_930_ = v___x_940_;
v_source_931_ = v_source_937_;
v_target_932_ = v_target_938_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11___redArg(lean_object* v_data_942_){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v_nbuckets_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_943_ = lean_array_get_size(v_data_942_);
v___x_944_ = lean_unsigned_to_nat(2u);
v_nbuckets_945_ = lean_nat_mul(v___x_943_, v___x_944_);
v___x_946_ = lean_unsigned_to_nat(0u);
v___x_947_ = lean_box(0);
v___x_948_ = lean_mk_array(v_nbuckets_945_, v___x_947_);
v___x_949_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v___x_946_, v_data_942_, v___x_948_);
return v___x_949_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(lean_object* v_a_950_, lean_object* v_x_951_){
_start:
{
if (lean_obj_tag(v_x_951_) == 0)
{
uint8_t v___x_952_; 
v___x_952_ = 0;
return v___x_952_;
}
else
{
lean_object* v_key_953_; lean_object* v_tail_954_; uint8_t v___x_955_; 
v_key_953_ = lean_ctor_get(v_x_951_, 0);
v_tail_954_ = lean_ctor_get(v_x_951_, 2);
v___x_955_ = l_Lean_ExprStructEq_beq(v_key_953_, v_a_950_);
if (v___x_955_ == 0)
{
v_x_951_ = v_tail_954_;
goto _start;
}
else
{
return v___x_955_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg___boxed(lean_object* v_a_957_, lean_object* v_x_958_){
_start:
{
uint8_t v_res_959_; lean_object* v_r_960_; 
v_res_959_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(v_a_957_, v_x_958_);
lean_dec(v_x_958_);
lean_dec_ref(v_a_957_);
v_r_960_ = lean_box(v_res_959_);
return v_r_960_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6___redArg(lean_object* v_m_961_, lean_object* v_a_962_, lean_object* v_b_963_){
_start:
{
lean_object* v_size_964_; lean_object* v_buckets_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_1008_; 
v_size_964_ = lean_ctor_get(v_m_961_, 0);
v_buckets_965_ = lean_ctor_get(v_m_961_, 1);
v_isSharedCheck_1008_ = !lean_is_exclusive(v_m_961_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_967_ = v_m_961_;
v_isShared_968_ = v_isSharedCheck_1008_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_buckets_965_);
lean_inc(v_size_964_);
lean_dec(v_m_961_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_1008_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_969_; uint64_t v___x_970_; uint64_t v___x_971_; uint64_t v___x_972_; uint64_t v_fold_973_; uint64_t v___x_974_; uint64_t v___x_975_; uint64_t v___x_976_; size_t v___x_977_; size_t v___x_978_; size_t v___x_979_; size_t v___x_980_; size_t v___x_981_; lean_object* v_bkt_982_; uint8_t v___x_983_; 
v___x_969_ = lean_array_get_size(v_buckets_965_);
v___x_970_ = l_Lean_ExprStructEq_hash(v_a_962_);
v___x_971_ = 32ULL;
v___x_972_ = lean_uint64_shift_right(v___x_970_, v___x_971_);
v_fold_973_ = lean_uint64_xor(v___x_970_, v___x_972_);
v___x_974_ = 16ULL;
v___x_975_ = lean_uint64_shift_right(v_fold_973_, v___x_974_);
v___x_976_ = lean_uint64_xor(v_fold_973_, v___x_975_);
v___x_977_ = lean_uint64_to_usize(v___x_976_);
v___x_978_ = lean_usize_of_nat(v___x_969_);
v___x_979_ = ((size_t)1ULL);
v___x_980_ = lean_usize_sub(v___x_978_, v___x_979_);
v___x_981_ = lean_usize_land(v___x_977_, v___x_980_);
v_bkt_982_ = lean_array_uget_borrowed(v_buckets_965_, v___x_981_);
v___x_983_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(v_a_962_, v_bkt_982_);
if (v___x_983_ == 0)
{
lean_object* v___x_984_; lean_object* v_size_x27_985_; lean_object* v___x_986_; lean_object* v_buckets_x27_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; uint8_t v___x_993_; 
v___x_984_ = lean_unsigned_to_nat(1u);
v_size_x27_985_ = lean_nat_add(v_size_964_, v___x_984_);
lean_dec(v_size_964_);
lean_inc(v_bkt_982_);
v___x_986_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_986_, 0, v_a_962_);
lean_ctor_set(v___x_986_, 1, v_b_963_);
lean_ctor_set(v___x_986_, 2, v_bkt_982_);
v_buckets_x27_987_ = lean_array_uset(v_buckets_965_, v___x_981_, v___x_986_);
v___x_988_ = lean_unsigned_to_nat(4u);
v___x_989_ = lean_nat_mul(v_size_x27_985_, v___x_988_);
v___x_990_ = lean_unsigned_to_nat(3u);
v___x_991_ = lean_nat_div(v___x_989_, v___x_990_);
lean_dec(v___x_989_);
v___x_992_ = lean_array_get_size(v_buckets_x27_987_);
v___x_993_ = lean_nat_dec_le(v___x_991_, v___x_992_);
lean_dec(v___x_991_);
if (v___x_993_ == 0)
{
lean_object* v_val_994_; lean_object* v___x_996_; 
v_val_994_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11___redArg(v_buckets_x27_987_);
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 1, v_val_994_);
lean_ctor_set(v___x_967_, 0, v_size_x27_985_);
v___x_996_ = v___x_967_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_size_x27_985_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v_val_994_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
else
{
lean_object* v___x_999_; 
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 1, v_buckets_x27_987_);
lean_ctor_set(v___x_967_, 0, v_size_x27_985_);
v___x_999_ = v___x_967_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_size_x27_985_);
lean_ctor_set(v_reuseFailAlloc_1000_, 1, v_buckets_x27_987_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
else
{
lean_object* v___x_1001_; lean_object* v_buckets_x27_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1006_; 
lean_inc(v_bkt_982_);
v___x_1001_ = lean_box(0);
v_buckets_x27_1002_ = lean_array_uset(v_buckets_965_, v___x_981_, v___x_1001_);
v___x_1003_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12___redArg(v_a_962_, v_b_963_, v_bkt_982_);
v___x_1004_ = lean_array_uset(v_buckets_x27_1002_, v___x_981_, v___x_1003_);
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 1, v___x_1004_);
v___x_1006_ = v___x_967_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_size_964_);
lean_ctor_set(v_reuseFailAlloc_1007_, 1, v___x_1004_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2(lean_object* v_a_1009_, lean_object* v_e_1010_, lean_object* v_a_1011_){
_start:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1013_ = lean_st_ref_take(v_a_1009_);
v___x_1014_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6___redArg(v___x_1013_, v_e_1010_, v_a_1011_);
v___x_1015_ = lean_st_ref_set(v_a_1009_, v___x_1014_);
v___x_1016_ = lean_box(0);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2___boxed(lean_object* v_a_1017_, lean_object* v_e_1018_, lean_object* v_a_1019_, lean_object* v___y_1020_){
_start:
{
lean_object* v_res_1021_; 
v_res_1021_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2(v_a_1017_, v_e_1018_, v_a_1019_);
lean_dec(v_a_1017_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_1022_, lean_object* v_x_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = lean_apply_1(v_x_1023_, lean_box(0));
v___x_1028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1027_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1029_, lean_object* v_x_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(v_00_u03b1_1029_, v_x_1030_, v___y_1031_, v___y_1032_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
return v_res_1034_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0(void){
_start:
{
lean_object* v___x_1036_; lean_object* v_dummy_1037_; 
v___x_1036_ = lean_box(0);
v_dummy_1037_ = l_Lean_Expr_sort___override(v___x_1036_);
return v_dummy_1037_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1(lean_object* v_pre_1038_, lean_object* v_post_1039_, size_t v_sz_1040_, size_t v_i_1041_, lean_object* v_bs_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_){
_start:
{
uint8_t v___x_1047_; 
v___x_1047_ = lean_usize_dec_lt(v_i_1041_, v_sz_1040_);
if (v___x_1047_ == 0)
{
lean_object* v___x_1048_; 
lean_dec_ref(v_post_1039_);
lean_dec_ref(v_pre_1038_);
v___x_1048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1048_, 0, v_bs_1042_);
return v___x_1048_;
}
else
{
lean_object* v_v_1049_; lean_object* v___x_1050_; 
v_v_1049_ = lean_array_uget_borrowed(v_bs_1042_, v_i_1041_);
lean_inc(v_v_1049_);
lean_inc_ref(v_post_1039_);
lean_inc_ref(v_pre_1038_);
v___x_1050_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1038_, v_post_1039_, v_v_1049_, v___y_1043_, v___y_1044_, v___y_1045_);
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_object* v_a_1051_; lean_object* v___x_1052_; lean_object* v_bs_x27_1053_; size_t v___x_1054_; size_t v___x_1055_; lean_object* v___x_1056_; 
v_a_1051_ = lean_ctor_get(v___x_1050_, 0);
lean_inc(v_a_1051_);
lean_dec_ref_known(v___x_1050_, 1);
v___x_1052_ = lean_unsigned_to_nat(0u);
v_bs_x27_1053_ = lean_array_uset(v_bs_1042_, v_i_1041_, v___x_1052_);
v___x_1054_ = ((size_t)1ULL);
v___x_1055_ = lean_usize_add(v_i_1041_, v___x_1054_);
v___x_1056_ = lean_array_uset(v_bs_x27_1053_, v_i_1041_, v_a_1051_);
v_i_1041_ = v___x_1055_;
v_bs_1042_ = v___x_1056_;
goto _start;
}
else
{
lean_object* v_a_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1065_; 
lean_dec_ref(v_bs_1042_);
lean_dec_ref(v_post_1039_);
lean_dec_ref(v_pre_1038_);
v_a_1058_ = lean_ctor_get(v___x_1050_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1060_ = v___x_1050_;
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_a_1058_);
lean_dec(v___x_1050_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1063_; 
if (v_isShared_1061_ == 0)
{
v___x_1063_ = v___x_1060_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_a_1058_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4(lean_object* v_pre_1066_, lean_object* v_post_1067_, lean_object* v_x_1068_, lean_object* v_x_1069_, lean_object* v_x_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_){
_start:
{
if (lean_obj_tag(v_x_1068_) == 5)
{
lean_object* v_fn_1075_; lean_object* v_arg_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
v_fn_1075_ = lean_ctor_get(v_x_1068_, 0);
lean_inc_ref(v_fn_1075_);
v_arg_1076_ = lean_ctor_get(v_x_1068_, 1);
lean_inc_ref(v_arg_1076_);
lean_dec_ref_known(v_x_1068_, 2);
v___x_1077_ = lean_array_set(v_x_1069_, v_x_1070_, v_arg_1076_);
v___x_1078_ = lean_unsigned_to_nat(1u);
v___x_1079_ = lean_nat_sub(v_x_1070_, v___x_1078_);
lean_dec(v_x_1070_);
v_x_1068_ = v_fn_1075_;
v_x_1069_ = v___x_1077_;
v_x_1070_ = v___x_1079_;
goto _start;
}
else
{
lean_object* v___x_1081_; 
lean_dec(v_x_1070_);
lean_inc_ref(v_post_1067_);
lean_inc_ref(v_pre_1066_);
v___x_1081_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1066_, v_post_1067_, v_x_1068_, v___y_1071_, v___y_1072_, v___y_1073_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v_a_1082_; size_t v_sz_1083_; size_t v___x_1084_; lean_object* v___x_1085_; 
v_a_1082_ = lean_ctor_get(v___x_1081_, 0);
lean_inc(v_a_1082_);
lean_dec_ref_known(v___x_1081_, 1);
v_sz_1083_ = lean_array_size(v_x_1069_);
v___x_1084_ = ((size_t)0ULL);
lean_inc_ref(v_post_1067_);
lean_inc_ref(v_pre_1066_);
v___x_1085_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1(v_pre_1066_, v_post_1067_, v_sz_1083_, v___x_1084_, v_x_1069_, v___y_1071_, v___y_1072_, v___y_1073_);
if (lean_obj_tag(v___x_1085_) == 0)
{
lean_object* v_a_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
v_a_1086_ = lean_ctor_get(v___x_1085_, 0);
lean_inc(v_a_1086_);
lean_dec_ref_known(v___x_1085_, 1);
v___x_1087_ = l_Lean_mkAppN(v_a_1082_, v_a_1086_);
lean_dec(v_a_1086_);
v___x_1088_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1066_, v_post_1067_, v___x_1087_, v___y_1071_, v___y_1072_, v___y_1073_);
return v___x_1088_;
}
else
{
lean_object* v_a_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1096_; 
lean_dec(v_a_1082_);
lean_dec_ref(v_post_1067_);
lean_dec_ref(v_pre_1066_);
v_a_1089_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1091_ = v___x_1085_;
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_a_1089_);
lean_dec(v___x_1085_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1094_; 
if (v_isShared_1092_ == 0)
{
v___x_1094_ = v___x_1091_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_a_1089_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
}
else
{
lean_dec_ref(v_x_1069_);
lean_dec_ref(v_post_1067_);
lean_dec_ref(v_pre_1066_);
return v___x_1081_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1(lean_object* v___x_1097_, lean_object* v_pre_1098_, lean_object* v_e_1099_, lean_object* v_post_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
lean_object* v___y_1106_; lean_object* v___y_1107_; lean_object* v___y_1108_; uint8_t v___y_1109_; lean_object* v___y_1110_; lean_object* v___y_1111_; lean_object* v___y_1112_; uint8_t v___y_1113_; lean_object* v___y_1123_; uint8_t v___y_1124_; lean_object* v___y_1125_; lean_object* v___y_1126_; lean_object* v___y_1127_; uint8_t v___y_1128_; lean_object* v___y_1136_; uint8_t v___y_1137_; lean_object* v___y_1138_; lean_object* v___y_1139_; lean_object* v___y_1140_; uint8_t v___y_1141_; lean_object* v___x_1148_; 
v___x_1148_ = l_Lean_Core_checkSystem(v___x_1097_, v___y_1102_, v___y_1103_);
if (lean_obj_tag(v___x_1148_) == 0)
{
lean_object* v___x_1149_; 
lean_dec_ref_known(v___x_1148_, 1);
lean_inc_ref(v_pre_1098_);
lean_inc(v___y_1103_);
lean_inc_ref(v___y_1102_);
lean_inc_ref(v_e_1099_);
v___x_1149_ = lean_apply_4(v_pre_1098_, v_e_1099_, v___y_1102_, v___y_1103_, lean_box(0));
if (lean_obj_tag(v___x_1149_) == 0)
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1239_; 
v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1152_ = v___x_1149_;
v_isShared_1153_ = v_isSharedCheck_1239_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1149_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1239_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___y_1155_; 
switch(lean_obj_tag(v_a_1150_))
{
case 0:
{
lean_object* v_e_1229_; lean_object* v___x_1231_; 
lean_dec_ref(v_post_1100_);
lean_dec_ref(v_e_1099_);
lean_dec_ref(v_pre_1098_);
v_e_1229_ = lean_ctor_get(v_a_1150_, 0);
lean_inc_ref(v_e_1229_);
lean_dec_ref_known(v_a_1150_, 1);
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 0, v_e_1229_);
v___x_1231_ = v___x_1152_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_e_1229_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
case 1:
{
lean_object* v_e_1233_; lean_object* v___x_1234_; 
lean_del_object(v___x_1152_);
lean_dec_ref(v_e_1099_);
v_e_1233_ = lean_ctor_get(v_a_1150_, 0);
lean_inc_ref(v_e_1233_);
lean_dec_ref_known(v_a_1150_, 1);
lean_inc_ref(v_post_1100_);
lean_inc_ref(v_pre_1098_);
v___x_1234_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1098_, v_post_1100_, v_e_1233_, v___y_1101_, v___y_1102_, v___y_1103_);
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_object* v_a_1235_; lean_object* v___x_1236_; 
v_a_1235_ = lean_ctor_get(v___x_1234_, 0);
lean_inc(v_a_1235_);
lean_dec_ref_known(v___x_1234_, 1);
v___x_1236_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1098_, v_post_1100_, v_a_1235_, v___y_1101_, v___y_1102_, v___y_1103_);
return v___x_1236_;
}
else
{
lean_dec_ref(v_post_1100_);
lean_dec_ref(v_pre_1098_);
return v___x_1234_;
}
}
default: 
{
lean_object* v_e_x3f_1237_; 
lean_del_object(v___x_1152_);
v_e_x3f_1237_ = lean_ctor_get(v_a_1150_, 0);
lean_inc(v_e_x3f_1237_);
lean_dec_ref_known(v_a_1150_, 1);
if (lean_obj_tag(v_e_x3f_1237_) == 0)
{
v___y_1155_ = v_e_1099_;
goto v___jp_1154_;
}
else
{
lean_object* v_val_1238_; 
lean_dec_ref(v_e_1099_);
v_val_1238_ = lean_ctor_get(v_e_x3f_1237_, 0);
lean_inc(v_val_1238_);
lean_dec_ref_known(v_e_x3f_1237_, 1);
v___y_1155_ = v_val_1238_;
goto v___jp_1154_;
}
}
}
v___jp_1154_:
{
switch(lean_obj_tag(v___y_1155_))
{
case 7:
{
lean_object* v_binderName_1156_; lean_object* v_binderType_1157_; lean_object* v_body_1158_; uint8_t v_binderInfo_1159_; lean_object* v___x_1160_; 
v_binderName_1156_ = lean_ctor_get(v___y_1155_, 0);
lean_inc(v_binderName_1156_);
v_binderType_1157_ = lean_ctor_get(v___y_1155_, 1);
v_body_1158_ = lean_ctor_get(v___y_1155_, 2);
v_binderInfo_1159_ = lean_ctor_get_uint8(v___y_1155_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1157_);
lean_inc_ref(v_post_1100_);
lean_inc_ref(v_pre_1098_);
v___x_1160_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1098_, v_post_1100_, v_binderType_1157_, v___y_1101_, v___y_1102_, v___y_1103_);
if (lean_obj_tag(v___x_1160_) == 0)
{
lean_object* v_a_1161_; lean_object* v___x_1162_; 
v_a_1161_ = lean_ctor_get(v___x_1160_, 0);
lean_inc(v_a_1161_);
lean_dec_ref_known(v___x_1160_, 1);
lean_inc_ref(v_body_1158_);
lean_inc_ref(v_post_1100_);
lean_inc_ref(v_pre_1098_);
v___x_1162_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1098_, v_post_1100_, v_body_1158_, v___y_1101_, v___y_1102_, v___y_1103_);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v_a_1163_; size_t v___x_1164_; size_t v___x_1165_; uint8_t v___x_1166_; 
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
lean_inc(v_a_1163_);
lean_dec_ref_known(v___x_1162_, 1);
v___x_1164_ = lean_ptr_addr(v_binderType_1157_);
v___x_1165_ = lean_ptr_addr(v_a_1161_);
v___x_1166_ = lean_usize_dec_eq(v___x_1164_, v___x_1165_);
if (v___x_1166_ == 0)
{
v___y_1136_ = v_a_1163_;
v___y_1137_ = v_binderInfo_1159_;
v___y_1138_ = v_binderName_1156_;
v___y_1139_ = v___y_1155_;
v___y_1140_ = v_a_1161_;
v___y_1141_ = v___x_1166_;
goto v___jp_1135_;
}
else
{
size_t v___x_1167_; size_t v___x_1168_; uint8_t v___x_1169_; 
v___x_1167_ = lean_ptr_addr(v_body_1158_);
v___x_1168_ = lean_ptr_addr(v_a_1163_);
v___x_1169_ = lean_usize_dec_eq(v___x_1167_, v___x_1168_);
v___y_1136_ = v_a_1163_;
v___y_1137_ = v_binderInfo_1159_;
v___y_1138_ = v_binderName_1156_;
v___y_1139_ = v___y_1155_;
v___y_1140_ = v_a_1161_;
v___y_1141_ = v___x_1169_;
goto v___jp_1135_;
}
}
else
{
lean_dec(v_a_1161_);
lean_dec(v_binderName_1156_);
lean_dec_ref_known(v___y_1155_, 3);
lean_dec_ref(v_post_1100_);
lean_dec_ref(v_pre_1098_);
return v___x_1162_;
}
}
else
{
lean_dec(v_binderName_1156_);
lean_dec_ref_known(v___y_1155_, 3);
lean_dec_ref(v_post_1100_);
lean_dec_ref(v_pre_1098_);
return v___x_1160_;
}
}
case 6:
{
lean_object* v_binderName_1170_; lean_object* v_binderType_1171_; lean_object* v_body_1172_; uint8_t v_binderInfo_1173_; lean_object* v___x_1174_; 
v_binderName_1170_ = lean_ctor_get(v___y_1155_, 0);
lean_inc(v_binderName_1170_);
v_binderType_1171_ = lean_ctor_get(v___y_1155_, 1);
v_body_1172_ = lean_ctor_get(v___y_1155_, 2);
v_binderInfo_1173_ = lean_ctor_get_uint8(v___y_1155_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1171_);
lean_inc_ref(v_post_1100_);
lean_inc_ref(v_pre_1098_);
v___x_1174_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1098_, v_post_1100_, v_binderType_1171_, v___y_1101_, v___y_1102_, v___y_1103_);
if (lean_obj_tag(v___x_1174_) == 0)
{
lean_object* v_a_1175_; lean_object* v___x_1176_; 
v_a_1175_ = lean_ctor_get(v___x_1174_, 0);
lean_inc(v_a_1175_);
lean_dec_ref_known(v___x_1174_, 1);
lean_inc_ref(v_body_1172_);
lean_inc_ref(v_post_1100_);
lean_inc_ref(v_pre_1098_);
v___x_1176_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1098_, v_post_1100_, v_body_1172_, v___y_1101_, v___y_1102_, v___y_1103_);
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_object* v_a_1177_; size_t v___x_1178_; size_t v___x_1179_; uint8_t v___x_1180_; 
v_a_1177_ = lean_ctor_get(v___x_1176_, 0);
lean_inc(v_a_1177_);
lean_dec_ref_known(v___x_1176_, 1);
v___x_1178_ = lean_ptr_addr(v_binderType_1171_);
v___x_1179_ = lean_ptr_addr(v_a_1175_);
v___x_1180_ = lean_usize_dec_eq(v___x_1178_, v___x_1179_);
if (v___x_1180_ == 0)
{
v___y_1123_ = v_binderName_1170_;
v___y_1124_ = v_binderInfo_1173_;
v___y_1125_ = v_a_1175_;
v___y_1126_ = v___y_1155_;
v___y_1127_ = v_a_1177_;
v___y_1128_ = v___x_1180_;
goto v___jp_1122_;
}
else
{
size_t v___x_1181_; size_t v___x_1182_; uint8_t v___x_1183_; 
v___x_1181_ = lean_ptr_addr(v_body_1172_);
v___x_1182_ = lean_ptr_addr(v_a_1177_);
v___x_1183_ = lean_usize_dec_eq(v___x_1181_, v___x_1182_);
v___y_1123_ = v_binderName_1170_;
v___y_1124_ = v_binderInfo_1173_;
v___y_1125_ = v_a_1175_;
v___y_1126_ = v___y_1155_;
v___y_1127_ = v_a_1177_;
v___y_1128_ = v___x_1183_;
goto v___jp_1122_;
}
}
else
{
lean_dec(v_a_1175_);
lean_dec(v_binderName_1170_);
lean_dec_ref_known(v___y_1155_, 3);
lean_dec_ref(v_post_1100_);
lean_dec_ref(v_pre_1098_);
return v___x_1176_;
}
}
else
{
lean_dec(v_binderName_1170_);
lean_dec_ref_known(v___y_1155_, 3);
lean_dec_ref(v_post_1100_);
lean_dec_ref(v_pre_1098_);
return v___x_1174_;
}
}
case 8:
{
lean_object* v_declName_1184_; lean_object* v_type_1185_; lean_object* v_value_1186_; lean_object* v_body_1187_; uint8_t v_nondep_1188_; lean_object* v___x_1189_; 
v_declName_1184_ = lean_ctor_get(v___y_1155_, 0);
lean_inc(v_declName_1184_);
v_type_1185_ = lean_ctor_get(v___y_1155_, 1);
v_value_1186_ = lean_ctor_get(v___y_1155_, 2);
v_body_1187_ = lean_ctor_get(v___y_1155_, 3);
lean_inc_ref(v_body_1187_);
v_nondep_1188_ = lean_ctor_get_uint8(v___y_1155_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_1185_);
lean_inc_ref(v_post_1100_);
lean_inc_ref(v_pre_1098_);
v___x_1189_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1098_, v_post_1100_, v_type_1185_, v___y_1101_, v___y_1102_, v___y_1103_);
if (lean_obj_tag(v___x_1189_) == 0)
{
lean_object* v_a_1190_; lean_object* v___x_1191_; 
v_a_1190_ = lean_ctor_get(v___x_1189_, 0);
lean_inc(v_a_1190_);
lean_dec_ref_known(v___x_1189_, 1);
lean_inc_ref(v_value_1186_);
lean_inc_ref(v_post_1100_);
lean_inc_ref(v_pre_1098_);
v___x_1191_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1098_, v_post_1100_, v_value_1186_, v___y_1101_, v___y_1102_, v___y_1103_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v_a_1192_; lean_object* v___x_1193_; 
v_a_1192_ = lean_ctor_get(v___x_1191_, 0);
lean_inc(v_a_1192_);
lean_dec_ref_known(v___x_1191_, 1);
lean_inc_ref(v_body_1187_);
lean_inc_ref(v_post_1100_);
lean_inc_ref(v_pre_1098_);
v___x_1193_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1098_, v_post_1100_, v_body_1187_, v___y_1101_, v___y_1102_, v___y_1103_);
if (lean_obj_tag(v___x_1193_) == 0)
{
lean_object* v_a_1194_; size_t v___x_1195_; size_t v___x_1196_; uint8_t v___x_1197_; 
v_a_1194_ = lean_ctor_get(v___x_1193_, 0);
lean_inc(v_a_1194_);
lean_dec_ref_known(v___x_1193_, 1);
v___x_1195_ = lean_ptr_addr(v_type_1185_);
v___x_1196_ = lean_ptr_addr(v_a_1190_);
v___x_1197_ = lean_usize_dec_eq(v___x_1195_, v___x_1196_);
if (v___x_1197_ == 0)
{
v___y_1106_ = v_body_1187_;
v___y_1107_ = v_a_1194_;
v___y_1108_ = v_declName_1184_;
v___y_1109_ = v_nondep_1188_;
v___y_1110_ = v_a_1190_;
v___y_1111_ = v___y_1155_;
v___y_1112_ = v_a_1192_;
v___y_1113_ = v___x_1197_;
goto v___jp_1105_;
}
else
{
size_t v___x_1198_; size_t v___x_1199_; uint8_t v___x_1200_; 
v___x_1198_ = lean_ptr_addr(v_value_1186_);
v___x_1199_ = lean_ptr_addr(v_a_1192_);
v___x_1200_ = lean_usize_dec_eq(v___x_1198_, v___x_1199_);
v___y_1106_ = v_body_1187_;
v___y_1107_ = v_a_1194_;
v___y_1108_ = v_declName_1184_;
v___y_1109_ = v_nondep_1188_;
v___y_1110_ = v_a_1190_;
v___y_1111_ = v___y_1155_;
v___y_1112_ = v_a_1192_;
v___y_1113_ = v___x_1200_;
goto v___jp_1105_;
}
}
else
{
lean_dec(v_a_1192_);
lean_dec(v_a_1190_);
lean_dec_ref(v_body_1187_);
lean_dec(v_declName_1184_);
lean_dec_ref_known(v___y_1155_, 4);
lean_dec_ref(v_post_1100_);
lean_dec_ref(v_pre_1098_);
return v___x_1193_;
}
}
else
{
lean_dec(v_a_1190_);
lean_dec_ref(v_body_1187_);
lean_dec(v_declName_1184_);
lean_dec_ref_known(v___y_1155_, 4);
lean_dec_ref(v_post_1100_);
lean_dec_ref(v_pre_1098_);
return v___x_1191_;
}
}
else
{
lean_dec_ref(v_body_1187_);
lean_dec(v_declName_1184_);
lean_dec_ref_known(v___y_1155_, 4);
lean_dec_ref(v_post_1100_);
lean_dec_ref(v_pre_1098_);
return v___x_1189_;
}
}
case 5:
{
lean_object* v_dummy_1201_; lean_object* v_nargs_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v_dummy_1201_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0);
v_nargs_1202_ = l_Lean_Expr_getAppNumArgs(v___y_1155_);
lean_inc(v_nargs_1202_);
v___x_1203_ = lean_mk_array(v_nargs_1202_, v_dummy_1201_);
v___x_1204_ = lean_unsigned_to_nat(1u);
v___x_1205_ = lean_nat_sub(v_nargs_1202_, v___x_1204_);
lean_dec(v_nargs_1202_);
v___x_1206_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4(v_pre_1098_, v_post_1100_, v___y_1155_, v___x_1203_, v___x_1205_, v___y_1101_, v___y_1102_, v___y_1103_);
return v___x_1206_;
}
case 10:
{
lean_object* v_data_1207_; lean_object* v_expr_1208_; lean_object* v___x_1209_; 
v_data_1207_ = lean_ctor_get(v___y_1155_, 0);
v_expr_1208_ = lean_ctor_get(v___y_1155_, 1);
lean_inc_ref(v_expr_1208_);
lean_inc_ref(v_post_1100_);
lean_inc_ref(v_pre_1098_);
v___x_1209_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1098_, v_post_1100_, v_expr_1208_, v___y_1101_, v___y_1102_, v___y_1103_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_object* v_a_1210_; size_t v___x_1211_; size_t v___x_1212_; uint8_t v___x_1213_; 
v_a_1210_ = lean_ctor_get(v___x_1209_, 0);
lean_inc(v_a_1210_);
lean_dec_ref_known(v___x_1209_, 1);
v___x_1211_ = lean_ptr_addr(v_expr_1208_);
v___x_1212_ = lean_ptr_addr(v_a_1210_);
v___x_1213_ = lean_usize_dec_eq(v___x_1211_, v___x_1212_);
if (v___x_1213_ == 0)
{
lean_object* v___x_1214_; lean_object* v___x_1215_; 
lean_inc(v_data_1207_);
lean_dec_ref_known(v___y_1155_, 2);
v___x_1214_ = l_Lean_Expr_mdata___override(v_data_1207_, v_a_1210_);
v___x_1215_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1098_, v_post_1100_, v___x_1214_, v___y_1101_, v___y_1102_, v___y_1103_);
return v___x_1215_;
}
else
{
lean_object* v___x_1216_; 
lean_dec(v_a_1210_);
v___x_1216_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1098_, v_post_1100_, v___y_1155_, v___y_1101_, v___y_1102_, v___y_1103_);
return v___x_1216_;
}
}
else
{
lean_dec_ref_known(v___y_1155_, 2);
lean_dec_ref(v_post_1100_);
lean_dec_ref(v_pre_1098_);
return v___x_1209_;
}
}
case 11:
{
lean_object* v_typeName_1217_; lean_object* v_idx_1218_; lean_object* v_struct_1219_; lean_object* v___x_1220_; 
v_typeName_1217_ = lean_ctor_get(v___y_1155_, 0);
v_idx_1218_ = lean_ctor_get(v___y_1155_, 1);
v_struct_1219_ = lean_ctor_get(v___y_1155_, 2);
lean_inc_ref(v_struct_1219_);
lean_inc_ref(v_post_1100_);
lean_inc_ref(v_pre_1098_);
v___x_1220_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1098_, v_post_1100_, v_struct_1219_, v___y_1101_, v___y_1102_, v___y_1103_);
if (lean_obj_tag(v___x_1220_) == 0)
{
lean_object* v_a_1221_; size_t v___x_1222_; size_t v___x_1223_; uint8_t v___x_1224_; 
v_a_1221_ = lean_ctor_get(v___x_1220_, 0);
lean_inc(v_a_1221_);
lean_dec_ref_known(v___x_1220_, 1);
v___x_1222_ = lean_ptr_addr(v_struct_1219_);
v___x_1223_ = lean_ptr_addr(v_a_1221_);
v___x_1224_ = lean_usize_dec_eq(v___x_1222_, v___x_1223_);
if (v___x_1224_ == 0)
{
lean_object* v___x_1225_; lean_object* v___x_1226_; 
lean_inc(v_idx_1218_);
lean_inc(v_typeName_1217_);
lean_dec_ref_known(v___y_1155_, 3);
v___x_1225_ = l_Lean_Expr_proj___override(v_typeName_1217_, v_idx_1218_, v_a_1221_);
v___x_1226_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1098_, v_post_1100_, v___x_1225_, v___y_1101_, v___y_1102_, v___y_1103_);
return v___x_1226_;
}
else
{
lean_object* v___x_1227_; 
lean_dec(v_a_1221_);
v___x_1227_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1098_, v_post_1100_, v___y_1155_, v___y_1101_, v___y_1102_, v___y_1103_);
return v___x_1227_;
}
}
else
{
lean_dec_ref_known(v___y_1155_, 3);
lean_dec_ref(v_post_1100_);
lean_dec_ref(v_pre_1098_);
return v___x_1220_;
}
}
default: 
{
lean_object* v___x_1228_; 
v___x_1228_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1098_, v_post_1100_, v___y_1155_, v___y_1101_, v___y_1102_, v___y_1103_);
return v___x_1228_;
}
}
}
}
}
else
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1247_; 
lean_dec_ref(v_post_1100_);
lean_dec_ref(v_e_1099_);
lean_dec_ref(v_pre_1098_);
v_a_1240_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1242_ = v___x_1149_;
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1149_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1245_; 
if (v_isShared_1243_ == 0)
{
v___x_1245_ = v___x_1242_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_a_1240_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
else
{
lean_object* v_a_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1255_; 
lean_dec_ref(v_post_1100_);
lean_dec_ref(v_e_1099_);
lean_dec_ref(v_pre_1098_);
v_a_1248_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1250_ = v___x_1148_;
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_a_1248_);
lean_dec(v___x_1148_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1253_; 
if (v_isShared_1251_ == 0)
{
v___x_1253_ = v___x_1250_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_a_1248_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
v___jp_1105_:
{
if (v___y_1113_ == 0)
{
lean_object* v___x_1114_; lean_object* v___x_1115_; 
lean_dec_ref(v___y_1111_);
lean_dec_ref(v___y_1106_);
v___x_1114_ = l_Lean_Expr_letE___override(v___y_1108_, v___y_1110_, v___y_1112_, v___y_1107_, v___y_1109_);
v___x_1115_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1098_, v_post_1100_, v___x_1114_, v___y_1101_, v___y_1102_, v___y_1103_);
return v___x_1115_;
}
else
{
size_t v___x_1116_; size_t v___x_1117_; uint8_t v___x_1118_; 
v___x_1116_ = lean_ptr_addr(v___y_1106_);
lean_dec_ref(v___y_1106_);
v___x_1117_ = lean_ptr_addr(v___y_1107_);
v___x_1118_ = lean_usize_dec_eq(v___x_1116_, v___x_1117_);
if (v___x_1118_ == 0)
{
lean_object* v___x_1119_; lean_object* v___x_1120_; 
lean_dec_ref(v___y_1111_);
v___x_1119_ = l_Lean_Expr_letE___override(v___y_1108_, v___y_1110_, v___y_1112_, v___y_1107_, v___y_1109_);
v___x_1120_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1098_, v_post_1100_, v___x_1119_, v___y_1101_, v___y_1102_, v___y_1103_);
return v___x_1120_;
}
else
{
lean_object* v___x_1121_; 
lean_dec_ref(v___y_1112_);
lean_dec_ref(v___y_1110_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
v___x_1121_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1098_, v_post_1100_, v___y_1111_, v___y_1101_, v___y_1102_, v___y_1103_);
return v___x_1121_;
}
}
}
v___jp_1122_:
{
if (v___y_1128_ == 0)
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
lean_dec_ref(v___y_1126_);
v___x_1129_ = l_Lean_Expr_lam___override(v___y_1123_, v___y_1125_, v___y_1127_, v___y_1124_);
v___x_1130_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1098_, v_post_1100_, v___x_1129_, v___y_1101_, v___y_1102_, v___y_1103_);
return v___x_1130_;
}
else
{
uint8_t v___x_1131_; 
v___x_1131_ = l_Lean_instBEqBinderInfo_beq(v___y_1124_, v___y_1124_);
if (v___x_1131_ == 0)
{
lean_object* v___x_1132_; lean_object* v___x_1133_; 
lean_dec_ref(v___y_1126_);
v___x_1132_ = l_Lean_Expr_lam___override(v___y_1123_, v___y_1125_, v___y_1127_, v___y_1124_);
v___x_1133_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1098_, v_post_1100_, v___x_1132_, v___y_1101_, v___y_1102_, v___y_1103_);
return v___x_1133_;
}
else
{
lean_object* v___x_1134_; 
lean_dec_ref(v___y_1127_);
lean_dec_ref(v___y_1125_);
lean_dec(v___y_1123_);
v___x_1134_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1098_, v_post_1100_, v___y_1126_, v___y_1101_, v___y_1102_, v___y_1103_);
return v___x_1134_;
}
}
}
v___jp_1135_:
{
if (v___y_1141_ == 0)
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
lean_dec_ref(v___y_1139_);
v___x_1142_ = l_Lean_Expr_forallE___override(v___y_1138_, v___y_1140_, v___y_1136_, v___y_1137_);
v___x_1143_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1098_, v_post_1100_, v___x_1142_, v___y_1101_, v___y_1102_, v___y_1103_);
return v___x_1143_;
}
else
{
uint8_t v___x_1144_; 
v___x_1144_ = l_Lean_instBEqBinderInfo_beq(v___y_1137_, v___y_1137_);
if (v___x_1144_ == 0)
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
lean_dec_ref(v___y_1139_);
v___x_1145_ = l_Lean_Expr_forallE___override(v___y_1138_, v___y_1140_, v___y_1136_, v___y_1137_);
v___x_1146_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1098_, v_post_1100_, v___x_1145_, v___y_1101_, v___y_1102_, v___y_1103_);
return v___x_1146_;
}
else
{
lean_object* v___x_1147_; 
lean_dec_ref(v___y_1140_);
lean_dec(v___y_1138_);
lean_dec_ref(v___y_1136_);
v___x_1147_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1098_, v_post_1100_, v___y_1139_, v___y_1101_, v___y_1102_, v___y_1103_);
return v___x_1147_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___boxed(lean_object* v___x_1256_, lean_object* v_pre_1257_, lean_object* v_e_1258_, lean_object* v_post_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1(v___x_1256_, v_pre_1257_, v_e_1258_, v_post_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
lean_dec(v___y_1260_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(lean_object* v_pre_1265_, lean_object* v_post_1266_, lean_object* v_e_1267_, lean_object* v_a_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; 
lean_inc(v_a_1268_);
v___x_1272_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1272_, 0, lean_box(0));
lean_closure_set(v___x_1272_, 1, lean_box(0));
lean_closure_set(v___x_1272_, 2, v_a_1268_);
v___x_1273_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(lean_box(0), v___x_1272_, v___y_1269_, v___y_1270_);
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_object* v_a_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1305_; 
v_a_1274_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1276_ = v___x_1273_;
v_isShared_1277_ = v_isSharedCheck_1305_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_a_1274_);
lean_dec(v___x_1273_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1305_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1278_; 
v___x_1278_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg(v_a_1274_, v_e_1267_);
lean_dec(v_a_1274_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v___x_1279_; lean_object* v___f_1280_; lean_object* v___x_1281_; 
lean_del_object(v___x_1276_);
v___x_1279_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___closed__0));
lean_inc_ref(v_e_1267_);
v___f_1280_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___boxed), 8, 4);
lean_closure_set(v___f_1280_, 0, v___x_1279_);
lean_closure_set(v___f_1280_, 1, v_pre_1265_);
lean_closure_set(v___f_1280_, 2, v_e_1267_);
lean_closure_set(v___f_1280_, 3, v_post_1266_);
v___x_1281_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg(v___f_1280_, v_a_1268_, v___y_1269_, v___y_1270_);
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_object* v_a_1282_; lean_object* v___f_1283_; lean_object* v___x_1284_; 
v_a_1282_ = lean_ctor_get(v___x_1281_, 0);
lean_inc_n(v_a_1282_, 2);
lean_dec_ref_known(v___x_1281_, 1);
lean_inc(v_a_1268_);
v___f_1283_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1283_, 0, v_a_1268_);
lean_closure_set(v___f_1283_, 1, v_e_1267_);
lean_closure_set(v___f_1283_, 2, v_a_1282_);
v___x_1284_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(lean_box(0), v___f_1283_, v___y_1269_, v___y_1270_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1291_; 
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1291_ == 0)
{
lean_object* v_unused_1292_; 
v_unused_1292_ = lean_ctor_get(v___x_1284_, 0);
lean_dec(v_unused_1292_);
v___x_1286_ = v___x_1284_;
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
else
{
lean_dec(v___x_1284_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1289_; 
if (v_isShared_1287_ == 0)
{
lean_ctor_set(v___x_1286_, 0, v_a_1282_);
v___x_1289_ = v___x_1286_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_a_1282_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
else
{
lean_object* v_a_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1300_; 
lean_dec(v_a_1282_);
v_a_1293_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1295_ = v___x_1284_;
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_a_1293_);
lean_dec(v___x_1284_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1298_; 
if (v_isShared_1296_ == 0)
{
v___x_1298_ = v___x_1295_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_a_1293_);
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
else
{
lean_dec_ref(v_e_1267_);
return v___x_1281_;
}
}
else
{
lean_object* v_val_1301_; lean_object* v___x_1303_; 
lean_dec_ref(v_e_1267_);
lean_dec_ref(v_post_1266_);
lean_dec_ref(v_pre_1265_);
v_val_1301_ = lean_ctor_get(v___x_1278_, 0);
lean_inc(v_val_1301_);
lean_dec_ref_known(v___x_1278_, 1);
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 0, v_val_1301_);
v___x_1303_ = v___x_1276_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_val_1301_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
}
}
else
{
lean_object* v_a_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1313_; 
lean_dec_ref(v_e_1267_);
lean_dec_ref(v_post_1266_);
lean_dec_ref(v_pre_1265_);
v_a_1306_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1308_ = v___x_1273_;
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_a_1306_);
lean_dec(v___x_1273_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1311_; 
if (v_isShared_1309_ == 0)
{
v___x_1311_ = v___x_1308_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_a_1306_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(lean_object* v_pre_1314_, lean_object* v_post_1315_, lean_object* v_e_1316_, lean_object* v_a_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_){
_start:
{
lean_object* v___x_1321_; 
lean_inc_ref(v_post_1315_);
lean_inc(v___y_1319_);
lean_inc_ref(v___y_1318_);
lean_inc_ref(v_e_1316_);
v___x_1321_ = lean_apply_4(v_post_1315_, v_e_1316_, v___y_1318_, v___y_1319_, lean_box(0));
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_object* v_a_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1340_; 
v_a_1322_ = lean_ctor_get(v___x_1321_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1324_ = v___x_1321_;
v_isShared_1325_ = v_isSharedCheck_1340_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_a_1322_);
lean_dec(v___x_1321_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1340_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
switch(lean_obj_tag(v_a_1322_))
{
case 0:
{
lean_object* v_e_1326_; lean_object* v___x_1328_; 
lean_dec_ref(v_e_1316_);
lean_dec_ref(v_post_1315_);
lean_dec_ref(v_pre_1314_);
v_e_1326_ = lean_ctor_get(v_a_1322_, 0);
lean_inc_ref(v_e_1326_);
lean_dec_ref_known(v_a_1322_, 1);
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 0, v_e_1326_);
v___x_1328_ = v___x_1324_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_e_1326_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
return v___x_1328_;
}
}
case 1:
{
lean_object* v_e_1330_; lean_object* v___x_1331_; 
lean_del_object(v___x_1324_);
lean_dec_ref(v_e_1316_);
v_e_1330_ = lean_ctor_get(v_a_1322_, 0);
lean_inc_ref(v_e_1330_);
lean_dec_ref_known(v_a_1322_, 1);
v___x_1331_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1314_, v_post_1315_, v_e_1330_, v_a_1317_, v___y_1318_, v___y_1319_);
return v___x_1331_;
}
default: 
{
lean_object* v_e_x3f_1332_; 
lean_dec_ref(v_post_1315_);
lean_dec_ref(v_pre_1314_);
v_e_x3f_1332_ = lean_ctor_get(v_a_1322_, 0);
lean_inc(v_e_x3f_1332_);
lean_dec_ref_known(v_a_1322_, 1);
if (lean_obj_tag(v_e_x3f_1332_) == 0)
{
lean_object* v___x_1334_; 
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 0, v_e_1316_);
v___x_1334_ = v___x_1324_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_e_1316_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
else
{
lean_object* v_val_1336_; lean_object* v___x_1338_; 
lean_dec_ref(v_e_1316_);
v_val_1336_ = lean_ctor_get(v_e_x3f_1332_, 0);
lean_inc(v_val_1336_);
lean_dec_ref_known(v_e_x3f_1332_, 1);
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 0, v_val_1336_);
v___x_1338_ = v___x_1324_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_val_1336_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
}
}
}
else
{
lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1348_; 
lean_dec_ref(v_e_1316_);
lean_dec_ref(v_post_1315_);
lean_dec_ref(v_pre_1314_);
v_a_1341_ = lean_ctor_get(v___x_1321_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1343_ = v___x_1321_;
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_dec(v___x_1321_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1346_; 
if (v_isShared_1344_ == 0)
{
v___x_1346_ = v___x_1343_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_a_1341_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_1349_, lean_object* v_post_1350_, lean_object* v_e_1351_, lean_object* v_a_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
lean_object* v_res_1356_; 
v_res_1356_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1349_, v_post_1350_, v_e_1351_, v_a_1352_, v___y_1353_, v___y_1354_);
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
lean_dec(v_a_1352_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_1357_, lean_object* v_post_1358_, lean_object* v_sz_1359_, lean_object* v_i_1360_, lean_object* v_bs_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_){
_start:
{
size_t v_sz_boxed_1366_; size_t v_i_boxed_1367_; lean_object* v_res_1368_; 
v_sz_boxed_1366_ = lean_unbox_usize(v_sz_1359_);
lean_dec(v_sz_1359_);
v_i_boxed_1367_ = lean_unbox_usize(v_i_1360_);
lean_dec(v_i_1360_);
v_res_1368_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1(v_pre_1357_, v_post_1358_, v_sz_boxed_1366_, v_i_boxed_1367_, v_bs_1361_, v___y_1362_, v___y_1363_, v___y_1364_);
lean_dec(v___y_1364_);
lean_dec_ref(v___y_1363_);
lean_dec(v___y_1362_);
return v_res_1368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_1369_, lean_object* v_post_1370_, lean_object* v_x_1371_, lean_object* v_x_1372_, lean_object* v_x_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_){
_start:
{
lean_object* v_res_1378_; 
v_res_1378_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4(v_pre_1369_, v_post_1370_, v_x_1371_, v_x_1372_, v_x_1373_, v___y_1374_, v___y_1375_, v___y_1376_);
lean_dec(v___y_1376_);
lean_dec_ref(v___y_1375_);
lean_dec(v___y_1374_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___boxed(lean_object* v_pre_1379_, lean_object* v_post_1380_, lean_object* v_e_1381_, lean_object* v_a_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_){
_start:
{
lean_object* v_res_1386_; 
v_res_1386_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1379_, v_post_1380_, v_e_1381_, v_a_1382_, v___y_1383_, v___y_1384_);
lean_dec(v___y_1384_);
lean_dec_ref(v___y_1383_);
lean_dec(v_a_1382_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(lean_object* v_00_u03b1_1387_, lean_object* v_x_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1392_ = lean_apply_1(v_x_1388_, lean_box(0));
v___x_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1392_);
return v___x_1393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1394_, lean_object* v_x_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(v_00_u03b1_1394_, v_x_1395_, v___y_1396_, v___y_1397_);
lean_dec(v___y_1397_);
lean_dec_ref(v___y_1396_);
return v_res_1399_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1400_ = lean_box(0);
v___x_1401_ = lean_unsigned_to_nat(16u);
v___x_1402_ = lean_mk_array(v___x_1401_, v___x_1400_);
return v___x_1402_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1403_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0, &l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0);
v___x_1404_ = lean_unsigned_to_nat(0u);
v___x_1405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1405_, 0, v___x_1404_);
lean_ctor_set(v___x_1405_, 1, v___x_1403_);
return v___x_1405_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; 
v___x_1406_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1, &l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1_once, _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1);
v___x_1407_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1407_, 0, lean_box(0));
lean_closure_set(v___x_1407_, 1, lean_box(0));
lean_closure_set(v___x_1407_, 2, v___x_1406_);
return v___x_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0(lean_object* v_input_1408_, lean_object* v_pre_1409_, lean_object* v_post_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v_a_1416_; lean_object* v___x_1417_; 
v___x_1414_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2);
v___x_1415_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(lean_box(0), v___x_1414_, v___y_1411_, v___y_1412_);
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
lean_inc(v_a_1416_);
lean_dec_ref(v___x_1415_);
v___x_1417_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1409_, v_post_1410_, v_input_1408_, v_a_1416_, v___y_1411_, v___y_1412_);
if (lean_obj_tag(v___x_1417_) == 0)
{
lean_object* v_a_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1427_; 
v_a_1418_ = lean_ctor_get(v___x_1417_, 0);
lean_inc(v_a_1418_);
lean_dec_ref_known(v___x_1417_, 1);
v___x_1419_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1419_, 0, lean_box(0));
lean_closure_set(v___x_1419_, 1, lean_box(0));
lean_closure_set(v___x_1419_, 2, v_a_1416_);
v___x_1420_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(lean_box(0), v___x_1419_, v___y_1411_, v___y_1412_);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1427_ == 0)
{
lean_object* v_unused_1428_; 
v_unused_1428_ = lean_ctor_get(v___x_1420_, 0);
lean_dec(v_unused_1428_);
v___x_1422_ = v___x_1420_;
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
else
{
lean_dec(v___x_1420_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1425_; 
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 0, v_a_1418_);
v___x_1425_ = v___x_1422_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_a_1418_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
else
{
lean_dec(v_a_1416_);
return v___x_1417_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___boxed(lean_object* v_input_1429_, lean_object* v_pre_1430_, lean_object* v_post_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
lean_object* v_res_1435_; 
v_res_1435_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0(v_input_1429_, v_pre_1430_, v_post_1431_, v___y_1432_, v___y_1433_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(lean_object* v_e_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_){
_start:
{
lean_object* v___f_1442_; lean_object* v___f_1443_; lean_object* v___x_1444_; 
v___f_1442_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___closed__0));
v___f_1443_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___closed__1));
v___x_1444_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0(v_e_1438_, v___f_1442_, v___f_1443_, v_a_1439_, v_a_1440_);
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___boxed(lean_object* v_e_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(v_e_1445_, v_a_1446_, v_a_1447_);
lean_dec(v_a_1447_);
lean_dec_ref(v_a_1446_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1450_, lean_object* v_m_1451_, lean_object* v_a_1452_){
_start:
{
lean_object* v___x_1453_; 
v___x_1453_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg(v_m_1451_, v_a_1452_);
return v___x_1453_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1454_, lean_object* v_m_1455_, lean_object* v_a_1456_){
_start:
{
lean_object* v_res_1457_; 
v_res_1457_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3(v_00_u03b2_1454_, v_m_1455_, v_a_1456_);
lean_dec_ref(v_a_1456_);
lean_dec_ref(v_m_1455_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_1458_, lean_object* v_ref_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
lean_object* v___x_1463_; 
v___x_1463_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1459_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1464_, lean_object* v_ref_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_1464_, v_ref_1465_, v___y_1466_, v___y_1467_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8(lean_object* v_00_u03b1_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
lean_object* v___x_1474_; 
v___x_1474_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg();
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8(v_00_u03b1_1475_, v___y_1476_, v___y_1477_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_1480_, lean_object* v_x_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_){
_start:
{
lean_object* v___x_1486_; 
v___x_1486_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg(v_x_1481_, v___y_1482_, v___y_1483_, v___y_1484_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_1487_, lean_object* v_x_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5(v_00_u03b1_1487_, v_x_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v___y_1489_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_1494_, lean_object* v_m_1495_, lean_object* v_a_1496_, lean_object* v_b_1497_){
_start:
{
lean_object* v___x_1498_; 
v___x_1498_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6___redArg(v_m_1495_, v_a_1496_, v_b_1497_);
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_1499_, lean_object* v_a_1500_, lean_object* v_x_1501_){
_start:
{
lean_object* v___x_1502_; 
v___x_1502_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1500_, v_x_1501_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1503_, lean_object* v_a_1504_, lean_object* v_x_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_1503_, v_a_1504_, v_x_1505_);
lean_dec(v_x_1505_);
lean_dec_ref(v_a_1504_);
return v_res_1506_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_1507_, lean_object* v_a_1508_, lean_object* v_x_1509_){
_start:
{
uint8_t v___x_1510_; 
v___x_1510_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1508_, v_x_1509_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___boxed(lean_object* v_00_u03b2_1511_, lean_object* v_a_1512_, lean_object* v_x_1513_){
_start:
{
uint8_t v_res_1514_; lean_object* v_r_1515_; 
v_res_1514_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10(v_00_u03b2_1511_, v_a_1512_, v_x_1513_);
lean_dec(v_x_1513_);
lean_dec_ref(v_a_1512_);
v_r_1515_ = lean_box(v_res_1514_);
return v_r_1515_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_1516_, lean_object* v_data_1517_){
_start:
{
lean_object* v___x_1518_; 
v___x_1518_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11___redArg(v_data_1517_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12(lean_object* v_00_u03b2_1519_, lean_object* v_a_1520_, lean_object* v_b_1521_, lean_object* v_x_1522_){
_start:
{
lean_object* v___x_1523_; 
v___x_1523_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1520_, v_b_1521_, v_x_1522_);
return v___x_1523_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12(lean_object* v_00_u03b2_1524_, lean_object* v_i_1525_, lean_object* v_source_1526_, lean_object* v_target_1527_){
_start:
{
lean_object* v___x_1528_; 
v___x_1528_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v_i_1525_, v_source_1526_, v_target_1527_);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_1529_, lean_object* v_x_1530_, lean_object* v_x_1531_){
_start:
{
lean_object* v___x_1532_; 
v___x_1532_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_x_1530_, v_x_1531_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(lean_object* v_declName_1533_, lean_object* v___y_1534_){
_start:
{
lean_object* v___x_1536_; lean_object* v_env_1537_; uint8_t v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1536_ = lean_st_ref_get(v___y_1534_);
v_env_1537_ = lean_ctor_get(v___x_1536_, 0);
lean_inc_ref(v_env_1537_);
lean_dec(v___x_1536_);
v___x_1538_ = l_Lean_isRecCore(v_env_1537_, v_declName_1533_);
v___x_1539_ = lean_box(v___x_1538_);
v___x_1540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1539_);
return v___x_1540_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg___boxed(lean_object* v_declName_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_){
_start:
{
lean_object* v_res_1544_; 
v_res_1544_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(v_declName_1541_, v___y_1542_);
lean_dec(v___y_1542_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2(lean_object* v_declName_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_){
_start:
{
lean_object* v___x_1551_; 
v___x_1551_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(v_declName_1545_, v___y_1549_);
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___boxed(lean_object* v_declName_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2(v_declName_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
lean_dec(v___y_1554_);
lean_dec_ref(v___y_1553_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(lean_object* v_declName_1559_, lean_object* v___y_1560_){
_start:
{
lean_object* v___x_1562_; lean_object* v_env_1563_; uint8_t v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1562_ = lean_st_ref_get(v___y_1560_);
v_env_1563_ = lean_ctor_get(v___x_1562_, 0);
lean_inc_ref(v_env_1563_);
lean_dec(v___x_1562_);
v___x_1564_ = l_Lean_getReducibilityStatusCore(v_env_1563_, v_declName_1559_);
v___x_1565_ = lean_box(v___x_1564_);
v___x_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1565_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg___boxed(lean_object* v_declName_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_){
_start:
{
lean_object* v_res_1570_; 
v_res_1570_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(v_declName_1567_, v___y_1568_);
lean_dec(v___y_1568_);
return v_res_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0(lean_object* v_declName_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_){
_start:
{
lean_object* v___x_1577_; lean_object* v_a_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1593_; 
v___x_1577_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(v_declName_1571_, v___y_1575_);
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1580_ = v___x_1577_;
v_isShared_1581_ = v_isSharedCheck_1593_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_a_1578_);
lean_dec(v___x_1577_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1593_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
uint8_t v___x_1582_; 
v___x_1582_ = lean_unbox(v_a_1578_);
lean_dec(v_a_1578_);
if (v___x_1582_ == 0)
{
uint8_t v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1586_; 
v___x_1583_ = 1;
v___x_1584_ = lean_box(v___x_1583_);
if (v_isShared_1581_ == 0)
{
lean_ctor_set(v___x_1580_, 0, v___x_1584_);
v___x_1586_ = v___x_1580_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v___x_1584_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
return v___x_1586_;
}
}
else
{
uint8_t v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1591_; 
v___x_1588_ = 0;
v___x_1589_ = lean_box(v___x_1588_);
if (v_isShared_1581_ == 0)
{
lean_ctor_set(v___x_1580_, 0, v___x_1589_);
v___x_1591_ = v___x_1580_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1589_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0___boxed(lean_object* v_declName_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_){
_start:
{
lean_object* v_res_1600_; 
v_res_1600_ = l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0(v_declName_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1595_);
return v_res_1600_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(lean_object* v_a_1601_, lean_object* v_b_1602_){
_start:
{
lean_object* v_array_1604_; lean_object* v_start_1605_; lean_object* v_stop_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1623_; 
v_array_1604_ = lean_ctor_get(v_a_1601_, 0);
v_start_1605_ = lean_ctor_get(v_a_1601_, 1);
v_stop_1606_ = lean_ctor_get(v_a_1601_, 2);
v_isSharedCheck_1623_ = !lean_is_exclusive(v_a_1601_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1608_ = v_a_1601_;
v_isShared_1609_ = v_isSharedCheck_1623_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_stop_1606_);
lean_inc(v_start_1605_);
lean_inc(v_array_1604_);
lean_dec(v_a_1601_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1623_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
uint8_t v___x_1610_; 
v___x_1610_ = lean_nat_dec_lt(v_start_1605_, v_stop_1606_);
if (v___x_1610_ == 0)
{
lean_object* v___x_1611_; 
lean_del_object(v___x_1608_);
lean_dec(v_stop_1606_);
lean_dec(v_start_1605_);
lean_dec_ref(v_array_1604_);
v___x_1611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1611_, 0, v_b_1602_);
return v___x_1611_;
}
else
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1616_; 
v___x_1612_ = lean_box(0);
v___x_1613_ = lean_unsigned_to_nat(1u);
v___x_1614_ = lean_nat_add(v_start_1605_, v___x_1613_);
lean_inc_ref(v_array_1604_);
if (v_isShared_1609_ == 0)
{
lean_ctor_set(v___x_1608_, 1, v___x_1614_);
v___x_1616_ = v___x_1608_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_array_1604_);
lean_ctor_set(v_reuseFailAlloc_1622_, 1, v___x_1614_);
lean_ctor_set(v_reuseFailAlloc_1622_, 2, v_stop_1606_);
v___x_1616_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
lean_object* v___x_1617_; uint8_t v___x_1618_; 
v___x_1617_ = lean_array_fget(v_array_1604_, v_start_1605_);
lean_dec(v_start_1605_);
lean_dec_ref(v_array_1604_);
v___x_1618_ = l_Lean_Expr_hasExprMVar(v___x_1617_);
lean_dec(v___x_1617_);
if (v___x_1618_ == 0)
{
v_a_1601_ = v___x_1616_;
v_b_1602_ = v___x_1612_;
goto _start;
}
else
{
lean_object* v___x_1620_; 
v___x_1620_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_dec_ref_known(v___x_1620_, 1);
v_a_1601_ = v___x_1616_;
v_b_1602_ = v___x_1612_;
goto _start;
}
else
{
lean_dec_ref(v___x_1616_);
return v___x_1620_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg___boxed(lean_object* v_a_1624_, lean_object* v_b_1625_, lean_object* v___y_1626_){
_start:
{
lean_object* v_res_1627_; 
v_res_1627_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(v_a_1624_, v_b_1625_);
return v_res_1627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(lean_object* v_e_1636_, uint8_t v_isMatch_1637_, uint8_t v_root_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_){
_start:
{
lean_object* v___y_1645_; lean_object* v_b_1646_; lean_object* v___x_1657_; 
v___x_1657_ = l_Lean_Meta_DiscrTree_reduceDT(v_e_1636_, v_root_1638_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_);
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_object* v_a_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1820_; 
v_a_1658_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1660_ = v___x_1657_;
v_isShared_1661_ = v_isSharedCheck_1820_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_a_1658_);
lean_dec(v___x_1657_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1820_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___y_1663_; lean_object* v___y_1673_; lean_object* v___y_1674_; lean_object* v___y_1675_; lean_object* v___y_1676_; 
if (v_root_1638_ == 0)
{
lean_object* v___x_1808_; 
lean_inc(v_a_1658_);
v___x_1808_ = l_Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f(v_a_1658_);
if (lean_obj_tag(v___x_1808_) == 1)
{
lean_object* v_val_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1819_; 
lean_del_object(v___x_1660_);
lean_dec(v_a_1658_);
v_val_1809_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1811_ = v___x_1808_;
v_isShared_1812_ = v_isSharedCheck_1819_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_val_1809_);
lean_dec(v___x_1808_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1819_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1814_; 
if (v_isShared_1812_ == 0)
{
lean_ctor_set_tag(v___x_1811_, 2);
v___x_1814_ = v___x_1811_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_val_1809_);
v___x_1814_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1815_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
v___x_1816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1814_);
lean_ctor_set(v___x_1816_, 1, v___x_1815_);
v___x_1817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1816_);
return v___x_1817_;
}
}
}
else
{
lean_dec(v___x_1808_);
v___y_1673_ = v_a_1639_;
v___y_1674_ = v_a_1640_;
v___y_1675_ = v_a_1641_;
v___y_1676_ = v_a_1642_;
goto v___jp_1672_;
}
}
else
{
v___y_1673_ = v_a_1639_;
v___y_1674_ = v_a_1640_;
v___y_1675_ = v_a_1641_;
v___y_1676_ = v_a_1642_;
goto v___jp_1672_;
}
v___jp_1662_:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1670_; 
v___x_1664_ = l_Lean_Expr_getAppNumArgs(v_a_1658_);
lean_inc(v___x_1664_);
v___x_1665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1665_, 0, v___y_1663_);
lean_ctor_set(v___x_1665_, 1, v___x_1664_);
v___x_1666_ = lean_mk_empty_array_with_capacity(v___x_1664_);
lean_dec(v___x_1664_);
v___x_1667_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1658_, v___x_1666_);
v___x_1668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1668_, 0, v___x_1665_);
lean_ctor_set(v___x_1668_, 1, v___x_1667_);
if (v_isShared_1661_ == 0)
{
lean_ctor_set(v___x_1660_, 0, v___x_1668_);
v___x_1670_ = v___x_1660_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v___x_1668_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
v___jp_1672_:
{
lean_object* v___x_1677_; 
v___x_1677_ = l_Lean_Expr_getAppFn(v_a_1658_);
switch(lean_obj_tag(v___x_1677_))
{
case 1:
{
lean_object* v_fvarId_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
lean_del_object(v___x_1660_);
v_fvarId_1678_ = lean_ctor_get(v___x_1677_, 0);
lean_inc(v_fvarId_1678_);
lean_dec_ref_known(v___x_1677_, 1);
v___x_1679_ = l_Lean_Expr_getAppNumArgs(v_a_1658_);
lean_inc(v___x_1679_);
v___x_1680_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1680_, 0, v_fvarId_1678_);
lean_ctor_set(v___x_1680_, 1, v___x_1679_);
v___x_1681_ = lean_mk_empty_array_with_capacity(v___x_1679_);
lean_dec(v___x_1679_);
v___x_1682_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1658_, v___x_1681_);
v___x_1683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1683_, 0, v___x_1680_);
lean_ctor_set(v___x_1683_, 1, v___x_1682_);
v___x_1684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1684_, 0, v___x_1683_);
return v___x_1684_;
}
case 2:
{
lean_del_object(v___x_1660_);
lean_dec(v_a_1658_);
if (v_isMatch_1637_ == 0)
{
lean_object* v_mvarId_1685_; lean_object* v___x_1686_; uint8_t v_isDefEqStuckEx_1687_; 
v_mvarId_1685_ = lean_ctor_get(v___x_1677_, 0);
lean_inc(v_mvarId_1685_);
lean_dec_ref_known(v___x_1677_, 1);
v___x_1686_ = l_Lean_Meta_Context_config(v___y_1673_);
v_isDefEqStuckEx_1687_ = lean_ctor_get_uint8(v___x_1686_, 4);
lean_dec_ref(v___x_1686_);
if (v_isDefEqStuckEx_1687_ == 0)
{
lean_object* v___x_1688_; 
v___x_1688_ = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(v_mvarId_1685_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
if (lean_obj_tag(v___x_1688_) == 0)
{
lean_object* v_a_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1702_; 
v_a_1689_ = lean_ctor_get(v___x_1688_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1688_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1691_ = v___x_1688_;
v_isShared_1692_ = v_isSharedCheck_1702_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_a_1689_);
lean_dec(v___x_1688_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1702_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
uint8_t v___x_1693_; 
v___x_1693_ = lean_unbox(v_a_1689_);
lean_dec(v_a_1689_);
if (v___x_1693_ == 0)
{
lean_object* v___x_1694_; lean_object* v___x_1696_; 
v___x_1694_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__2));
if (v_isShared_1692_ == 0)
{
lean_ctor_set(v___x_1691_, 0, v___x_1694_);
v___x_1696_ = v___x_1691_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v___x_1694_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
else
{
lean_object* v___x_1698_; lean_object* v___x_1700_; 
v___x_1698_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
if (v_isShared_1692_ == 0)
{
lean_ctor_set(v___x_1691_, 0, v___x_1698_);
v___x_1700_ = v___x_1691_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v___x_1698_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
}
else
{
lean_object* v_a_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1710_; 
v_a_1703_ = lean_ctor_get(v___x_1688_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1688_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1705_ = v___x_1688_;
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_a_1703_);
lean_dec(v___x_1688_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1708_; 
if (v_isShared_1706_ == 0)
{
v___x_1708_ = v___x_1705_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_a_1703_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
}
else
{
lean_object* v___x_1711_; lean_object* v___x_1712_; 
lean_dec(v_mvarId_1685_);
v___x_1711_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__2));
v___x_1712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1712_, 0, v___x_1711_);
return v___x_1712_;
}
}
else
{
lean_object* v___x_1713_; lean_object* v___x_1714_; 
lean_dec_ref_known(v___x_1677_, 1);
v___x_1713_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
v___x_1714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1714_, 0, v___x_1713_);
return v___x_1714_;
}
}
case 4:
{
lean_object* v_declName_1715_; lean_object* v___x_1716_; uint8_t v_isDefEqStuckEx_1717_; 
v_declName_1715_ = lean_ctor_get(v___x_1677_, 0);
lean_inc(v_declName_1715_);
lean_dec_ref_known(v___x_1677_, 2);
v___x_1716_ = l_Lean_Meta_Context_config(v___y_1673_);
v_isDefEqStuckEx_1717_ = lean_ctor_get_uint8(v___x_1716_, 4);
lean_dec_ref(v___x_1716_);
if (v_isDefEqStuckEx_1717_ == 0)
{
v___y_1663_ = v_declName_1715_;
goto v___jp_1662_;
}
else
{
uint8_t v___x_1718_; 
v___x_1718_ = l_Lean_Expr_hasExprMVar(v_a_1658_);
if (v___x_1718_ == 0)
{
v___y_1663_ = v_declName_1715_;
goto v___jp_1662_;
}
else
{
lean_object* v___x_1719_; 
lean_inc(v_declName_1715_);
v___x_1719_ = l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0(v_declName_1715_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
if (lean_obj_tag(v___x_1719_) == 0)
{
lean_object* v_a_1720_; uint8_t v___x_1721_; 
v_a_1720_ = lean_ctor_get(v___x_1719_, 0);
lean_inc(v_a_1720_);
lean_dec_ref_known(v___x_1719_, 1);
v___x_1721_ = lean_unbox(v_a_1720_);
lean_dec(v_a_1720_);
if (v___x_1721_ == 0)
{
lean_object* v___x_1722_; lean_object* v_env_1723_; lean_object* v___x_1724_; 
v___x_1722_ = lean_st_ref_get(v___y_1676_);
v_env_1723_ = lean_ctor_get(v___x_1722_, 0);
lean_inc_ref(v_env_1723_);
lean_dec(v___x_1722_);
v___x_1724_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_1723_, v_a_1658_);
if (lean_obj_tag(v___x_1724_) == 1)
{
lean_object* v_val_1725_; lean_object* v_numDiscrs_1726_; lean_object* v_nargs_1727_; lean_object* v_dummy_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
v_val_1725_ = lean_ctor_get(v___x_1724_, 0);
lean_inc(v_val_1725_);
lean_dec_ref_known(v___x_1724_, 1);
v_numDiscrs_1726_ = lean_ctor_get(v_val_1725_, 1);
lean_inc(v_numDiscrs_1726_);
v_nargs_1727_ = l_Lean_Expr_getAppNumArgs(v_a_1658_);
v_dummy_1728_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0);
lean_inc(v_nargs_1727_);
v___x_1729_ = lean_mk_array(v_nargs_1727_, v_dummy_1728_);
v___x_1730_ = lean_unsigned_to_nat(1u);
v___x_1731_ = lean_nat_sub(v_nargs_1727_, v___x_1730_);
lean_dec(v_nargs_1727_);
lean_inc(v_a_1658_);
v___x_1732_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1658_, v___x_1729_, v___x_1731_);
v___x_1733_ = l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(v_val_1725_);
lean_dec(v_val_1725_);
v___x_1734_ = lean_nat_add(v___x_1733_, v_numDiscrs_1726_);
lean_dec(v_numDiscrs_1726_);
v___x_1735_ = l_Array_toSubarray___redArg(v___x_1732_, v___x_1733_, v___x_1734_);
v___x_1736_ = lean_box(0);
v___x_1737_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(v___x_1735_, v___x_1736_);
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_dec_ref_known(v___x_1737_, 1);
v___y_1663_ = v_declName_1715_;
goto v___jp_1662_;
}
else
{
lean_object* v_a_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1745_; 
lean_dec(v_declName_1715_);
lean_del_object(v___x_1660_);
lean_dec(v_a_1658_);
v_a_1738_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1745_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1740_ = v___x_1737_;
v_isShared_1741_ = v_isSharedCheck_1745_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_a_1738_);
lean_dec(v___x_1737_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1745_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___x_1743_; 
if (v_isShared_1741_ == 0)
{
v___x_1743_ = v___x_1740_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_a_1738_);
v___x_1743_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
return v___x_1743_;
}
}
}
}
else
{
lean_object* v___x_1746_; lean_object* v_a_1747_; uint8_t v___x_1748_; 
lean_dec(v___x_1724_);
lean_inc(v_declName_1715_);
v___x_1746_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(v_declName_1715_, v___y_1676_);
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
lean_inc(v_a_1747_);
lean_dec_ref(v___x_1746_);
v___x_1748_ = lean_unbox(v_a_1747_);
lean_dec(v_a_1747_);
if (v___x_1748_ == 0)
{
v___y_1663_ = v_declName_1715_;
goto v___jp_1662_;
}
else
{
lean_object* v___x_1749_; 
v___x_1749_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_dec_ref_known(v___x_1749_, 1);
v___y_1663_ = v_declName_1715_;
goto v___jp_1662_;
}
else
{
lean_object* v_a_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1757_; 
lean_dec(v_declName_1715_);
lean_del_object(v___x_1660_);
lean_dec(v_a_1658_);
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
v_isSharedCheck_1757_ = !lean_is_exclusive(v___x_1749_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1752_ = v___x_1749_;
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_a_1750_);
lean_dec(v___x_1749_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1755_; 
if (v_isShared_1753_ == 0)
{
v___x_1755_ = v___x_1752_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_a_1750_);
v___x_1755_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
return v___x_1755_;
}
}
}
}
}
}
else
{
lean_object* v___x_1758_; 
v___x_1758_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_dec_ref_known(v___x_1758_, 1);
v___y_1663_ = v_declName_1715_;
goto v___jp_1662_;
}
else
{
lean_object* v_a_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1766_; 
lean_dec(v_declName_1715_);
lean_del_object(v___x_1660_);
lean_dec(v_a_1658_);
v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1761_ = v___x_1758_;
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_a_1759_);
lean_dec(v___x_1758_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1764_; 
if (v_isShared_1762_ == 0)
{
v___x_1764_ = v___x_1761_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_a_1759_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
}
}
else
{
lean_object* v_a_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1774_; 
lean_dec(v_declName_1715_);
lean_del_object(v___x_1660_);
lean_dec(v_a_1658_);
v_a_1767_ = lean_ctor_get(v___x_1719_, 0);
v_isSharedCheck_1774_ = !lean_is_exclusive(v___x_1719_);
if (v_isSharedCheck_1774_ == 0)
{
v___x_1769_ = v___x_1719_;
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_a_1767_);
lean_dec(v___x_1719_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1772_; 
if (v_isShared_1770_ == 0)
{
v___x_1772_ = v___x_1769_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v_a_1767_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
return v___x_1772_;
}
}
}
}
}
}
case 7:
{
lean_object* v_binderType_1775_; lean_object* v_body_1776_; uint8_t v___x_1777_; 
lean_del_object(v___x_1660_);
lean_dec(v_a_1658_);
v_binderType_1775_ = lean_ctor_get(v___x_1677_, 1);
lean_inc_ref(v_binderType_1775_);
v_body_1776_ = lean_ctor_get(v___x_1677_, 2);
lean_inc_ref(v_body_1776_);
lean_dec_ref_known(v___x_1677_, 3);
v___x_1777_ = l_Lean_Expr_hasLooseBVars(v_body_1776_);
if (v___x_1777_ == 0)
{
v___y_1645_ = v_binderType_1775_;
v_b_1646_ = v_body_1776_;
goto v___jp_1644_;
}
else
{
lean_object* v___x_1778_; 
v___x_1778_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(v_body_1776_, v___y_1675_, v___y_1676_);
if (lean_obj_tag(v___x_1778_) == 0)
{
lean_object* v_a_1779_; 
v_a_1779_ = lean_ctor_get(v___x_1778_, 0);
lean_inc(v_a_1779_);
lean_dec_ref_known(v___x_1778_, 1);
v___y_1645_ = v_binderType_1775_;
v_b_1646_ = v_a_1779_;
goto v___jp_1644_;
}
else
{
lean_object* v_a_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1787_; 
lean_dec_ref(v_binderType_1775_);
v_a_1780_ = lean_ctor_get(v___x_1778_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1782_ = v___x_1778_;
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_a_1780_);
lean_dec(v___x_1778_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1785_; 
if (v_isShared_1783_ == 0)
{
v___x_1785_ = v___x_1782_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_a_1780_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
}
}
case 9:
{
lean_object* v_a_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
lean_del_object(v___x_1660_);
lean_dec(v_a_1658_);
v_a_1788_ = lean_ctor_get(v___x_1677_, 0);
lean_inc_ref(v_a_1788_);
lean_dec_ref_known(v___x_1677_, 1);
v___x_1789_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1789_, 0, v_a_1788_);
v___x_1790_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
v___x_1791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1791_, 0, v___x_1789_);
lean_ctor_set(v___x_1791_, 1, v___x_1790_);
v___x_1792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1792_, 0, v___x_1791_);
return v___x_1792_;
}
case 11:
{
lean_object* v_typeName_1793_; lean_object* v_idx_1794_; lean_object* v_struct_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
lean_del_object(v___x_1660_);
v_typeName_1793_ = lean_ctor_get(v___x_1677_, 0);
lean_inc(v_typeName_1793_);
v_idx_1794_ = lean_ctor_get(v___x_1677_, 1);
lean_inc(v_idx_1794_);
v_struct_1795_ = lean_ctor_get(v___x_1677_, 2);
lean_inc_ref(v_struct_1795_);
lean_dec_ref_known(v___x_1677_, 3);
v___x_1796_ = l_Lean_Expr_getAppNumArgs(v_a_1658_);
lean_inc(v___x_1796_);
v___x_1797_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_1797_, 0, v_typeName_1793_);
lean_ctor_set(v___x_1797_, 1, v_idx_1794_);
lean_ctor_set(v___x_1797_, 2, v___x_1796_);
v___x_1798_ = lean_unsigned_to_nat(1u);
v___x_1799_ = lean_mk_empty_array_with_capacity(v___x_1798_);
v___x_1800_ = lean_array_push(v___x_1799_, v_struct_1795_);
v___x_1801_ = lean_mk_empty_array_with_capacity(v___x_1796_);
lean_dec(v___x_1796_);
v___x_1802_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1658_, v___x_1801_);
v___x_1803_ = l_Array_append___redArg(v___x_1800_, v___x_1802_);
lean_dec_ref(v___x_1802_);
v___x_1804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1804_, 0, v___x_1797_);
lean_ctor_set(v___x_1804_, 1, v___x_1803_);
v___x_1805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1805_, 0, v___x_1804_);
return v___x_1805_;
}
default: 
{
lean_object* v___x_1806_; lean_object* v___x_1807_; 
lean_dec_ref(v___x_1677_);
lean_del_object(v___x_1660_);
lean_dec(v_a_1658_);
v___x_1806_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
v___x_1807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1806_);
return v___x_1807_;
}
}
}
}
}
else
{
lean_object* v_a_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1828_; 
v_a_1821_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1823_ = v___x_1657_;
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_a_1821_);
lean_dec(v___x_1657_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1826_; 
if (v_isShared_1824_ == 0)
{
v___x_1826_ = v___x_1823_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_a_1821_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
}
v___jp_1644_:
{
uint8_t v___x_1647_; 
v___x_1647_ = l_Lean_Expr_hasLooseBVars(v_b_1646_);
if (v___x_1647_ == 0)
{
lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1648_ = lean_box(5);
v___x_1649_ = lean_unsigned_to_nat(2u);
v___x_1650_ = lean_mk_empty_array_with_capacity(v___x_1649_);
v___x_1651_ = lean_array_push(v___x_1650_, v___y_1645_);
v___x_1652_ = lean_array_push(v___x_1651_, v_b_1646_);
v___x_1653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1648_);
lean_ctor_set(v___x_1653_, 1, v___x_1652_);
v___x_1654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1653_);
return v___x_1654_;
}
else
{
lean_object* v___x_1655_; lean_object* v___x_1656_; 
lean_dec_ref(v_b_1646_);
lean_dec_ref(v___y_1645_);
v___x_1655_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
v___x_1656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1655_);
return v___x_1656_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___boxed(lean_object* v_e_1829_, lean_object* v_isMatch_1830_, lean_object* v_root_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_){
_start:
{
uint8_t v_isMatch_boxed_1837_; uint8_t v_root_boxed_1838_; lean_object* v_res_1839_; 
v_isMatch_boxed_1837_ = lean_unbox(v_isMatch_1830_);
v_root_boxed_1838_ = lean_unbox(v_root_1831_);
v_res_1839_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_1829_, v_isMatch_boxed_1837_, v_root_boxed_1838_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_);
lean_dec(v_a_1835_);
lean_dec_ref(v_a_1834_);
lean_dec(v_a_1833_);
lean_dec_ref(v_a_1832_);
return v_res_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0(lean_object* v_declName_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_){
_start:
{
lean_object* v___x_1846_; 
v___x_1846_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(v_declName_1840_, v___y_1844_);
return v___x_1846_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___boxed(lean_object* v_declName_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_){
_start:
{
lean_object* v_res_1853_; 
v_res_1853_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0(v_declName_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_);
lean_dec(v___y_1851_);
lean_dec_ref(v___y_1850_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
return v_res_1853_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1(lean_object* v_inst_1854_, lean_object* v_R_1855_, lean_object* v_a_1856_, lean_object* v_b_1857_, lean_object* v_c_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_){
_start:
{
lean_object* v___x_1864_; 
v___x_1864_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(v_a_1856_, v_b_1857_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___boxed(lean_object* v_inst_1865_, lean_object* v_R_1866_, lean_object* v_a_1867_, lean_object* v_b_1868_, lean_object* v_c_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_){
_start:
{
lean_object* v_res_1875_; 
v_res_1875_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1(v_inst_1865_, v_R_1866_, v_a_1867_, v_b_1868_, v_c_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_);
lean_dec(v___y_1873_);
lean_dec_ref(v___y_1872_);
lean_dec(v___y_1871_);
lean_dec_ref(v___y_1870_);
return v_res_1875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getMatchKeyArgs(lean_object* v_e_1876_, uint8_t v_root_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_){
_start:
{
uint8_t v___x_1883_; lean_object* v___x_1884_; 
v___x_1883_ = 1;
v___x_1884_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_1876_, v___x_1883_, v_root_1877_, v_a_1878_, v_a_1879_, v_a_1880_, v_a_1881_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getMatchKeyArgs___boxed(lean_object* v_e_1885_, lean_object* v_root_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_){
_start:
{
uint8_t v_root_boxed_1892_; lean_object* v_res_1893_; 
v_root_boxed_1892_ = lean_unbox(v_root_1886_);
v_res_1893_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getMatchKeyArgs(v_e_1885_, v_root_boxed_1892_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
lean_dec(v_a_1890_);
lean_dec_ref(v_a_1889_);
lean_dec(v_a_1888_);
lean_dec_ref(v_a_1887_);
return v_res_1893_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1(void){
_start:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; 
v___x_1896_ = lean_box(0);
v___x_1897_ = lean_unsigned_to_nat(16u);
v___x_1898_ = lean_mk_array(v___x_1897_, v___x_1896_);
return v___x_1898_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2(void){
_start:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1899_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1);
v___x_1900_ = lean_unsigned_to_nat(0u);
v___x_1901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1900_);
lean_ctor_set(v___x_1901_, 1, v___x_1899_);
return v___x_1901_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__4(void){
_start:
{
lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1904_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__3));
v___x_1905_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_1906_ = lean_unsigned_to_nat(0u);
v___x_1907_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0));
v___x_1908_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1907_);
lean_ctor_set(v___x_1908_, 1, v___x_1906_);
lean_ctor_set(v___x_1908_, 2, v___x_1905_);
lean_ctor_set(v___x_1908_, 3, v___x_1904_);
return v___x_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default(lean_object* v_00_u03b1_1909_){
_start:
{
lean_object* v___x_1910_; 
v___x_1910_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__4, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__4);
return v___x_1910_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0(void){
_start:
{
lean_object* v___x_1911_; 
v___x_1911_ = l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default(lean_box(0));
return v___x_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie(lean_object* v_a_1912_){
_start:
{
lean_object* v___x_1913_; 
v___x_1913_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0);
return v___x_1913_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__1(void){
_start:
{
lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1916_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_1917_ = lean_unsigned_to_nat(0u);
v___x_1918_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_1919_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1918_);
lean_ctor_set(v___x_1919_, 1, v___x_1917_);
lean_ctor_set(v___x_1919_, 2, v___x_1916_);
lean_ctor_set(v___x_1919_, 3, v___x_1918_);
return v___x_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie(lean_object* v_00_u03b1_1920_){
_start:
{
lean_object* v___x_1921_; 
v___x_1921_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__1, &l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__1);
return v___x_1921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Trie_pushPending___redArg(lean_object* v_x_1922_, lean_object* v_x_1923_){
_start:
{
lean_object* v_values_1924_; lean_object* v_star_1925_; lean_object* v_children_1926_; lean_object* v_pending_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1935_; 
v_values_1924_ = lean_ctor_get(v_x_1922_, 0);
v_star_1925_ = lean_ctor_get(v_x_1922_, 1);
v_children_1926_ = lean_ctor_get(v_x_1922_, 2);
v_pending_1927_ = lean_ctor_get(v_x_1922_, 3);
v_isSharedCheck_1935_ = !lean_is_exclusive(v_x_1922_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1929_ = v_x_1922_;
v_isShared_1930_ = v_isSharedCheck_1935_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_pending_1927_);
lean_inc(v_children_1926_);
lean_inc(v_star_1925_);
lean_inc(v_values_1924_);
lean_dec(v_x_1922_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1935_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1931_; lean_object* v___x_1933_; 
v___x_1931_ = lean_array_push(v_pending_1927_, v_x_1923_);
if (v_isShared_1930_ == 0)
{
lean_ctor_set(v___x_1929_, 3, v___x_1931_);
v___x_1933_ = v___x_1929_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_values_1924_);
lean_ctor_set(v_reuseFailAlloc_1934_, 1, v_star_1925_);
lean_ctor_set(v_reuseFailAlloc_1934_, 2, v_children_1926_);
lean_ctor_set(v_reuseFailAlloc_1934_, 3, v___x_1931_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
return v___x_1933_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Trie_pushPending(lean_object* v_00_u03b1_1936_, lean_object* v_x_1937_, lean_object* v_x_1938_){
_start:
{
lean_object* v___x_1939_; 
v___x_1939_ = l_Lean_Meta_LazyDiscrTree_Trie_pushPending___redArg(v_x_1937_, v_x_1938_);
return v___x_1939_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; 
v___x_1940_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0);
v___x_1941_ = lean_unsigned_to_nat(1u);
v___x_1942_ = lean_mk_empty_array_with_capacity(v___x_1941_);
v___x_1943_ = lean_array_push(v___x_1942_, v___x_1940_);
return v___x_1943_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__1(void){
_start:
{
lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; 
v___x_1944_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_1945_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0);
v___x_1946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1946_, 0, v___x_1945_);
lean_ctor_set(v___x_1946_, 1, v___x_1944_);
return v___x_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabited(lean_object* v_00_u03b1_1947_){
_start:
{
lean_object* v___x_1948_; 
v___x_1948_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabited___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabited___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__1);
return v___x_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(lean_object* v_msgData_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_){
_start:
{
lean_object* v___x_1955_; lean_object* v_env_1956_; lean_object* v___x_1957_; lean_object* v_mctx_1958_; lean_object* v_lctx_1959_; lean_object* v_options_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; 
v___x_1955_ = lean_st_ref_get(v___y_1953_);
v_env_1956_ = lean_ctor_get(v___x_1955_, 0);
lean_inc_ref(v_env_1956_);
lean_dec(v___x_1955_);
v___x_1957_ = lean_st_ref_get(v___y_1951_);
v_mctx_1958_ = lean_ctor_get(v___x_1957_, 0);
lean_inc_ref(v_mctx_1958_);
lean_dec(v___x_1957_);
v_lctx_1959_ = lean_ctor_get(v___y_1950_, 2);
v_options_1960_ = lean_ctor_get(v___y_1952_, 2);
lean_inc_ref(v_options_1960_);
lean_inc_ref(v_lctx_1959_);
v___x_1961_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1961_, 0, v_env_1956_);
lean_ctor_set(v___x_1961_, 1, v_mctx_1958_);
lean_ctor_set(v___x_1961_, 2, v_lctx_1959_);
lean_ctor_set(v___x_1961_, 3, v_options_1960_);
v___x_1962_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1961_);
lean_ctor_set(v___x_1962_, 1, v_msgData_1949_);
v___x_1963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1963_, 0, v___x_1962_);
return v___x_1963_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0___boxed(lean_object* v_msgData_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_){
_start:
{
lean_object* v_res_1970_; 
v_res_1970_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(v_msgData_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
return v_res_1970_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(lean_object* v_msg_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_){
_start:
{
lean_object* v_ref_1977_; lean_object* v___x_1978_; lean_object* v_a_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_1987_; 
v_ref_1977_ = lean_ctor_get(v___y_1974_, 5);
v___x_1978_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(v_msg_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
v_a_1979_ = lean_ctor_get(v___x_1978_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1981_ = v___x_1978_;
v_isShared_1982_ = v_isSharedCheck_1987_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_a_1979_);
lean_dec(v___x_1978_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_1987_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___x_1983_; lean_object* v___x_1985_; 
lean_inc(v_ref_1977_);
v___x_1983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1983_, 0, v_ref_1977_);
lean_ctor_set(v___x_1983_, 1, v_a_1979_);
if (v_isShared_1982_ == 0)
{
lean_ctor_set_tag(v___x_1981_, 1);
lean_ctor_set(v___x_1981_, 0, v___x_1983_);
v___x_1985_ = v___x_1981_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v___x_1983_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg___boxed(lean_object* v_msg_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_){
_start:
{
lean_object* v_res_1994_; 
v_res_1994_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(v_msg_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
lean_dec(v___y_1990_);
lean_dec_ref(v___y_1989_);
return v_res_1994_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1(void){
_start:
{
lean_object* v___x_1996_; lean_object* v___x_1997_; 
v___x_1996_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_pushArgs___closed__0));
v___x_1997_ = l_Lean_stringToMessageData(v___x_1996_);
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushArgs(uint8_t v_root_1998_, lean_object* v_todo_1999_, lean_object* v_e_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_){
_start:
{
uint8_t v___x_2006_; 
v___x_2006_ = l_Lean_Meta_DiscrTree_hasNoindexAnnotation(v_e_2000_);
if (v___x_2006_ == 0)
{
lean_object* v___x_2007_; 
v___x_2007_ = l_Lean_Meta_DiscrTree_reduceDT(v_e_2000_, v_root_1998_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2147_; 
v_a_2008_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2010_ = v___x_2007_;
v_isShared_2011_ = v_isSharedCheck_2147_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_dec(v___x_2007_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2147_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v_v_2013_; lean_object* v___x_2019_; lean_object* v_k_2021_; lean_object* v_nargs_2022_; lean_object* v_todo_2023_; lean_object* v___y_2024_; lean_object* v___y_2025_; lean_object* v___y_2026_; lean_object* v___y_2027_; 
v___x_2019_ = l_Lean_Expr_getAppFn(v_a_2008_);
switch(lean_obj_tag(v___x_2019_))
{
case 9:
{
lean_object* v_a_2066_; 
lean_dec(v_a_2008_);
v_a_2066_ = lean_ctor_get(v___x_2019_, 0);
lean_inc_ref(v_a_2066_);
lean_dec_ref_known(v___x_2019_, 1);
v_v_2013_ = v_a_2066_;
goto v___jp_2012_;
}
case 4:
{
lean_object* v_declName_2067_; lean_object* v___y_2069_; lean_object* v___y_2070_; lean_object* v___y_2071_; lean_object* v___y_2072_; 
v_declName_2067_ = lean_ctor_get(v___x_2019_, 0);
lean_inc(v_declName_2067_);
if (v_root_1998_ == 0)
{
lean_object* v___x_2075_; 
lean_inc(v_a_2008_);
v___x_2075_ = l_Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f(v_a_2008_);
if (lean_obj_tag(v___x_2075_) == 1)
{
lean_object* v_val_2076_; 
lean_dec_ref_known(v___x_2019_, 2);
lean_dec(v_declName_2067_);
lean_dec(v_a_2008_);
v_val_2076_ = lean_ctor_get(v___x_2075_, 0);
lean_inc(v_val_2076_);
lean_dec_ref_known(v___x_2075_, 1);
v_v_2013_ = v_val_2076_;
goto v___jp_2012_;
}
else
{
lean_object* v___x_2077_; 
lean_dec(v___x_2075_);
lean_del_object(v___x_2010_);
v___x_2077_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset(v_declName_2067_, v_a_2008_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v_a_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2088_; 
v_a_2078_ = lean_ctor_get(v___x_2077_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2080_ = v___x_2077_;
v_isShared_2081_ = v_isSharedCheck_2088_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_a_2078_);
lean_dec(v___x_2077_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2088_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
uint8_t v___x_2082_; 
v___x_2082_ = lean_unbox(v_a_2078_);
lean_dec(v_a_2078_);
if (v___x_2082_ == 0)
{
lean_del_object(v___x_2080_);
v___y_2069_ = v_a_2001_;
v___y_2070_ = v_a_2002_;
v___y_2071_ = v_a_2003_;
v___y_2072_ = v_a_2004_;
goto v___jp_2068_;
}
else
{
lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2086_; 
lean_dec_ref_known(v___x_2019_, 2);
lean_dec(v_declName_2067_);
lean_dec(v_a_2008_);
v___x_2083_ = lean_box(3);
v___x_2084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2083_);
lean_ctor_set(v___x_2084_, 1, v_todo_1999_);
if (v_isShared_2081_ == 0)
{
lean_ctor_set(v___x_2080_, 0, v___x_2084_);
v___x_2086_ = v___x_2080_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v___x_2084_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
}
else
{
lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2096_; 
lean_dec_ref_known(v___x_2019_, 2);
lean_dec(v_declName_2067_);
lean_dec(v_a_2008_);
lean_dec_ref(v_todo_1999_);
v_a_2089_ = lean_ctor_get(v___x_2077_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2091_ = v___x_2077_;
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_2077_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2094_; 
if (v_isShared_2092_ == 0)
{
v___x_2094_ = v___x_2091_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_a_2089_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
}
}
else
{
lean_del_object(v___x_2010_);
v___y_2069_ = v_a_2001_;
v___y_2070_ = v_a_2002_;
v___y_2071_ = v_a_2003_;
v___y_2072_ = v_a_2004_;
goto v___jp_2068_;
}
v___jp_2068_:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; 
v___x_2073_ = l_Lean_Expr_getAppNumArgs(v_a_2008_);
lean_inc(v___x_2073_);
v___x_2074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2074_, 0, v_declName_2067_);
lean_ctor_set(v___x_2074_, 1, v___x_2073_);
v_k_2021_ = v___x_2074_;
v_nargs_2022_ = v___x_2073_;
v_todo_2023_ = v_todo_1999_;
v___y_2024_ = v___y_2069_;
v___y_2025_ = v___y_2070_;
v___y_2026_ = v___y_2071_;
v___y_2027_ = v___y_2072_;
goto v___jp_2020_;
}
}
case 11:
{
lean_object* v_typeName_2097_; lean_object* v_idx_2098_; lean_object* v_struct_2099_; lean_object* v___x_2100_; lean_object* v___y_2102_; lean_object* v_env_2106_; uint8_t v___x_2107_; 
lean_del_object(v___x_2010_);
v_typeName_2097_ = lean_ctor_get(v___x_2019_, 0);
lean_inc(v_typeName_2097_);
v_idx_2098_ = lean_ctor_get(v___x_2019_, 1);
lean_inc(v_idx_2098_);
v_struct_2099_ = lean_ctor_get(v___x_2019_, 2);
lean_inc_ref(v_struct_2099_);
v___x_2100_ = lean_st_ref_get(v_a_2004_);
v_env_2106_ = lean_ctor_get(v___x_2100_, 0);
lean_inc_ref(v_env_2106_);
lean_dec(v___x_2100_);
v___x_2107_ = l_Lean_isClass(v_env_2106_, v_typeName_2097_);
if (v___x_2107_ == 0)
{
v___y_2102_ = v_struct_2099_;
goto v___jp_2101_;
}
else
{
lean_object* v___x_2108_; 
v___x_2108_ = l_Lean_Meta_DiscrTree_mkNoindexAnnotation(v_struct_2099_);
v___y_2102_ = v___x_2108_;
goto v___jp_2101_;
}
v___jp_2101_:
{
lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___x_2103_ = l_Lean_Expr_getAppNumArgs(v_a_2008_);
lean_inc(v___x_2103_);
v___x_2104_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_2104_, 0, v_typeName_2097_);
lean_ctor_set(v___x_2104_, 1, v_idx_2098_);
lean_ctor_set(v___x_2104_, 2, v___x_2103_);
v___x_2105_ = lean_array_push(v_todo_1999_, v___y_2102_);
v_k_2021_ = v___x_2104_;
v_nargs_2022_ = v___x_2103_;
v_todo_2023_ = v___x_2105_;
v___y_2024_ = v_a_2001_;
v___y_2025_ = v_a_2002_;
v___y_2026_ = v_a_2003_;
v___y_2027_ = v_a_2004_;
goto v___jp_2020_;
}
}
case 1:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; 
lean_dec_ref_known(v___x_2019_, 1);
lean_del_object(v___x_2010_);
lean_dec(v_a_2008_);
v___x_2109_ = lean_box(3);
v___x_2110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2109_);
lean_ctor_set(v___x_2110_, 1, v_todo_1999_);
v___x_2111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2111_, 0, v___x_2110_);
return v___x_2111_;
}
case 2:
{
lean_object* v_mvarId_2112_; lean_object* v___x_2113_; uint8_t v___x_2114_; 
lean_del_object(v___x_2010_);
lean_dec(v_a_2008_);
v_mvarId_2112_ = lean_ctor_get(v___x_2019_, 0);
lean_inc(v_mvarId_2112_);
lean_dec_ref_known(v___x_2019_, 1);
v___x_2113_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_tmpMVarId));
v___x_2114_ = l_Lean_instBEqMVarId_beq(v_mvarId_2112_, v___x_2113_);
lean_dec(v_mvarId_2112_);
if (v___x_2114_ == 0)
{
lean_object* v___x_2115_; lean_object* v___x_2116_; 
lean_dec_ref(v_todo_1999_);
v___x_2115_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1, &l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1);
v___x_2116_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(v___x_2115_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_);
return v___x_2116_;
}
else
{
lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2117_ = lean_box(3);
v___x_2118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2117_);
lean_ctor_set(v___x_2118_, 1, v_todo_1999_);
v___x_2119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2118_);
return v___x_2119_;
}
}
case 7:
{
lean_object* v_binderType_2120_; lean_object* v_body_2121_; lean_object* v_b_2123_; uint8_t v___x_2133_; 
lean_del_object(v___x_2010_);
lean_dec(v_a_2008_);
v_binderType_2120_ = lean_ctor_get(v___x_2019_, 1);
lean_inc_ref(v_binderType_2120_);
v_body_2121_ = lean_ctor_get(v___x_2019_, 2);
lean_inc_ref(v_body_2121_);
lean_dec_ref_known(v___x_2019_, 3);
v___x_2133_ = l_Lean_Expr_hasLooseBVars(v_body_2121_);
if (v___x_2133_ == 0)
{
v_b_2123_ = v_body_2121_;
goto v___jp_2122_;
}
else
{
lean_object* v___x_2134_; 
v___x_2134_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(v_body_2121_, v_a_2003_, v_a_2004_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_object* v_a_2135_; 
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
lean_inc(v_a_2135_);
lean_dec_ref_known(v___x_2134_, 1);
v_b_2123_ = v_a_2135_;
goto v___jp_2122_;
}
else
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2143_; 
lean_dec_ref(v_binderType_2120_);
lean_dec_ref(v_todo_1999_);
v_a_2136_ = lean_ctor_get(v___x_2134_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2138_ = v___x_2134_;
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2134_);
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
v___jp_2122_:
{
uint8_t v___x_2124_; 
v___x_2124_ = l_Lean_Expr_hasLooseBVars(v_b_2123_);
if (v___x_2124_ == 0)
{
lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
v___x_2125_ = lean_box(5);
v___x_2126_ = lean_array_push(v_todo_1999_, v_binderType_2120_);
v___x_2127_ = lean_array_push(v___x_2126_, v_b_2123_);
v___x_2128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2125_);
lean_ctor_set(v___x_2128_, 1, v___x_2127_);
v___x_2129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2128_);
return v___x_2129_;
}
else
{
lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
lean_dec_ref(v_b_2123_);
lean_dec_ref(v_binderType_2120_);
v___x_2130_ = lean_box(4);
v___x_2131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2130_);
lean_ctor_set(v___x_2131_, 1, v_todo_1999_);
v___x_2132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2131_);
return v___x_2132_;
}
}
}
default: 
{
lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
lean_dec_ref(v___x_2019_);
lean_del_object(v___x_2010_);
lean_dec(v_a_2008_);
v___x_2144_ = lean_box(4);
v___x_2145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2145_, 0, v___x_2144_);
lean_ctor_set(v___x_2145_, 1, v_todo_1999_);
v___x_2146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2146_, 0, v___x_2145_);
return v___x_2146_;
}
}
v___jp_2012_:
{
lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2017_; 
v___x_2014_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2014_, 0, v_v_2013_);
v___x_2015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2015_, 0, v___x_2014_);
lean_ctor_set(v___x_2015_, 1, v_todo_1999_);
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 0, v___x_2015_);
v___x_2017_ = v___x_2010_;
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
v___jp_2020_:
{
lean_object* v___x_2028_; 
lean_inc(v_nargs_2022_);
v___x_2028_ = l_Lean_Meta_getFunInfoNArgs(v___x_2019_, v_nargs_2022_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
if (lean_obj_tag(v___x_2028_) == 0)
{
lean_object* v_a_2029_; lean_object* v_paramInfo_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2056_; 
v_a_2029_ = lean_ctor_get(v___x_2028_, 0);
lean_inc(v_a_2029_);
lean_dec_ref_known(v___x_2028_, 1);
v_paramInfo_2030_ = lean_ctor_get(v_a_2029_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v_a_2029_);
if (v_isSharedCheck_2056_ == 0)
{
lean_object* v_unused_2057_; 
v_unused_2057_ = lean_ctor_get(v_a_2029_, 1);
lean_dec(v_unused_2057_);
v___x_2032_ = v_a_2029_;
v_isShared_2033_ = v_isSharedCheck_2056_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_paramInfo_2030_);
lean_dec(v_a_2029_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2056_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___x_2034_ = lean_unsigned_to_nat(1u);
v___x_2035_ = lean_nat_sub(v_nargs_2022_, v___x_2034_);
lean_dec(v_nargs_2022_);
v___x_2036_ = l_Lean_Meta_LazyDiscrTree_MatchClone_pushArgsAux(v_paramInfo_2030_, v___x_2035_, v_a_2008_, v_todo_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
lean_dec_ref(v_paramInfo_2030_);
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_object* v_a_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2047_; 
v_a_2037_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2039_ = v___x_2036_;
v_isShared_2040_ = v_isSharedCheck_2047_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_a_2037_);
lean_dec(v___x_2036_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2047_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2042_; 
if (v_isShared_2033_ == 0)
{
lean_ctor_set(v___x_2032_, 1, v_a_2037_);
lean_ctor_set(v___x_2032_, 0, v_k_2021_);
v___x_2042_ = v___x_2032_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_k_2021_);
lean_ctor_set(v_reuseFailAlloc_2046_, 1, v_a_2037_);
v___x_2042_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
lean_object* v___x_2044_; 
if (v_isShared_2040_ == 0)
{
lean_ctor_set(v___x_2039_, 0, v___x_2042_);
v___x_2044_ = v___x_2039_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v___x_2042_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
}
else
{
lean_object* v_a_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2055_; 
lean_del_object(v___x_2032_);
lean_dec(v_k_2021_);
v_a_2048_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2055_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2055_ == 0)
{
v___x_2050_ = v___x_2036_;
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_a_2048_);
lean_dec(v___x_2036_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___x_2053_; 
if (v_isShared_2051_ == 0)
{
v___x_2053_ = v___x_2050_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_a_2048_);
v___x_2053_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
return v___x_2053_;
}
}
}
}
}
else
{
lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2065_; 
lean_dec_ref(v_todo_2023_);
lean_dec(v_nargs_2022_);
lean_dec(v_k_2021_);
lean_dec(v_a_2008_);
v_a_2058_ = lean_ctor_get(v___x_2028_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2028_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2060_ = v___x_2028_;
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_2028_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2063_; 
if (v_isShared_2061_ == 0)
{
v___x_2063_ = v___x_2060_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_a_2058_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
}
}
}
}
else
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
lean_dec_ref(v_todo_1999_);
v_a_2148_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2150_ = v___x_2007_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2007_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2153_; 
if (v_isShared_2151_ == 0)
{
v___x_2153_ = v___x_2150_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_a_2148_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
}
}
else
{
lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
lean_dec_ref(v_e_2000_);
v___x_2156_ = lean_box(3);
v___x_2157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2156_);
lean_ctor_set(v___x_2157_, 1, v_todo_1999_);
v___x_2158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2157_);
return v___x_2158_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushArgs___boxed(lean_object* v_root_2159_, lean_object* v_todo_2160_, lean_object* v_e_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_){
_start:
{
uint8_t v_root_boxed_2167_; lean_object* v_res_2168_; 
v_root_boxed_2167_ = lean_unbox(v_root_2159_);
v_res_2168_ = l_Lean_Meta_LazyDiscrTree_pushArgs(v_root_boxed_2167_, v_todo_2160_, v_e_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_);
lean_dec(v_a_2165_);
lean_dec_ref(v_a_2164_);
lean_dec(v_a_2163_);
lean_dec_ref(v_a_2162_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0(lean_object* v_00_u03b1_2169_, lean_object* v_msg_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_){
_start:
{
lean_object* v___x_2176_; 
v___x_2176_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(v_msg_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___boxed(lean_object* v_00_u03b1_2177_, lean_object* v_msg_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_){
_start:
{
lean_object* v_res_2184_; 
v_res_2184_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0(v_00_u03b1_2177_, v_msg_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
lean_dec(v___y_2180_);
lean_dec_ref(v___y_2179_);
return v_res_2184_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_initCapacity(void){
_start:
{
lean_object* v___x_2185_; 
v___x_2185_ = lean_unsigned_to_nat(8u);
return v___x_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_rootKey(lean_object* v_e_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_){
_start:
{
uint8_t v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; 
v___x_2192_ = 1;
v___x_2193_ = lean_unsigned_to_nat(8u);
v___x_2194_ = lean_mk_empty_array_with_capacity(v___x_2193_);
v___x_2195_ = l_Lean_Meta_LazyDiscrTree_pushArgs(v___x_2192_, v___x_2194_, v_e_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_);
return v___x_2195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_rootKey___boxed(lean_object* v_e_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_){
_start:
{
lean_object* v_res_2202_; 
v_res_2202_ = l_Lean_Meta_LazyDiscrTree_rootKey(v_e_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_);
lean_dec(v_a_2200_);
lean_dec_ref(v_a_2199_);
lean_dec(v_a_2198_);
lean_dec_ref(v_a_2197_);
return v_res_2202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_buildPath(lean_object* v_op_2203_, uint8_t v_root_2204_, lean_object* v_todo_2205_, lean_object* v_keys_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_){
_start:
{
lean_object* v___x_2212_; lean_object* v___x_2213_; uint8_t v___x_2214_; 
v___x_2212_ = lean_array_get_size(v_todo_2205_);
v___x_2213_ = lean_unsigned_to_nat(0u);
v___x_2214_ = lean_nat_dec_eq(v___x_2212_, v___x_2213_);
if (v___x_2214_ == 0)
{
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v_e_2218_; lean_object* v_todo_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2215_ = l_Lean_instInhabitedExpr;
v___x_2216_ = lean_unsigned_to_nat(1u);
v___x_2217_ = lean_nat_sub(v___x_2212_, v___x_2216_);
v_e_2218_ = lean_array_get(v___x_2215_, v_todo_2205_, v___x_2217_);
lean_dec(v___x_2217_);
v_todo_2219_ = lean_array_pop(v_todo_2205_);
v___x_2220_ = lean_box(v_root_2204_);
lean_inc_ref(v_op_2203_);
lean_inc(v_a_2210_);
lean_inc_ref(v_a_2209_);
lean_inc(v_a_2208_);
lean_inc_ref(v_a_2207_);
v___x_2221_ = lean_apply_8(v_op_2203_, v___x_2220_, v_todo_2219_, v_e_2218_, v_a_2207_, v_a_2208_, v_a_2209_, v_a_2210_, lean_box(0));
if (lean_obj_tag(v___x_2221_) == 0)
{
lean_object* v_a_2222_; lean_object* v_fst_2223_; lean_object* v_snd_2224_; lean_object* v___x_2225_; 
v_a_2222_ = lean_ctor_get(v___x_2221_, 0);
lean_inc(v_a_2222_);
lean_dec_ref_known(v___x_2221_, 1);
v_fst_2223_ = lean_ctor_get(v_a_2222_, 0);
lean_inc(v_fst_2223_);
v_snd_2224_ = lean_ctor_get(v_a_2222_, 1);
lean_inc(v_snd_2224_);
lean_dec(v_a_2222_);
v___x_2225_ = lean_array_push(v_keys_2206_, v_fst_2223_);
v_root_2204_ = v___x_2214_;
v_todo_2205_ = v_snd_2224_;
v_keys_2206_ = v___x_2225_;
goto _start;
}
else
{
lean_object* v_a_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2234_; 
lean_dec_ref(v_keys_2206_);
lean_dec_ref(v_op_2203_);
v_a_2227_ = lean_ctor_get(v___x_2221_, 0);
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_2221_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2229_ = v___x_2221_;
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_a_2227_);
lean_dec(v___x_2221_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2232_; 
if (v_isShared_2230_ == 0)
{
v___x_2232_ = v___x_2229_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v_a_2227_);
v___x_2232_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
return v___x_2232_;
}
}
}
}
else
{
lean_object* v___x_2235_; 
lean_dec_ref(v_todo_2205_);
lean_dec_ref(v_op_2203_);
v___x_2235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2235_, 0, v_keys_2206_);
return v___x_2235_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_buildPath___boxed(lean_object* v_op_2236_, lean_object* v_root_2237_, lean_object* v_todo_2238_, lean_object* v_keys_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_){
_start:
{
uint8_t v_root_boxed_2245_; lean_object* v_res_2246_; 
v_root_boxed_2245_ = lean_unbox(v_root_2237_);
v_res_2246_ = l_Lean_Meta_LazyDiscrTree_buildPath(v_op_2236_, v_root_boxed_2245_, v_todo_2238_, v_keys_2239_, v_a_2240_, v_a_2241_, v_a_2242_, v_a_2243_);
lean_dec(v_a_2243_);
lean_dec_ref(v_a_2242_);
lean_dec(v_a_2241_);
lean_dec_ref(v_a_2240_);
return v_res_2246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_patternPath(lean_object* v_e_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_){
_start:
{
lean_object* v_op_2254_; lean_object* v___x_2255_; lean_object* v_todo_2256_; uint8_t v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; 
v_op_2254_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_patternPath___closed__0));
v___x_2255_ = lean_unsigned_to_nat(8u);
v_todo_2256_ = lean_mk_empty_array_with_capacity(v___x_2255_);
v___x_2257_ = 1;
lean_inc_ref(v_todo_2256_);
v___x_2258_ = lean_array_push(v_todo_2256_, v_e_2248_);
v___x_2259_ = l_Lean_Meta_LazyDiscrTree_buildPath(v_op_2254_, v___x_2257_, v___x_2258_, v_todo_2256_, v_a_2249_, v_a_2250_, v_a_2251_, v_a_2252_);
return v___x_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_patternPath___boxed(lean_object* v_e_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_){
_start:
{
lean_object* v_res_2266_; 
v_res_2266_ = l_Lean_Meta_LazyDiscrTree_patternPath(v_e_2260_, v_a_2261_, v_a_2262_, v_a_2263_, v_a_2264_);
lean_dec(v_a_2264_);
lean_dec_ref(v_a_2263_);
lean_dec(v_a_2262_);
lean_dec_ref(v_a_2261_);
return v_res_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath___lam__0(uint8_t v_root_2267_, lean_object* v_todo_2268_, lean_object* v_e_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_){
_start:
{
uint8_t v___x_2275_; lean_object* v___x_2276_; 
v___x_2275_ = 1;
v___x_2276_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_2269_, v___x_2275_, v_root_2267_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_);
if (lean_obj_tag(v___x_2276_) == 0)
{
lean_object* v_a_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2294_; 
v_a_2277_ = lean_ctor_get(v___x_2276_, 0);
v_isSharedCheck_2294_ = !lean_is_exclusive(v___x_2276_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2279_ = v___x_2276_;
v_isShared_2280_ = v_isSharedCheck_2294_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_a_2277_);
lean_dec(v___x_2276_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2294_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
lean_object* v_fst_2281_; lean_object* v_snd_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2293_; 
v_fst_2281_ = lean_ctor_get(v_a_2277_, 0);
v_snd_2282_ = lean_ctor_get(v_a_2277_, 1);
v_isSharedCheck_2293_ = !lean_is_exclusive(v_a_2277_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2284_ = v_a_2277_;
v_isShared_2285_ = v_isSharedCheck_2293_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_snd_2282_);
lean_inc(v_fst_2281_);
lean_dec(v_a_2277_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2293_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v___x_2286_; lean_object* v___x_2288_; 
v___x_2286_ = l_Array_append___redArg(v_todo_2268_, v_snd_2282_);
lean_dec(v_snd_2282_);
if (v_isShared_2285_ == 0)
{
lean_ctor_set(v___x_2284_, 1, v___x_2286_);
v___x_2288_ = v___x_2284_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v_fst_2281_);
lean_ctor_set(v_reuseFailAlloc_2292_, 1, v___x_2286_);
v___x_2288_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
lean_object* v___x_2290_; 
if (v_isShared_2280_ == 0)
{
lean_ctor_set(v___x_2279_, 0, v___x_2288_);
v___x_2290_ = v___x_2279_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v___x_2288_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
return v___x_2290_;
}
}
}
}
}
else
{
lean_dec_ref(v_todo_2268_);
return v___x_2276_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath___lam__0___boxed(lean_object* v_root_2295_, lean_object* v_todo_2296_, lean_object* v_e_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_){
_start:
{
uint8_t v_root_boxed_2303_; lean_object* v_res_2304_; 
v_root_boxed_2303_ = lean_unbox(v_root_2295_);
v_res_2304_ = l_Lean_Meta_LazyDiscrTree_targetPath___lam__0(v_root_boxed_2303_, v_todo_2296_, v_e_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_);
lean_dec(v___y_2301_);
lean_dec_ref(v___y_2300_);
lean_dec(v___y_2299_);
lean_dec_ref(v___y_2298_);
return v_res_2304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath(lean_object* v_e_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_){
_start:
{
lean_object* v_op_2312_; lean_object* v___x_2313_; lean_object* v_todo_2314_; uint8_t v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; 
v_op_2312_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_targetPath___closed__0));
v___x_2313_ = lean_unsigned_to_nat(8u);
v_todo_2314_ = lean_mk_empty_array_with_capacity(v___x_2313_);
v___x_2315_ = 1;
lean_inc_ref(v_todo_2314_);
v___x_2316_ = lean_array_push(v_todo_2314_, v_e_2306_);
v___x_2317_ = l_Lean_Meta_LazyDiscrTree_buildPath(v_op_2312_, v___x_2315_, v___x_2316_, v_todo_2314_, v_a_2307_, v_a_2308_, v_a_2309_, v_a_2310_);
return v___x_2317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath___boxed(lean_object* v_e_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_){
_start:
{
lean_object* v_res_2324_; 
v_res_2324_ = l_Lean_Meta_LazyDiscrTree_targetPath(v_e_2318_, v_a_2319_, v_a_2320_, v_a_2321_, v_a_2322_);
lean_dec(v_a_2322_);
lean_dec_ref(v_a_2321_);
lean_dec(v_a_2320_);
lean_dec_ref(v_a_2319_);
return v_res_2324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___redArg(lean_object* v_d_2325_, lean_object* v_m_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_){
_start:
{
lean_object* v_tries_2332_; lean_object* v_roots_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2374_; 
v_tries_2332_ = lean_ctor_get(v_d_2325_, 0);
v_roots_2333_ = lean_ctor_get(v_d_2325_, 1);
v_isSharedCheck_2374_ = !lean_is_exclusive(v_d_2325_);
if (v_isSharedCheck_2374_ == 0)
{
v___x_2335_ = v_d_2325_;
v_isShared_2336_ = v_isSharedCheck_2374_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_roots_2333_);
lean_inc(v_tries_2332_);
lean_dec(v_d_2325_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2374_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v___x_2337_; lean_object* v_keyedConfig_2338_; uint8_t v_trackZetaDelta_2339_; lean_object* v_zetaDeltaSet_2340_; lean_object* v_lctx_2341_; lean_object* v_localInstances_2342_; lean_object* v_defEqCtx_x3f_2343_; lean_object* v_synthPendingDepth_2344_; lean_object* v_customCanUnfoldPredicate_x3f_2345_; uint8_t v_univApprox_2346_; uint8_t v_inTypeClassResolution_2347_; uint8_t v_cacheInferType_2348_; uint8_t v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; 
v___x_2337_ = lean_st_mk_ref(v_tries_2332_);
v_keyedConfig_2338_ = lean_ctor_get(v_a_2327_, 0);
v_trackZetaDelta_2339_ = lean_ctor_get_uint8(v_a_2327_, sizeof(void*)*7);
v_zetaDeltaSet_2340_ = lean_ctor_get(v_a_2327_, 1);
v_lctx_2341_ = lean_ctor_get(v_a_2327_, 2);
v_localInstances_2342_ = lean_ctor_get(v_a_2327_, 3);
v_defEqCtx_x3f_2343_ = lean_ctor_get(v_a_2327_, 4);
v_synthPendingDepth_2344_ = lean_ctor_get(v_a_2327_, 5);
v_customCanUnfoldPredicate_x3f_2345_ = lean_ctor_get(v_a_2327_, 6);
v_univApprox_2346_ = lean_ctor_get_uint8(v_a_2327_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2347_ = lean_ctor_get_uint8(v_a_2327_, sizeof(void*)*7 + 2);
v_cacheInferType_2348_ = lean_ctor_get_uint8(v_a_2327_, sizeof(void*)*7 + 3);
v___x_2349_ = 2;
lean_inc_ref(v_keyedConfig_2338_);
v___x_2350_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2349_, v_keyedConfig_2338_);
lean_inc(v_customCanUnfoldPredicate_x3f_2345_);
lean_inc(v_synthPendingDepth_2344_);
lean_inc(v_defEqCtx_x3f_2343_);
lean_inc_ref(v_localInstances_2342_);
lean_inc_ref(v_lctx_2341_);
lean_inc(v_zetaDeltaSet_2340_);
v___x_2351_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2351_, 0, v___x_2350_);
lean_ctor_set(v___x_2351_, 1, v_zetaDeltaSet_2340_);
lean_ctor_set(v___x_2351_, 2, v_lctx_2341_);
lean_ctor_set(v___x_2351_, 3, v_localInstances_2342_);
lean_ctor_set(v___x_2351_, 4, v_defEqCtx_x3f_2343_);
lean_ctor_set(v___x_2351_, 5, v_synthPendingDepth_2344_);
lean_ctor_set(v___x_2351_, 6, v_customCanUnfoldPredicate_x3f_2345_);
lean_ctor_set_uint8(v___x_2351_, sizeof(void*)*7, v_trackZetaDelta_2339_);
lean_ctor_set_uint8(v___x_2351_, sizeof(void*)*7 + 1, v_univApprox_2346_);
lean_ctor_set_uint8(v___x_2351_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2347_);
lean_ctor_set_uint8(v___x_2351_, sizeof(void*)*7 + 3, v_cacheInferType_2348_);
lean_inc(v_a_2330_);
lean_inc_ref(v_a_2329_);
lean_inc(v_a_2328_);
lean_inc(v___x_2337_);
v___x_2352_ = lean_apply_6(v_m_2326_, v___x_2337_, v___x_2351_, v_a_2328_, v_a_2329_, v_a_2330_, lean_box(0));
if (lean_obj_tag(v___x_2352_) == 0)
{
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2365_; 
v_a_2353_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2355_ = v___x_2352_;
v_isShared_2356_ = v_isSharedCheck_2365_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2352_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2365_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2357_; lean_object* v___x_2359_; 
v___x_2357_ = lean_st_ref_get(v___x_2337_);
lean_dec(v___x_2337_);
if (v_isShared_2336_ == 0)
{
lean_ctor_set(v___x_2335_, 0, v___x_2357_);
v___x_2359_ = v___x_2335_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v___x_2357_);
lean_ctor_set(v_reuseFailAlloc_2364_, 1, v_roots_2333_);
v___x_2359_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
lean_object* v___x_2360_; lean_object* v___x_2362_; 
v___x_2360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2360_, 0, v_a_2353_);
lean_ctor_set(v___x_2360_, 1, v___x_2359_);
if (v_isShared_2356_ == 0)
{
lean_ctor_set(v___x_2355_, 0, v___x_2360_);
v___x_2362_ = v___x_2355_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v___x_2360_);
v___x_2362_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
return v___x_2362_;
}
}
}
}
else
{
lean_object* v_a_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2373_; 
lean_dec(v___x_2337_);
lean_del_object(v___x_2335_);
lean_dec_ref(v_roots_2333_);
v_a_2366_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2368_ = v___x_2352_;
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_a_2366_);
lean_dec(v___x_2352_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___redArg___boxed(lean_object* v_d_2375_, lean_object* v_m_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_){
_start:
{
lean_object* v_res_2382_; 
v_res_2382_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_d_2375_, v_m_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_);
lean_dec(v_a_2380_);
lean_dec_ref(v_a_2379_);
lean_dec(v_a_2378_);
lean_dec_ref(v_a_2377_);
return v_res_2382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch(lean_object* v_00_u03b1_2383_, lean_object* v_00_u03b2_2384_, lean_object* v_d_2385_, lean_object* v_m_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_){
_start:
{
lean_object* v___x_2392_; 
v___x_2392_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_d_2385_, v_m_2386_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_);
return v___x_2392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___boxed(lean_object* v_00_u03b1_2393_, lean_object* v_00_u03b2_2394_, lean_object* v_d_2395_, lean_object* v_m_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_){
_start:
{
lean_object* v_res_2402_; 
v_res_2402_ = l_Lean_Meta_LazyDiscrTree_runMatch(v_00_u03b1_2393_, v_00_u03b2_2394_, v_d_2395_, v_m_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_);
lean_dec(v_a_2400_);
lean_dec_ref(v_a_2399_);
lean_dec(v_a_2398_);
lean_dec_ref(v_a_2397_);
return v_res_2402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie___redArg(lean_object* v_i_2403_, lean_object* v_v_2404_, lean_object* v_a_2405_){
_start:
{
lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
v___x_2407_ = lean_st_ref_take(v_a_2405_);
v___x_2408_ = lean_array_set(v___x_2407_, v_i_2403_, v_v_2404_);
v___x_2409_ = lean_st_ref_set(v_a_2405_, v___x_2408_);
v___x_2410_ = lean_box(0);
v___x_2411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2410_);
return v___x_2411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie___redArg___boxed(lean_object* v_i_2412_, lean_object* v_v_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_){
_start:
{
lean_object* v_res_2416_; 
v_res_2416_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_i_2412_, v_v_2413_, v_a_2414_);
lean_dec(v_a_2414_);
lean_dec(v_i_2412_);
return v_res_2416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie(lean_object* v_00_u03b1_2417_, lean_object* v_i_2418_, lean_object* v_v_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_){
_start:
{
lean_object* v___x_2426_; 
v___x_2426_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_i_2418_, v_v_2419_, v_a_2420_);
return v___x_2426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie___boxed(lean_object* v_00_u03b1_2427_, lean_object* v_i_2428_, lean_object* v_v_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_){
_start:
{
lean_object* v_res_2436_; 
v_res_2436_ = l_Lean_Meta_LazyDiscrTree_setTrie(v_00_u03b1_2427_, v_i_2428_, v_v_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_);
lean_dec(v_a_2434_);
lean_dec_ref(v_a_2433_);
lean_dec(v_a_2432_);
lean_dec_ref(v_a_2431_);
lean_dec(v_a_2430_);
lean_dec(v_i_2428_);
return v_res_2436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___redArg___lam__0(lean_object* v_e_2437_, lean_object* v_a_2438_){
_start:
{
lean_object* v_sz_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; 
v_sz_2439_ = lean_array_get_size(v_a_2438_);
v___x_2440_ = lean_unsigned_to_nat(0u);
v___x_2441_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_2442_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_2443_ = lean_unsigned_to_nat(1u);
v___x_2444_ = lean_mk_empty_array_with_capacity(v___x_2443_);
v___x_2445_ = lean_array_push(v___x_2444_, v_e_2437_);
v___x_2446_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2446_, 0, v___x_2441_);
lean_ctor_set(v___x_2446_, 1, v___x_2440_);
lean_ctor_set(v___x_2446_, 2, v___x_2442_);
lean_ctor_set(v___x_2446_, 3, v___x_2445_);
v___x_2447_ = lean_array_push(v_a_2438_, v___x_2446_);
v___x_2448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2448_, 0, v_sz_2439_);
lean_ctor_set(v___x_2448_, 1, v___x_2447_);
return v___x_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___redArg(lean_object* v_inst_2449_, lean_object* v_e_2450_){
_start:
{
lean_object* v_modifyGet_2451_; lean_object* v___f_2452_; lean_object* v___x_2453_; 
v_modifyGet_2451_ = lean_ctor_get(v_inst_2449_, 2);
lean_inc(v_modifyGet_2451_);
lean_dec_ref(v_inst_2449_);
v___f_2452_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_newTrie___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2452_, 0, v_e_2450_);
v___x_2453_ = lean_apply_2(v_modifyGet_2451_, lean_box(0), v___f_2452_);
return v___x_2453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie(lean_object* v_m_2454_, lean_object* v_00_u03b1_2455_, lean_object* v_inst_2456_, lean_object* v_inst_2457_, lean_object* v_e_2458_){
_start:
{
lean_object* v___x_2459_; 
v___x_2459_ = l_Lean_Meta_LazyDiscrTree_newTrie___redArg(v_inst_2457_, v_e_2458_);
return v___x_2459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___boxed(lean_object* v_m_2460_, lean_object* v_00_u03b1_2461_, lean_object* v_inst_2462_, lean_object* v_inst_2463_, lean_object* v_e_2464_){
_start:
{
lean_object* v_res_2465_; 
v_res_2465_ = l_Lean_Meta_LazyDiscrTree_newTrie(v_m_2460_, v_00_u03b1_2461_, v_inst_2462_, v_inst_2463_, v_e_2464_);
lean_dec_ref(v_inst_2462_);
return v_res_2465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(lean_object* v_i_2466_, lean_object* v_e_2467_, lean_object* v_a_2468_){
_start:
{
lean_object* v___x_2470_; lean_object* v_fst_2472_; lean_object* v_snd_2473_; lean_object* v___x_2476_; lean_object* v___x_2477_; uint8_t v___x_2478_; 
v___x_2470_ = lean_st_ref_take(v_a_2468_);
v___x_2476_ = lean_box(0);
v___x_2477_ = lean_array_get_size(v___x_2470_);
v___x_2478_ = lean_nat_dec_lt(v_i_2466_, v___x_2477_);
if (v___x_2478_ == 0)
{
lean_dec_ref(v_e_2467_);
v_fst_2472_ = v___x_2476_;
v_snd_2473_ = v___x_2470_;
goto v___jp_2471_;
}
else
{
lean_object* v_v_2479_; lean_object* v_xs_x27_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; 
v_v_2479_ = lean_array_fget(v___x_2470_, v_i_2466_);
v_xs_x27_2480_ = lean_array_fset(v___x_2470_, v_i_2466_, v___x_2476_);
v___x_2481_ = l_Lean_Meta_LazyDiscrTree_Trie_pushPending___redArg(v_v_2479_, v_e_2467_);
v___x_2482_ = lean_array_fset(v_xs_x27_2480_, v_i_2466_, v___x_2481_);
v_fst_2472_ = v___x_2476_;
v_snd_2473_ = v___x_2482_;
goto v___jp_2471_;
}
v___jp_2471_:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; 
v___x_2474_ = lean_st_ref_set(v_a_2468_, v_snd_2473_);
v___x_2475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2475_, 0, v_fst_2472_);
return v___x_2475_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg___boxed(lean_object* v_i_2483_, lean_object* v_e_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_){
_start:
{
lean_object* v_res_2487_; 
v_res_2487_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_i_2483_, v_e_2484_, v_a_2485_);
lean_dec(v_a_2485_);
lean_dec(v_i_2483_);
return v_res_2487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie(lean_object* v_00_u03b1_2488_, lean_object* v_i_2489_, lean_object* v_e_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_){
_start:
{
lean_object* v___x_2497_; 
v___x_2497_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_i_2489_, v_e_2490_, v_a_2491_);
return v___x_2497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___boxed(lean_object* v_00_u03b1_2498_, lean_object* v_i_2499_, lean_object* v_e_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_){
_start:
{
lean_object* v_res_2507_; 
v_res_2507_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie(v_00_u03b1_2498_, v_i_2499_, v_e_2500_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_);
lean_dec(v_a_2505_);
lean_dec_ref(v_a_2504_);
lean_dec(v_a_2503_);
lean_dec_ref(v_a_2502_);
lean_dec(v_a_2501_);
lean_dec(v_i_2499_);
return v_res_2507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0(lean_object* v_x_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_){
_start:
{
lean_object* v___x_2515_; 
lean_inc(v___y_2509_);
v___x_2515_ = lean_apply_6(v_x_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, lean_box(0));
return v___x_2515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0___boxed(lean_object* v_x_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_){
_start:
{
lean_object* v_res_2523_; 
v_res_2523_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0(v_x_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_);
lean_dec(v___y_2517_);
return v_res_2523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(lean_object* v_lctx_2524_, lean_object* v_localInsts_2525_, lean_object* v_x_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_){
_start:
{
lean_object* v___f_2533_; lean_object* v___x_2534_; 
lean_inc(v___y_2527_);
v___f_2533_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2533_, 0, v_x_2526_);
lean_closure_set(v___f_2533_, 1, v___y_2527_);
v___x_2534_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_2524_, v_localInsts_2525_, v___f_2533_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_);
if (lean_obj_tag(v___x_2534_) == 0)
{
return v___x_2534_;
}
else
{
lean_object* v_a_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2542_; 
v_a_2535_ = lean_ctor_get(v___x_2534_, 0);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2534_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2537_ = v___x_2534_;
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_a_2535_);
lean_dec(v___x_2534_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
lean_object* v___x_2540_; 
if (v_isShared_2538_ == 0)
{
v___x_2540_ = v___x_2537_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_a_2535_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
return v___x_2540_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___boxed(lean_object* v_lctx_2543_, lean_object* v_localInsts_2544_, lean_object* v_x_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_){
_start:
{
lean_object* v_res_2552_; 
v_res_2552_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(v_lctx_2543_, v_localInsts_2544_, v_x_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
lean_dec(v___y_2550_);
lean_dec_ref(v___y_2549_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
lean_dec(v___y_2546_);
return v_res_2552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0(lean_object* v_00_u03b1_2553_, lean_object* v_00_u03b1_2554_, lean_object* v_lctx_2555_, lean_object* v_localInsts_2556_, lean_object* v_x_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_){
_start:
{
lean_object* v___x_2564_; 
v___x_2564_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(v_lctx_2555_, v_localInsts_2556_, v_x_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_);
return v___x_2564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___boxed(lean_object* v_00_u03b1_2565_, lean_object* v_00_u03b1_2566_, lean_object* v_lctx_2567_, lean_object* v_localInsts_2568_, lean_object* v_x_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_){
_start:
{
lean_object* v_res_2576_; 
v_res_2576_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0(v_00_u03b1_2565_, v_00_u03b1_2566_, v_lctx_2567_, v_localInsts_2568_, v_x_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_);
lean_dec(v___y_2574_);
lean_dec_ref(v___y_2573_);
lean_dec(v___y_2572_);
lean_dec_ref(v___y_2571_);
lean_dec(v___y_2570_);
return v_res_2576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(lean_object* v_e_2577_, lean_object* v___y_2578_){
_start:
{
lean_object* v___x_2580_; lean_object* v_sz_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
v___x_2580_ = lean_st_ref_take(v___y_2578_);
v_sz_2581_ = lean_array_get_size(v___x_2580_);
v___x_2582_ = lean_unsigned_to_nat(0u);
v___x_2583_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_2584_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_2585_ = lean_unsigned_to_nat(1u);
v___x_2586_ = lean_mk_empty_array_with_capacity(v___x_2585_);
v___x_2587_ = lean_array_push(v___x_2586_, v_e_2577_);
v___x_2588_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2588_, 0, v___x_2583_);
lean_ctor_set(v___x_2588_, 1, v___x_2582_);
lean_ctor_set(v___x_2588_, 2, v___x_2584_);
lean_ctor_set(v___x_2588_, 3, v___x_2587_);
v___x_2589_ = lean_array_push(v___x_2580_, v___x_2588_);
v___x_2590_ = lean_st_ref_set(v___y_2578_, v___x_2589_);
v___x_2591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2591_, 0, v_sz_2581_);
return v___x_2591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg___boxed(lean_object* v_e_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_){
_start:
{
lean_object* v_res_2595_; 
v_res_2595_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v_e_2592_, v___y_2593_);
lean_dec(v___y_2593_);
return v_res_2595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2(lean_object* v_00_u03b1_2596_, lean_object* v_e_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_){
_start:
{
lean_object* v___x_2604_; 
v___x_2604_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v_e_2597_, v___y_2598_);
return v___x_2604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___boxed(lean_object* v_00_u03b1_2605_, lean_object* v_e_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_){
_start:
{
lean_object* v_res_2613_; 
v_res_2613_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2(v_00_u03b1_2605_, v_e_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec(v___y_2609_);
lean_dec_ref(v___y_2608_);
lean_dec(v___y_2607_);
return v_res_2613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0(uint8_t v___x_2614_, lean_object* v_todo_2615_, lean_object* v_e_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_){
_start:
{
lean_object* v___x_2623_; 
v___x_2623_ = l_Lean_Meta_LazyDiscrTree_pushArgs(v___x_2614_, v_todo_2615_, v_e_2616_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_);
return v___x_2623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0___boxed(lean_object* v___x_2624_, lean_object* v_todo_2625_, lean_object* v_e_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_){
_start:
{
uint8_t v___x_4138__boxed_2633_; lean_object* v_res_2634_; 
v___x_4138__boxed_2633_ = lean_unbox(v___x_2624_);
v_res_2634_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0(v___x_4138__boxed_2633_, v_todo_2625_, v_e_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
lean_dec(v___y_2627_);
return v_res_2634_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(lean_object* v_a_2635_, lean_object* v_b_2636_, lean_object* v_x_2637_){
_start:
{
if (lean_obj_tag(v_x_2637_) == 0)
{
lean_dec(v_b_2636_);
lean_dec(v_a_2635_);
return v_x_2637_;
}
else
{
lean_object* v_key_2638_; lean_object* v_value_2639_; lean_object* v_tail_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2652_; 
v_key_2638_ = lean_ctor_get(v_x_2637_, 0);
v_value_2639_ = lean_ctor_get(v_x_2637_, 1);
v_tail_2640_ = lean_ctor_get(v_x_2637_, 2);
v_isSharedCheck_2652_ = !lean_is_exclusive(v_x_2637_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2642_ = v_x_2637_;
v_isShared_2643_ = v_isSharedCheck_2652_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_tail_2640_);
lean_inc(v_value_2639_);
lean_inc(v_key_2638_);
lean_dec(v_x_2637_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2652_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
uint8_t v___x_2644_; 
v___x_2644_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_2638_, v_a_2635_);
if (v___x_2644_ == 0)
{
lean_object* v___x_2645_; lean_object* v___x_2647_; 
v___x_2645_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(v_a_2635_, v_b_2636_, v_tail_2640_);
if (v_isShared_2643_ == 0)
{
lean_ctor_set(v___x_2642_, 2, v___x_2645_);
v___x_2647_ = v___x_2642_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v_key_2638_);
lean_ctor_set(v_reuseFailAlloc_2648_, 1, v_value_2639_);
lean_ctor_set(v_reuseFailAlloc_2648_, 2, v___x_2645_);
v___x_2647_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
return v___x_2647_;
}
}
else
{
lean_object* v___x_2650_; 
lean_dec(v_value_2639_);
lean_dec(v_key_2638_);
if (v_isShared_2643_ == 0)
{
lean_ctor_set(v___x_2642_, 1, v_b_2636_);
lean_ctor_set(v___x_2642_, 0, v_a_2635_);
v___x_2650_ = v___x_2642_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v_a_2635_);
lean_ctor_set(v_reuseFailAlloc_2651_, 1, v_b_2636_);
lean_ctor_set(v_reuseFailAlloc_2651_, 2, v_tail_2640_);
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
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(lean_object* v_a_2653_, lean_object* v_x_2654_){
_start:
{
if (lean_obj_tag(v_x_2654_) == 0)
{
uint8_t v___x_2655_; 
v___x_2655_ = 0;
return v___x_2655_;
}
else
{
lean_object* v_key_2656_; lean_object* v_tail_2657_; uint8_t v___x_2658_; 
v_key_2656_ = lean_ctor_get(v_x_2654_, 0);
v_tail_2657_ = lean_ctor_get(v_x_2654_, 2);
v___x_2658_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_2656_, v_a_2653_);
if (v___x_2658_ == 0)
{
v_x_2654_ = v_tail_2657_;
goto _start;
}
else
{
return v___x_2658_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg___boxed(lean_object* v_a_2660_, lean_object* v_x_2661_){
_start:
{
uint8_t v_res_2662_; lean_object* v_r_2663_; 
v_res_2662_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(v_a_2660_, v_x_2661_);
lean_dec(v_x_2661_);
lean_dec(v_a_2660_);
v_r_2663_ = lean_box(v_res_2662_);
return v_r_2663_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7___redArg(lean_object* v_x_2664_, lean_object* v_x_2665_){
_start:
{
if (lean_obj_tag(v_x_2665_) == 0)
{
return v_x_2664_;
}
else
{
lean_object* v_key_2666_; lean_object* v_value_2667_; lean_object* v_tail_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2691_; 
v_key_2666_ = lean_ctor_get(v_x_2665_, 0);
v_value_2667_ = lean_ctor_get(v_x_2665_, 1);
v_tail_2668_ = lean_ctor_get(v_x_2665_, 2);
v_isSharedCheck_2691_ = !lean_is_exclusive(v_x_2665_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2670_ = v_x_2665_;
v_isShared_2671_ = v_isSharedCheck_2691_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_tail_2668_);
lean_inc(v_value_2667_);
lean_inc(v_key_2666_);
lean_dec(v_x_2665_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2691_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2672_; uint64_t v___x_2673_; uint64_t v___x_2674_; uint64_t v___x_2675_; uint64_t v_fold_2676_; uint64_t v___x_2677_; uint64_t v___x_2678_; uint64_t v___x_2679_; size_t v___x_2680_; size_t v___x_2681_; size_t v___x_2682_; size_t v___x_2683_; size_t v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2687_; 
v___x_2672_ = lean_array_get_size(v_x_2664_);
v___x_2673_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_key_2666_);
v___x_2674_ = 32ULL;
v___x_2675_ = lean_uint64_shift_right(v___x_2673_, v___x_2674_);
v_fold_2676_ = lean_uint64_xor(v___x_2673_, v___x_2675_);
v___x_2677_ = 16ULL;
v___x_2678_ = lean_uint64_shift_right(v_fold_2676_, v___x_2677_);
v___x_2679_ = lean_uint64_xor(v_fold_2676_, v___x_2678_);
v___x_2680_ = lean_uint64_to_usize(v___x_2679_);
v___x_2681_ = lean_usize_of_nat(v___x_2672_);
v___x_2682_ = ((size_t)1ULL);
v___x_2683_ = lean_usize_sub(v___x_2681_, v___x_2682_);
v___x_2684_ = lean_usize_land(v___x_2680_, v___x_2683_);
v___x_2685_ = lean_array_uget_borrowed(v_x_2664_, v___x_2684_);
lean_inc(v___x_2685_);
if (v_isShared_2671_ == 0)
{
lean_ctor_set(v___x_2670_, 2, v___x_2685_);
v___x_2687_ = v___x_2670_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_key_2666_);
lean_ctor_set(v_reuseFailAlloc_2690_, 1, v_value_2667_);
lean_ctor_set(v_reuseFailAlloc_2690_, 2, v___x_2685_);
v___x_2687_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
lean_object* v___x_2688_; 
v___x_2688_ = lean_array_uset(v_x_2664_, v___x_2684_, v___x_2687_);
v_x_2664_ = v___x_2688_;
v_x_2665_ = v_tail_2668_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6___redArg(lean_object* v_i_2692_, lean_object* v_source_2693_, lean_object* v_target_2694_){
_start:
{
lean_object* v___x_2695_; uint8_t v___x_2696_; 
v___x_2695_ = lean_array_get_size(v_source_2693_);
v___x_2696_ = lean_nat_dec_lt(v_i_2692_, v___x_2695_);
if (v___x_2696_ == 0)
{
lean_dec_ref(v_source_2693_);
lean_dec(v_i_2692_);
return v_target_2694_;
}
else
{
lean_object* v_es_2697_; lean_object* v___x_2698_; lean_object* v_source_2699_; lean_object* v_target_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; 
v_es_2697_ = lean_array_fget(v_source_2693_, v_i_2692_);
v___x_2698_ = lean_box(0);
v_source_2699_ = lean_array_fset(v_source_2693_, v_i_2692_, v___x_2698_);
v_target_2700_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7___redArg(v_target_2694_, v_es_2697_);
v___x_2701_ = lean_unsigned_to_nat(1u);
v___x_2702_ = lean_nat_add(v_i_2692_, v___x_2701_);
lean_dec(v_i_2692_);
v_i_2692_ = v___x_2702_;
v_source_2693_ = v_source_2699_;
v_target_2694_ = v_target_2700_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5___redArg(lean_object* v_data_2704_){
_start:
{
lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v_nbuckets_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; 
v___x_2705_ = lean_array_get_size(v_data_2704_);
v___x_2706_ = lean_unsigned_to_nat(2u);
v_nbuckets_2707_ = lean_nat_mul(v___x_2705_, v___x_2706_);
v___x_2708_ = lean_unsigned_to_nat(0u);
v___x_2709_ = lean_box(0);
v___x_2710_ = lean_mk_array(v_nbuckets_2707_, v___x_2709_);
v___x_2711_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6___redArg(v___x_2708_, v_data_2704_, v___x_2710_);
return v___x_2711_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(lean_object* v_m_2712_, lean_object* v_a_2713_, lean_object* v_b_2714_){
_start:
{
lean_object* v_size_2715_; lean_object* v_buckets_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2759_; 
v_size_2715_ = lean_ctor_get(v_m_2712_, 0);
v_buckets_2716_ = lean_ctor_get(v_m_2712_, 1);
v_isSharedCheck_2759_ = !lean_is_exclusive(v_m_2712_);
if (v_isSharedCheck_2759_ == 0)
{
v___x_2718_ = v_m_2712_;
v_isShared_2719_ = v_isSharedCheck_2759_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_buckets_2716_);
lean_inc(v_size_2715_);
lean_dec(v_m_2712_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2759_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v___x_2720_; uint64_t v___x_2721_; uint64_t v___x_2722_; uint64_t v___x_2723_; uint64_t v_fold_2724_; uint64_t v___x_2725_; uint64_t v___x_2726_; uint64_t v___x_2727_; size_t v___x_2728_; size_t v___x_2729_; size_t v___x_2730_; size_t v___x_2731_; size_t v___x_2732_; lean_object* v_bkt_2733_; uint8_t v___x_2734_; 
v___x_2720_ = lean_array_get_size(v_buckets_2716_);
v___x_2721_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_a_2713_);
v___x_2722_ = 32ULL;
v___x_2723_ = lean_uint64_shift_right(v___x_2721_, v___x_2722_);
v_fold_2724_ = lean_uint64_xor(v___x_2721_, v___x_2723_);
v___x_2725_ = 16ULL;
v___x_2726_ = lean_uint64_shift_right(v_fold_2724_, v___x_2725_);
v___x_2727_ = lean_uint64_xor(v_fold_2724_, v___x_2726_);
v___x_2728_ = lean_uint64_to_usize(v___x_2727_);
v___x_2729_ = lean_usize_of_nat(v___x_2720_);
v___x_2730_ = ((size_t)1ULL);
v___x_2731_ = lean_usize_sub(v___x_2729_, v___x_2730_);
v___x_2732_ = lean_usize_land(v___x_2728_, v___x_2731_);
v_bkt_2733_ = lean_array_uget_borrowed(v_buckets_2716_, v___x_2732_);
v___x_2734_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(v_a_2713_, v_bkt_2733_);
if (v___x_2734_ == 0)
{
lean_object* v___x_2735_; lean_object* v_size_x27_2736_; lean_object* v___x_2737_; lean_object* v_buckets_x27_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; uint8_t v___x_2744_; 
v___x_2735_ = lean_unsigned_to_nat(1u);
v_size_x27_2736_ = lean_nat_add(v_size_2715_, v___x_2735_);
lean_dec(v_size_2715_);
lean_inc(v_bkt_2733_);
v___x_2737_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2737_, 0, v_a_2713_);
lean_ctor_set(v___x_2737_, 1, v_b_2714_);
lean_ctor_set(v___x_2737_, 2, v_bkt_2733_);
v_buckets_x27_2738_ = lean_array_uset(v_buckets_2716_, v___x_2732_, v___x_2737_);
v___x_2739_ = lean_unsigned_to_nat(4u);
v___x_2740_ = lean_nat_mul(v_size_x27_2736_, v___x_2739_);
v___x_2741_ = lean_unsigned_to_nat(3u);
v___x_2742_ = lean_nat_div(v___x_2740_, v___x_2741_);
lean_dec(v___x_2740_);
v___x_2743_ = lean_array_get_size(v_buckets_x27_2738_);
v___x_2744_ = lean_nat_dec_le(v___x_2742_, v___x_2743_);
lean_dec(v___x_2742_);
if (v___x_2744_ == 0)
{
lean_object* v_val_2745_; lean_object* v___x_2747_; 
v_val_2745_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5___redArg(v_buckets_x27_2738_);
if (v_isShared_2719_ == 0)
{
lean_ctor_set(v___x_2718_, 1, v_val_2745_);
lean_ctor_set(v___x_2718_, 0, v_size_x27_2736_);
v___x_2747_ = v___x_2718_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v_size_x27_2736_);
lean_ctor_set(v_reuseFailAlloc_2748_, 1, v_val_2745_);
v___x_2747_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
return v___x_2747_;
}
}
else
{
lean_object* v___x_2750_; 
if (v_isShared_2719_ == 0)
{
lean_ctor_set(v___x_2718_, 1, v_buckets_x27_2738_);
lean_ctor_set(v___x_2718_, 0, v_size_x27_2736_);
v___x_2750_ = v___x_2718_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v_size_x27_2736_);
lean_ctor_set(v_reuseFailAlloc_2751_, 1, v_buckets_x27_2738_);
v___x_2750_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
return v___x_2750_;
}
}
}
else
{
lean_object* v___x_2752_; lean_object* v_buckets_x27_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2757_; 
lean_inc(v_bkt_2733_);
v___x_2752_ = lean_box(0);
v_buckets_x27_2753_ = lean_array_uset(v_buckets_2716_, v___x_2732_, v___x_2752_);
v___x_2754_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(v_a_2713_, v_b_2714_, v_bkt_2733_);
v___x_2755_ = lean_array_uset(v_buckets_x27_2753_, v___x_2732_, v___x_2754_);
if (v_isShared_2719_ == 0)
{
lean_ctor_set(v___x_2718_, 1, v___x_2755_);
v___x_2757_ = v___x_2718_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v_size_2715_);
lean_ctor_set(v_reuseFailAlloc_2758_, 1, v___x_2755_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
return v___x_2757_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(lean_object* v_a_2760_, lean_object* v_x_2761_){
_start:
{
if (lean_obj_tag(v_x_2761_) == 0)
{
lean_object* v___x_2762_; 
v___x_2762_ = lean_box(0);
return v___x_2762_;
}
else
{
lean_object* v_key_2763_; lean_object* v_value_2764_; lean_object* v_tail_2765_; uint8_t v___x_2766_; 
v_key_2763_ = lean_ctor_get(v_x_2761_, 0);
v_value_2764_ = lean_ctor_get(v_x_2761_, 1);
v_tail_2765_ = lean_ctor_get(v_x_2761_, 2);
v___x_2766_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_2763_, v_a_2760_);
if (v___x_2766_ == 0)
{
v_x_2761_ = v_tail_2765_;
goto _start;
}
else
{
lean_object* v___x_2768_; 
lean_inc(v_value_2764_);
v___x_2768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2768_, 0, v_value_2764_);
return v___x_2768_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg___boxed(lean_object* v_a_2769_, lean_object* v_x_2770_){
_start:
{
lean_object* v_res_2771_; 
v_res_2771_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(v_a_2769_, v_x_2770_);
lean_dec(v_x_2770_);
lean_dec(v_a_2769_);
return v_res_2771_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(lean_object* v_m_2772_, lean_object* v_a_2773_){
_start:
{
lean_object* v_buckets_2774_; lean_object* v___x_2775_; uint64_t v___x_2776_; uint64_t v___x_2777_; uint64_t v___x_2778_; uint64_t v_fold_2779_; uint64_t v___x_2780_; uint64_t v___x_2781_; uint64_t v___x_2782_; size_t v___x_2783_; size_t v___x_2784_; size_t v___x_2785_; size_t v___x_2786_; size_t v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; 
v_buckets_2774_ = lean_ctor_get(v_m_2772_, 1);
v___x_2775_ = lean_array_get_size(v_buckets_2774_);
v___x_2776_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_a_2773_);
v___x_2777_ = 32ULL;
v___x_2778_ = lean_uint64_shift_right(v___x_2776_, v___x_2777_);
v_fold_2779_ = lean_uint64_xor(v___x_2776_, v___x_2778_);
v___x_2780_ = 16ULL;
v___x_2781_ = lean_uint64_shift_right(v_fold_2779_, v___x_2780_);
v___x_2782_ = lean_uint64_xor(v_fold_2779_, v___x_2781_);
v___x_2783_ = lean_uint64_to_usize(v___x_2782_);
v___x_2784_ = lean_usize_of_nat(v___x_2775_);
v___x_2785_ = ((size_t)1ULL);
v___x_2786_ = lean_usize_sub(v___x_2784_, v___x_2785_);
v___x_2787_ = lean_usize_land(v___x_2783_, v___x_2786_);
v___x_2788_ = lean_array_uget_borrowed(v_buckets_2774_, v___x_2787_);
v___x_2789_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(v_a_2773_, v___x_2788_);
return v___x_2789_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg___boxed(lean_object* v_m_2790_, lean_object* v_a_2791_){
_start:
{
lean_object* v_res_2792_; 
v_res_2792_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_m_2790_, v_a_2791_);
lean_dec(v_a_2791_);
lean_dec_ref(v_m_2790_);
return v_res_2792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(lean_object* v_p_2793_, lean_object* v_entry_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_){
_start:
{
lean_object* v_snd_2801_; lean_object* v_snd_2802_; lean_object* v_fst_2803_; lean_object* v_fst_2804_; lean_object* v_snd_2805_; lean_object* v_fst_2806_; lean_object* v_fst_2807_; lean_object* v_snd_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; uint8_t v___x_2811_; 
v_snd_2801_ = lean_ctor_get(v_p_2793_, 1);
v_snd_2802_ = lean_ctor_get(v_entry_2794_, 1);
lean_inc(v_snd_2802_);
v_fst_2803_ = lean_ctor_get(v_p_2793_, 0);
v_fst_2804_ = lean_ctor_get(v_snd_2801_, 0);
v_snd_2805_ = lean_ctor_get(v_snd_2801_, 1);
v_fst_2806_ = lean_ctor_get(v_entry_2794_, 0);
lean_inc(v_fst_2806_);
lean_dec_ref(v_entry_2794_);
v_fst_2807_ = lean_ctor_get(v_snd_2802_, 0);
lean_inc(v_fst_2807_);
v_snd_2808_ = lean_ctor_get(v_snd_2802_, 1);
v___x_2809_ = lean_array_get_size(v_fst_2806_);
v___x_2810_ = lean_unsigned_to_nat(0u);
v___x_2811_ = lean_nat_dec_eq(v___x_2809_, v___x_2810_);
if (v___x_2811_ == 0)
{
lean_object* v_fst_2812_; lean_object* v_snd_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2918_; 
v_fst_2812_ = lean_ctor_get(v_fst_2807_, 0);
v_snd_2813_ = lean_ctor_get(v_fst_2807_, 1);
v_isSharedCheck_2918_ = !lean_is_exclusive(v_fst_2807_);
if (v_isSharedCheck_2918_ == 0)
{
v___x_2815_ = v_fst_2807_;
v_isShared_2816_ = v_isSharedCheck_2918_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_snd_2813_);
lean_inc(v_fst_2812_);
lean_dec(v_fst_2807_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2918_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v_e_2820_; lean_object* v_todo_2821_; lean_object* v___x_2822_; lean_object* v___f_2823_; lean_object* v___x_2824_; 
v___x_2817_ = l_Lean_instInhabitedExpr;
v___x_2818_ = lean_unsigned_to_nat(1u);
v___x_2819_ = lean_nat_sub(v___x_2809_, v___x_2818_);
v_e_2820_ = lean_array_get(v___x_2817_, v_fst_2806_, v___x_2819_);
lean_dec(v___x_2819_);
v_todo_2821_ = lean_array_pop(v_fst_2806_);
v___x_2822_ = lean_box(v___x_2811_);
v___f_2823_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2823_, 0, v___x_2822_);
lean_closure_set(v___f_2823_, 1, v_todo_2821_);
lean_closure_set(v___f_2823_, 2, v_e_2820_);
v___x_2824_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(v_fst_2812_, v_snd_2813_, v___f_2823_, v_a_2795_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_);
if (lean_obj_tag(v___x_2824_) == 0)
{
lean_object* v_a_2825_; lean_object* v_fst_2826_; lean_object* v_snd_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2909_; 
v_a_2825_ = lean_ctor_get(v___x_2824_, 0);
lean_inc(v_a_2825_);
lean_dec_ref_known(v___x_2824_, 1);
v_fst_2826_ = lean_ctor_get(v_a_2825_, 0);
v_snd_2827_ = lean_ctor_get(v_a_2825_, 1);
v_isSharedCheck_2909_ = !lean_is_exclusive(v_a_2825_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2829_ = v_a_2825_;
v_isShared_2830_ = v_isSharedCheck_2909_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_snd_2827_);
lean_inc(v_fst_2826_);
lean_dec(v_a_2825_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2909_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v___x_2831_; uint8_t v___x_2832_; 
v___x_2831_ = lean_box(3);
v___x_2832_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_fst_2826_, v___x_2831_);
if (v___x_2832_ == 0)
{
lean_object* v___x_2833_; 
v___x_2833_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_snd_2805_, v_fst_2826_);
if (lean_obj_tag(v___x_2833_) == 0)
{
lean_object* v___x_2835_; 
lean_inc(v_snd_2805_);
lean_inc(v_fst_2804_);
lean_inc(v_fst_2803_);
lean_dec_ref(v_p_2793_);
lean_inc(v_snd_2802_);
if (v_isShared_2830_ == 0)
{
lean_ctor_set(v___x_2829_, 1, v_snd_2802_);
lean_ctor_set(v___x_2829_, 0, v_snd_2827_);
v___x_2835_ = v___x_2829_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v_snd_2827_);
lean_ctor_set(v_reuseFailAlloc_2858_, 1, v_snd_2802_);
v___x_2835_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2855_; 
v_isSharedCheck_2855_ = !lean_is_exclusive(v_snd_2802_);
if (v_isSharedCheck_2855_ == 0)
{
lean_object* v_unused_2856_; lean_object* v_unused_2857_; 
v_unused_2856_ = lean_ctor_get(v_snd_2802_, 1);
lean_dec(v_unused_2856_);
v_unused_2857_ = lean_ctor_get(v_snd_2802_, 0);
lean_dec(v_unused_2857_);
v___x_2837_ = v_snd_2802_;
v_isShared_2838_ = v_isSharedCheck_2855_;
goto v_resetjp_2836_;
}
else
{
lean_dec(v_snd_2802_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2855_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___x_2839_; lean_object* v_a_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2854_; 
v___x_2839_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v___x_2835_, v_a_2795_);
v_a_2840_ = lean_ctor_get(v___x_2839_, 0);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2842_ = v___x_2839_;
v_isShared_2843_ = v_isSharedCheck_2854_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_a_2840_);
lean_dec(v___x_2839_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2854_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v___x_2844_; lean_object* v___x_2846_; 
v___x_2844_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_snd_2805_, v_fst_2826_, v_a_2840_);
if (v_isShared_2816_ == 0)
{
lean_ctor_set(v___x_2815_, 1, v___x_2844_);
lean_ctor_set(v___x_2815_, 0, v_fst_2804_);
v___x_2846_ = v___x_2815_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_fst_2804_);
lean_ctor_set(v_reuseFailAlloc_2853_, 1, v___x_2844_);
v___x_2846_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
lean_object* v___x_2848_; 
if (v_isShared_2838_ == 0)
{
lean_ctor_set(v___x_2837_, 1, v___x_2846_);
lean_ctor_set(v___x_2837_, 0, v_fst_2803_);
v___x_2848_ = v___x_2837_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v_fst_2803_);
lean_ctor_set(v_reuseFailAlloc_2852_, 1, v___x_2846_);
v___x_2848_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
lean_object* v___x_2850_; 
if (v_isShared_2843_ == 0)
{
lean_ctor_set(v___x_2842_, 0, v___x_2848_);
v___x_2850_ = v___x_2842_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v___x_2848_);
v___x_2850_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
return v___x_2850_;
}
}
}
}
}
}
}
else
{
lean_object* v_val_2859_; lean_object* v___x_2861_; 
lean_dec(v_fst_2826_);
lean_del_object(v___x_2815_);
v_val_2859_ = lean_ctor_get(v___x_2833_, 0);
lean_inc(v_val_2859_);
lean_dec_ref_known(v___x_2833_, 1);
if (v_isShared_2830_ == 0)
{
lean_ctor_set(v___x_2829_, 1, v_snd_2802_);
lean_ctor_set(v___x_2829_, 0, v_snd_2827_);
v___x_2861_ = v___x_2829_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v_snd_2827_);
lean_ctor_set(v_reuseFailAlloc_2871_, 1, v_snd_2802_);
v___x_2861_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
lean_object* v___x_2862_; lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_2869_; 
v___x_2862_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_val_2859_, v___x_2861_, v_a_2795_);
lean_dec(v_val_2859_);
v_isSharedCheck_2869_ = !lean_is_exclusive(v___x_2862_);
if (v_isSharedCheck_2869_ == 0)
{
lean_object* v_unused_2870_; 
v_unused_2870_ = lean_ctor_get(v___x_2862_, 0);
lean_dec(v_unused_2870_);
v___x_2864_ = v___x_2862_;
v_isShared_2865_ = v_isSharedCheck_2869_;
goto v_resetjp_2863_;
}
else
{
lean_dec(v___x_2862_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_2869_;
goto v_resetjp_2863_;
}
v_resetjp_2863_:
{
lean_object* v___x_2867_; 
if (v_isShared_2865_ == 0)
{
lean_ctor_set(v___x_2864_, 0, v_p_2793_);
v___x_2867_ = v___x_2864_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v_p_2793_);
v___x_2867_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
return v___x_2867_;
}
}
}
}
}
else
{
uint8_t v___x_2872_; 
lean_dec(v_fst_2826_);
v___x_2872_ = lean_nat_dec_eq(v_fst_2804_, v___x_2810_);
if (v___x_2872_ == 0)
{
lean_object* v___x_2874_; 
lean_del_object(v___x_2815_);
if (v_isShared_2830_ == 0)
{
lean_ctor_set(v___x_2829_, 1, v_snd_2802_);
lean_ctor_set(v___x_2829_, 0, v_snd_2827_);
v___x_2874_ = v___x_2829_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v_snd_2827_);
lean_ctor_set(v_reuseFailAlloc_2884_, 1, v_snd_2802_);
v___x_2874_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
lean_object* v___x_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2882_; 
v___x_2875_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_fst_2804_, v___x_2874_, v_a_2795_);
v_isSharedCheck_2882_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_2882_ == 0)
{
lean_object* v_unused_2883_; 
v_unused_2883_ = lean_ctor_get(v___x_2875_, 0);
lean_dec(v_unused_2883_);
v___x_2877_ = v___x_2875_;
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
else
{
lean_dec(v___x_2875_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v___x_2880_; 
if (v_isShared_2878_ == 0)
{
lean_ctor_set(v___x_2877_, 0, v_p_2793_);
v___x_2880_ = v___x_2877_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v_p_2793_);
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
else
{
lean_object* v___x_2886_; 
lean_inc(v_snd_2805_);
lean_inc(v_fst_2803_);
lean_dec_ref(v_p_2793_);
lean_inc(v_snd_2802_);
if (v_isShared_2830_ == 0)
{
lean_ctor_set(v___x_2829_, 1, v_snd_2802_);
lean_ctor_set(v___x_2829_, 0, v_snd_2827_);
v___x_2886_ = v___x_2829_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v_snd_2827_);
lean_ctor_set(v_reuseFailAlloc_2908_, 1, v_snd_2802_);
v___x_2886_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2905_; 
v_isSharedCheck_2905_ = !lean_is_exclusive(v_snd_2802_);
if (v_isSharedCheck_2905_ == 0)
{
lean_object* v_unused_2906_; lean_object* v_unused_2907_; 
v_unused_2906_ = lean_ctor_get(v_snd_2802_, 1);
lean_dec(v_unused_2906_);
v_unused_2907_ = lean_ctor_get(v_snd_2802_, 0);
lean_dec(v_unused_2907_);
v___x_2888_ = v_snd_2802_;
v_isShared_2889_ = v_isSharedCheck_2905_;
goto v_resetjp_2887_;
}
else
{
lean_dec(v_snd_2802_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2905_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2890_; lean_object* v_a_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2904_; 
v___x_2890_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v___x_2886_, v_a_2795_);
v_a_2891_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2893_ = v___x_2890_;
v_isShared_2894_ = v_isSharedCheck_2904_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_a_2891_);
lean_dec(v___x_2890_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2904_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v___x_2896_; 
if (v_isShared_2816_ == 0)
{
lean_ctor_set(v___x_2815_, 1, v_snd_2805_);
lean_ctor_set(v___x_2815_, 0, v_a_2891_);
v___x_2896_ = v___x_2815_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_a_2891_);
lean_ctor_set(v_reuseFailAlloc_2903_, 1, v_snd_2805_);
v___x_2896_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
lean_object* v___x_2898_; 
if (v_isShared_2889_ == 0)
{
lean_ctor_set(v___x_2888_, 1, v___x_2896_);
lean_ctor_set(v___x_2888_, 0, v_fst_2803_);
v___x_2898_ = v___x_2888_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_fst_2803_);
lean_ctor_set(v_reuseFailAlloc_2902_, 1, v___x_2896_);
v___x_2898_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
lean_object* v___x_2900_; 
if (v_isShared_2894_ == 0)
{
lean_ctor_set(v___x_2893_, 0, v___x_2898_);
v___x_2900_ = v___x_2893_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v___x_2898_);
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
}
}
}
}
}
}
else
{
lean_object* v_a_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2917_; 
lean_del_object(v___x_2815_);
lean_dec(v_snd_2802_);
lean_dec_ref(v_p_2793_);
v_a_2910_ = lean_ctor_get(v___x_2824_, 0);
v_isSharedCheck_2917_ = !lean_is_exclusive(v___x_2824_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2912_ = v___x_2824_;
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_a_2910_);
lean_dec(v___x_2824_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
lean_object* v___x_2915_; 
if (v_isShared_2913_ == 0)
{
v___x_2915_ = v___x_2912_;
goto v_reusejp_2914_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v_a_2910_);
v___x_2915_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2914_;
}
v_reusejp_2914_:
{
return v___x_2915_;
}
}
}
}
}
else
{
lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_2927_; 
lean_inc(v_snd_2808_);
lean_inc(v_fst_2803_);
lean_inc(v_snd_2801_);
lean_dec(v_fst_2807_);
lean_dec(v_fst_2806_);
lean_dec_ref(v_p_2793_);
v_isSharedCheck_2927_ = !lean_is_exclusive(v_snd_2802_);
if (v_isSharedCheck_2927_ == 0)
{
lean_object* v_unused_2928_; lean_object* v_unused_2929_; 
v_unused_2928_ = lean_ctor_get(v_snd_2802_, 1);
lean_dec(v_unused_2928_);
v_unused_2929_ = lean_ctor_get(v_snd_2802_, 0);
lean_dec(v_unused_2929_);
v___x_2920_ = v_snd_2802_;
v_isShared_2921_ = v_isSharedCheck_2927_;
goto v_resetjp_2919_;
}
else
{
lean_dec(v_snd_2802_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_2927_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
lean_object* v_values_2922_; lean_object* v___x_2924_; 
v_values_2922_ = lean_array_push(v_fst_2803_, v_snd_2808_);
if (v_isShared_2921_ == 0)
{
lean_ctor_set(v___x_2920_, 1, v_snd_2801_);
lean_ctor_set(v___x_2920_, 0, v_values_2922_);
v___x_2924_ = v___x_2920_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2926_, 0, v_values_2922_);
lean_ctor_set(v_reuseFailAlloc_2926_, 1, v_snd_2801_);
v___x_2924_ = v_reuseFailAlloc_2926_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
lean_object* v___x_2925_; 
v___x_2925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2925_, 0, v___x_2924_);
return v___x_2925_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___boxed(lean_object* v_p_2930_, lean_object* v_entry_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_, lean_object* v_a_2935_, lean_object* v_a_2936_, lean_object* v_a_2937_){
_start:
{
lean_object* v_res_2938_; 
v_res_2938_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(v_p_2930_, v_entry_2931_, v_a_2932_, v_a_2933_, v_a_2934_, v_a_2935_, v_a_2936_);
lean_dec(v_a_2936_);
lean_dec_ref(v_a_2935_);
lean_dec(v_a_2934_);
lean_dec_ref(v_a_2933_);
lean_dec(v_a_2932_);
return v_res_2938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry(lean_object* v_00_u03b1_2939_, lean_object* v_p_2940_, lean_object* v_entry_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_){
_start:
{
lean_object* v___x_2948_; 
v___x_2948_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(v_p_2940_, v_entry_2941_, v_a_2942_, v_a_2943_, v_a_2944_, v_a_2945_, v_a_2946_);
return v___x_2948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___boxed(lean_object* v_00_u03b1_2949_, lean_object* v_p_2950_, lean_object* v_entry_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_){
_start:
{
lean_object* v_res_2958_; 
v_res_2958_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry(v_00_u03b1_2949_, v_p_2950_, v_entry_2951_, v_a_2952_, v_a_2953_, v_a_2954_, v_a_2955_, v_a_2956_);
lean_dec(v_a_2956_);
lean_dec_ref(v_a_2955_);
lean_dec(v_a_2954_);
lean_dec_ref(v_a_2953_);
lean_dec(v_a_2952_);
return v_res_2958_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1(lean_object* v_00_u03b2_2959_, lean_object* v_m_2960_, lean_object* v_a_2961_){
_start:
{
lean_object* v___x_2962_; 
v___x_2962_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_m_2960_, v_a_2961_);
return v___x_2962_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___boxed(lean_object* v_00_u03b2_2963_, lean_object* v_m_2964_, lean_object* v_a_2965_){
_start:
{
lean_object* v_res_2966_; 
v_res_2966_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1(v_00_u03b2_2963_, v_m_2964_, v_a_2965_);
lean_dec(v_a_2965_);
lean_dec_ref(v_m_2964_);
return v_res_2966_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3(lean_object* v_00_u03b2_2967_, lean_object* v_m_2968_, lean_object* v_a_2969_, lean_object* v_b_2970_){
_start:
{
lean_object* v___x_2971_; 
v___x_2971_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_m_2968_, v_a_2969_, v_b_2970_);
return v___x_2971_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1(lean_object* v_00_u03b2_2972_, lean_object* v_a_2973_, lean_object* v_x_2974_){
_start:
{
lean_object* v___x_2975_; 
v___x_2975_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(v_a_2973_, v_x_2974_);
return v___x_2975_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2976_, lean_object* v_a_2977_, lean_object* v_x_2978_){
_start:
{
lean_object* v_res_2979_; 
v_res_2979_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1(v_00_u03b2_2976_, v_a_2977_, v_x_2978_);
lean_dec(v_x_2978_);
lean_dec(v_a_2977_);
return v_res_2979_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4(lean_object* v_00_u03b2_2980_, lean_object* v_a_2981_, lean_object* v_x_2982_){
_start:
{
uint8_t v___x_2983_; 
v___x_2983_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(v_a_2981_, v_x_2982_);
return v___x_2983_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___boxed(lean_object* v_00_u03b2_2984_, lean_object* v_a_2985_, lean_object* v_x_2986_){
_start:
{
uint8_t v_res_2987_; lean_object* v_r_2988_; 
v_res_2987_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4(v_00_u03b2_2984_, v_a_2985_, v_x_2986_);
lean_dec(v_x_2986_);
lean_dec(v_a_2985_);
v_r_2988_ = lean_box(v_res_2987_);
return v_r_2988_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5(lean_object* v_00_u03b2_2989_, lean_object* v_data_2990_){
_start:
{
lean_object* v___x_2991_; 
v___x_2991_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5___redArg(v_data_2990_);
return v___x_2991_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6(lean_object* v_00_u03b2_2992_, lean_object* v_a_2993_, lean_object* v_b_2994_, lean_object* v_x_2995_){
_start:
{
lean_object* v___x_2996_; 
v___x_2996_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(v_a_2993_, v_b_2994_, v_x_2995_);
return v___x_2996_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_2997_, lean_object* v_i_2998_, lean_object* v_source_2999_, lean_object* v_target_3000_){
_start:
{
lean_object* v___x_3001_; 
v___x_3001_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6___redArg(v_i_2998_, v_source_2999_, v_target_3000_);
return v___x_3001_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_3002_, lean_object* v_x_3003_, lean_object* v_x_3004_){
_start:
{
lean_object* v___x_3005_; 
v___x_3005_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7___redArg(v_x_3003_, v_x_3004_);
return v___x_3005_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(lean_object* v_as_3006_, size_t v_i_3007_, size_t v_stop_3008_, lean_object* v_b_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_){
_start:
{
uint8_t v___x_3016_; 
v___x_3016_ = lean_usize_dec_eq(v_i_3007_, v_stop_3008_);
if (v___x_3016_ == 0)
{
lean_object* v___x_3017_; lean_object* v___x_3018_; 
v___x_3017_ = lean_array_uget_borrowed(v_as_3006_, v_i_3007_);
lean_inc(v___x_3017_);
v___x_3018_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(v_b_3009_, v___x_3017_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_);
if (lean_obj_tag(v___x_3018_) == 0)
{
lean_object* v_a_3019_; size_t v___x_3020_; size_t v___x_3021_; 
v_a_3019_ = lean_ctor_get(v___x_3018_, 0);
lean_inc(v_a_3019_);
lean_dec_ref_known(v___x_3018_, 1);
v___x_3020_ = ((size_t)1ULL);
v___x_3021_ = lean_usize_add(v_i_3007_, v___x_3020_);
v_i_3007_ = v___x_3021_;
v_b_3009_ = v_a_3019_;
goto _start;
}
else
{
return v___x_3018_;
}
}
else
{
lean_object* v___x_3023_; 
v___x_3023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3023_, 0, v_b_3009_);
return v___x_3023_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg___boxed(lean_object* v_as_3024_, lean_object* v_i_3025_, lean_object* v_stop_3026_, lean_object* v_b_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_){
_start:
{
size_t v_i_boxed_3034_; size_t v_stop_boxed_3035_; lean_object* v_res_3036_; 
v_i_boxed_3034_ = lean_unbox_usize(v_i_3025_);
lean_dec(v_i_3025_);
v_stop_boxed_3035_ = lean_unbox_usize(v_stop_3026_);
lean_dec(v_stop_3026_);
v_res_3036_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_as_3024_, v_i_boxed_3034_, v_stop_boxed_3035_, v_b_3027_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_, v___y_3032_);
lean_dec(v___y_3032_);
lean_dec_ref(v___y_3031_);
lean_dec(v___y_3030_);
lean_dec_ref(v___y_3029_);
lean_dec(v___y_3028_);
lean_dec_ref(v_as_3024_);
return v_res_3036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(lean_object* v_values_3037_, lean_object* v_starIdx_3038_, lean_object* v_children_3039_, lean_object* v_entries_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_){
_start:
{
lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; uint8_t v___x_3051_; 
v___x_3047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3047_, 0, v_starIdx_3038_);
lean_ctor_set(v___x_3047_, 1, v_children_3039_);
v___x_3048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3048_, 0, v_values_3037_);
lean_ctor_set(v___x_3048_, 1, v___x_3047_);
v___x_3049_ = lean_unsigned_to_nat(0u);
v___x_3050_ = lean_array_get_size(v_entries_3040_);
v___x_3051_ = lean_nat_dec_lt(v___x_3049_, v___x_3050_);
if (v___x_3051_ == 0)
{
lean_object* v___x_3052_; 
v___x_3052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3052_, 0, v___x_3048_);
return v___x_3052_;
}
else
{
uint8_t v___x_3053_; 
v___x_3053_ = lean_nat_dec_le(v___x_3050_, v___x_3050_);
if (v___x_3053_ == 0)
{
if (v___x_3051_ == 0)
{
lean_object* v___x_3054_; 
v___x_3054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3054_, 0, v___x_3048_);
return v___x_3054_;
}
else
{
size_t v___x_3055_; size_t v___x_3056_; lean_object* v___x_3057_; 
v___x_3055_ = ((size_t)0ULL);
v___x_3056_ = lean_usize_of_nat(v___x_3050_);
v___x_3057_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_entries_3040_, v___x_3055_, v___x_3056_, v___x_3048_, v_a_3041_, v_a_3042_, v_a_3043_, v_a_3044_, v_a_3045_);
return v___x_3057_;
}
}
else
{
size_t v___x_3058_; size_t v___x_3059_; lean_object* v___x_3060_; 
v___x_3058_ = ((size_t)0ULL);
v___x_3059_ = lean_usize_of_nat(v___x_3050_);
v___x_3060_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_entries_3040_, v___x_3058_, v___x_3059_, v___x_3048_, v_a_3041_, v_a_3042_, v_a_3043_, v_a_3044_, v_a_3045_);
return v___x_3060_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg___boxed(lean_object* v_values_3061_, lean_object* v_starIdx_3062_, lean_object* v_children_3063_, lean_object* v_entries_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_){
_start:
{
lean_object* v_res_3071_; 
v_res_3071_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(v_values_3061_, v_starIdx_3062_, v_children_3063_, v_entries_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
lean_dec(v_a_3069_);
lean_dec_ref(v_a_3068_);
lean_dec(v_a_3067_);
lean_dec_ref(v_a_3066_);
lean_dec(v_a_3065_);
lean_dec_ref(v_entries_3064_);
return v_res_3071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries(lean_object* v_00_u03b1_3072_, lean_object* v_values_3073_, lean_object* v_starIdx_3074_, lean_object* v_children_3075_, lean_object* v_entries_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_){
_start:
{
lean_object* v___x_3083_; 
v___x_3083_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(v_values_3073_, v_starIdx_3074_, v_children_3075_, v_entries_3076_, v_a_3077_, v_a_3078_, v_a_3079_, v_a_3080_, v_a_3081_);
return v___x_3083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries___boxed(lean_object* v_00_u03b1_3084_, lean_object* v_values_3085_, lean_object* v_starIdx_3086_, lean_object* v_children_3087_, lean_object* v_entries_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_){
_start:
{
lean_object* v_res_3095_; 
v_res_3095_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries(v_00_u03b1_3084_, v_values_3085_, v_starIdx_3086_, v_children_3087_, v_entries_3088_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_);
lean_dec(v_a_3093_);
lean_dec_ref(v_a_3092_);
lean_dec(v_a_3091_);
lean_dec_ref(v_a_3090_);
lean_dec(v_a_3089_);
lean_dec_ref(v_entries_3088_);
return v_res_3095_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0(lean_object* v_00_u03b1_3096_, lean_object* v_as_3097_, size_t v_i_3098_, size_t v_stop_3099_, lean_object* v_b_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_){
_start:
{
lean_object* v___x_3107_; 
v___x_3107_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_as_3097_, v_i_3098_, v_stop_3099_, v_b_3100_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_);
return v___x_3107_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___boxed(lean_object* v_00_u03b1_3108_, lean_object* v_as_3109_, lean_object* v_i_3110_, lean_object* v_stop_3111_, lean_object* v_b_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_){
_start:
{
size_t v_i_boxed_3119_; size_t v_stop_boxed_3120_; lean_object* v_res_3121_; 
v_i_boxed_3119_ = lean_unbox_usize(v_i_3110_);
lean_dec(v_i_3110_);
v_stop_boxed_3120_ = lean_unbox_usize(v_stop_3111_);
lean_dec(v_stop_3111_);
v_res_3121_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0(v_00_u03b1_3108_, v_as_3109_, v_i_boxed_3119_, v_stop_boxed_3120_, v_b_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_);
lean_dec(v___y_3117_);
lean_dec_ref(v___y_3116_);
lean_dec(v___y_3115_);
lean_dec_ref(v___y_3114_);
lean_dec(v___y_3113_);
lean_dec_ref(v_as_3109_);
return v_res_3121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode___redArg(lean_object* v_c_3122_, lean_object* v_a_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_, lean_object* v_a_3127_){
_start:
{
lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v_values_3132_; lean_object* v_star_3133_; lean_object* v_children_3134_; lean_object* v_pending_3135_; lean_object* v___x_3137_; uint8_t v_isShared_3138_; uint8_t v_isSharedCheck_3165_; 
v___x_3129_ = lean_st_ref_get(v_a_3123_);
v___x_3130_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0);
v___x_3131_ = lean_array_get(v___x_3130_, v___x_3129_, v_c_3122_);
lean_dec(v___x_3129_);
v_values_3132_ = lean_ctor_get(v___x_3131_, 0);
v_star_3133_ = lean_ctor_get(v___x_3131_, 1);
v_children_3134_ = lean_ctor_get(v___x_3131_, 2);
v_pending_3135_ = lean_ctor_get(v___x_3131_, 3);
v_isSharedCheck_3165_ = !lean_is_exclusive(v___x_3131_);
if (v_isSharedCheck_3165_ == 0)
{
v___x_3137_ = v___x_3131_;
v_isShared_3138_ = v_isSharedCheck_3165_;
goto v_resetjp_3136_;
}
else
{
lean_inc(v_pending_3135_);
lean_inc(v_children_3134_);
lean_inc(v_star_3133_);
lean_inc(v_values_3132_);
lean_dec(v___x_3131_);
v___x_3137_ = lean_box(0);
v_isShared_3138_ = v_isSharedCheck_3165_;
goto v_resetjp_3136_;
}
v_resetjp_3136_:
{
lean_object* v___x_3139_; lean_object* v___x_3140_; uint8_t v___x_3141_; 
v___x_3139_ = lean_array_get_size(v_pending_3135_);
v___x_3140_ = lean_unsigned_to_nat(0u);
v___x_3141_ = lean_nat_dec_eq(v___x_3139_, v___x_3140_);
if (v___x_3141_ == 0)
{
lean_object* v___x_3142_; lean_object* v___x_3143_; 
v___x_3142_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_c_3122_, v___x_3130_, v_a_3123_);
lean_dec_ref(v___x_3142_);
v___x_3143_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(v_values_3132_, v_star_3133_, v_children_3134_, v_pending_3135_, v_a_3123_, v_a_3124_, v_a_3125_, v_a_3126_, v_a_3127_);
lean_dec_ref(v_pending_3135_);
if (lean_obj_tag(v___x_3143_) == 0)
{
lean_object* v_a_3144_; lean_object* v_snd_3145_; lean_object* v_fst_3146_; lean_object* v_fst_3147_; lean_object* v_snd_3148_; lean_object* v___x_3149_; lean_object* v___x_3151_; 
v_a_3144_ = lean_ctor_get(v___x_3143_, 0);
lean_inc(v_a_3144_);
lean_dec_ref_known(v___x_3143_, 1);
v_snd_3145_ = lean_ctor_get(v_a_3144_, 1);
v_fst_3146_ = lean_ctor_get(v_a_3144_, 0);
v_fst_3147_ = lean_ctor_get(v_snd_3145_, 0);
v_snd_3148_ = lean_ctor_get(v_snd_3145_, 1);
v___x_3149_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__3));
lean_inc(v_snd_3148_);
lean_inc(v_fst_3147_);
lean_inc(v_fst_3146_);
if (v_isShared_3138_ == 0)
{
lean_ctor_set(v___x_3137_, 3, v___x_3149_);
lean_ctor_set(v___x_3137_, 2, v_snd_3148_);
lean_ctor_set(v___x_3137_, 1, v_fst_3147_);
lean_ctor_set(v___x_3137_, 0, v_fst_3146_);
v___x_3151_ = v___x_3137_;
goto v_reusejp_3150_;
}
else
{
lean_object* v_reuseFailAlloc_3161_; 
v_reuseFailAlloc_3161_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3161_, 0, v_fst_3146_);
lean_ctor_set(v_reuseFailAlloc_3161_, 1, v_fst_3147_);
lean_ctor_set(v_reuseFailAlloc_3161_, 2, v_snd_3148_);
lean_ctor_set(v_reuseFailAlloc_3161_, 3, v___x_3149_);
v___x_3151_ = v_reuseFailAlloc_3161_;
goto v_reusejp_3150_;
}
v_reusejp_3150_:
{
lean_object* v___x_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3159_; 
v___x_3152_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_c_3122_, v___x_3151_, v_a_3123_);
v_isSharedCheck_3159_ = !lean_is_exclusive(v___x_3152_);
if (v_isSharedCheck_3159_ == 0)
{
lean_object* v_unused_3160_; 
v_unused_3160_ = lean_ctor_get(v___x_3152_, 0);
lean_dec(v_unused_3160_);
v___x_3154_ = v___x_3152_;
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
else
{
lean_dec(v___x_3152_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
v_resetjp_3153_:
{
lean_object* v___x_3157_; 
if (v_isShared_3155_ == 0)
{
lean_ctor_set(v___x_3154_, 0, v_a_3144_);
v___x_3157_ = v___x_3154_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v_a_3144_);
v___x_3157_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
return v___x_3157_;
}
}
}
}
else
{
lean_del_object(v___x_3137_);
return v___x_3143_;
}
}
else
{
lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; 
lean_del_object(v___x_3137_);
lean_dec_ref(v_pending_3135_);
v___x_3162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3162_, 0, v_star_3133_);
lean_ctor_set(v___x_3162_, 1, v_children_3134_);
v___x_3163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3163_, 0, v_values_3132_);
lean_ctor_set(v___x_3163_, 1, v___x_3162_);
v___x_3164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3164_, 0, v___x_3163_);
return v___x_3164_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode___redArg___boxed(lean_object* v_c_3166_, lean_object* v_a_3167_, lean_object* v_a_3168_, lean_object* v_a_3169_, lean_object* v_a_3170_, lean_object* v_a_3171_, lean_object* v_a_3172_){
_start:
{
lean_object* v_res_3173_; 
v_res_3173_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_c_3166_, v_a_3167_, v_a_3168_, v_a_3169_, v_a_3170_, v_a_3171_);
lean_dec(v_a_3171_);
lean_dec_ref(v_a_3170_);
lean_dec(v_a_3169_);
lean_dec_ref(v_a_3168_);
lean_dec(v_a_3167_);
lean_dec(v_c_3166_);
return v_res_3173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode(lean_object* v_00_u03b1_3174_, lean_object* v_c_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_, lean_object* v_a_3178_, lean_object* v_a_3179_, lean_object* v_a_3180_){
_start:
{
lean_object* v___x_3182_; 
v___x_3182_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_c_3175_, v_a_3176_, v_a_3177_, v_a_3178_, v_a_3179_, v_a_3180_);
return v___x_3182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode___boxed(lean_object* v_00_u03b1_3183_, lean_object* v_c_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_){
_start:
{
lean_object* v_res_3191_; 
v_res_3191_ = l_Lean_Meta_LazyDiscrTree_evalNode(v_00_u03b1_3183_, v_c_3184_, v_a_3185_, v_a_3186_, v_a_3187_, v_a_3188_, v_a_3189_);
lean_dec(v_a_3189_);
lean_dec_ref(v_a_3188_);
lean_dec(v_a_3187_);
lean_dec_ref(v_a_3186_);
lean_dec(v_a_3185_);
lean_dec(v_c_3184_);
return v_res_3191_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(lean_object* v_a_3192_, lean_object* v_fallback_3193_, lean_object* v_x_3194_){
_start:
{
if (lean_obj_tag(v_x_3194_) == 0)
{
lean_inc(v_fallback_3193_);
return v_fallback_3193_;
}
else
{
lean_object* v_key_3195_; lean_object* v_value_3196_; lean_object* v_tail_3197_; uint8_t v___x_3198_; 
v_key_3195_ = lean_ctor_get(v_x_3194_, 0);
v_value_3196_ = lean_ctor_get(v_x_3194_, 1);
v_tail_3197_ = lean_ctor_get(v_x_3194_, 2);
v___x_3198_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_3195_, v_a_3192_);
if (v___x_3198_ == 0)
{
v_x_3194_ = v_tail_3197_;
goto _start;
}
else
{
lean_inc(v_value_3196_);
return v_value_3196_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg___boxed(lean_object* v_a_3200_, lean_object* v_fallback_3201_, lean_object* v_x_3202_){
_start:
{
lean_object* v_res_3203_; 
v_res_3203_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(v_a_3200_, v_fallback_3201_, v_x_3202_);
lean_dec(v_x_3202_);
lean_dec(v_fallback_3201_);
lean_dec(v_a_3200_);
return v_res_3203_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(lean_object* v_m_3204_, lean_object* v_a_3205_, lean_object* v_fallback_3206_){
_start:
{
lean_object* v_buckets_3207_; lean_object* v___x_3208_; uint64_t v___x_3209_; uint64_t v___x_3210_; uint64_t v___x_3211_; uint64_t v_fold_3212_; uint64_t v___x_3213_; uint64_t v___x_3214_; uint64_t v___x_3215_; size_t v___x_3216_; size_t v___x_3217_; size_t v___x_3218_; size_t v___x_3219_; size_t v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; 
v_buckets_3207_ = lean_ctor_get(v_m_3204_, 1);
v___x_3208_ = lean_array_get_size(v_buckets_3207_);
v___x_3209_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_a_3205_);
v___x_3210_ = 32ULL;
v___x_3211_ = lean_uint64_shift_right(v___x_3209_, v___x_3210_);
v_fold_3212_ = lean_uint64_xor(v___x_3209_, v___x_3211_);
v___x_3213_ = 16ULL;
v___x_3214_ = lean_uint64_shift_right(v_fold_3212_, v___x_3213_);
v___x_3215_ = lean_uint64_xor(v_fold_3212_, v___x_3214_);
v___x_3216_ = lean_uint64_to_usize(v___x_3215_);
v___x_3217_ = lean_usize_of_nat(v___x_3208_);
v___x_3218_ = ((size_t)1ULL);
v___x_3219_ = lean_usize_sub(v___x_3217_, v___x_3218_);
v___x_3220_ = lean_usize_land(v___x_3216_, v___x_3219_);
v___x_3221_ = lean_array_uget_borrowed(v_buckets_3207_, v___x_3220_);
v___x_3222_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(v_a_3205_, v_fallback_3206_, v___x_3221_);
return v___x_3222_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg___boxed(lean_object* v_m_3223_, lean_object* v_a_3224_, lean_object* v_fallback_3225_){
_start:
{
lean_object* v_res_3226_; 
v_res_3226_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_m_3223_, v_a_3224_, v_fallback_3225_);
lean_dec(v_fallback_3225_);
lean_dec(v_a_3224_);
lean_dec_ref(v_m_3223_);
return v_res_3226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg(lean_object* v_next_3227_, lean_object* v_rest_3228_, lean_object* v_a_3229_, lean_object* v_a_3230_, lean_object* v_a_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_){
_start:
{
lean_object* v___x_3235_; uint8_t v___x_3236_; 
v___x_3235_ = lean_unsigned_to_nat(0u);
v___x_3236_ = lean_nat_dec_eq(v_next_3227_, v___x_3235_);
if (v___x_3236_ == 0)
{
lean_object* v___x_3237_; 
v___x_3237_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_next_3227_, v_a_3229_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_);
if (lean_obj_tag(v___x_3237_) == 0)
{
lean_object* v_a_3238_; lean_object* v___x_3240_; uint8_t v_isShared_3241_; uint8_t v_isSharedCheck_3263_; 
v_a_3238_ = lean_ctor_get(v___x_3237_, 0);
v_isSharedCheck_3263_ = !lean_is_exclusive(v___x_3237_);
if (v_isSharedCheck_3263_ == 0)
{
v___x_3240_ = v___x_3237_;
v_isShared_3241_ = v_isSharedCheck_3263_;
goto v_resetjp_3239_;
}
else
{
lean_inc(v_a_3238_);
lean_dec(v___x_3237_);
v___x_3240_ = lean_box(0);
v_isShared_3241_ = v_isSharedCheck_3263_;
goto v_resetjp_3239_;
}
v_resetjp_3239_:
{
lean_object* v_snd_3242_; 
v_snd_3242_ = lean_ctor_get(v_a_3238_, 1);
lean_inc(v_snd_3242_);
lean_dec(v_a_3238_);
if (lean_obj_tag(v_rest_3228_) == 0)
{
lean_object* v_fst_3243_; lean_object* v_snd_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3252_; 
v_fst_3243_ = lean_ctor_get(v_snd_3242_, 0);
lean_inc(v_fst_3243_);
v_snd_3244_ = lean_ctor_get(v_snd_3242_, 1);
lean_inc(v_snd_3244_);
lean_dec(v_snd_3242_);
v___x_3245_ = lean_st_ref_take(v_a_3229_);
v___x_3246_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_3247_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3247_, 0, v___x_3246_);
lean_ctor_set(v___x_3247_, 1, v_fst_3243_);
lean_ctor_set(v___x_3247_, 2, v_snd_3244_);
lean_ctor_set(v___x_3247_, 3, v___x_3246_);
v___x_3248_ = lean_array_set(v___x_3245_, v_next_3227_, v___x_3247_);
lean_dec(v_next_3227_);
v___x_3249_ = lean_st_ref_set(v_a_3229_, v___x_3248_);
v___x_3250_ = lean_box(0);
if (v_isShared_3241_ == 0)
{
lean_ctor_set(v___x_3240_, 0, v___x_3250_);
v___x_3252_ = v___x_3240_;
goto v_reusejp_3251_;
}
else
{
lean_object* v_reuseFailAlloc_3253_; 
v_reuseFailAlloc_3253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3253_, 0, v___x_3250_);
v___x_3252_ = v_reuseFailAlloc_3253_;
goto v_reusejp_3251_;
}
v_reusejp_3251_:
{
return v___x_3252_;
}
}
else
{
lean_object* v_fst_3254_; lean_object* v_snd_3255_; lean_object* v_head_3256_; lean_object* v_tail_3257_; lean_object* v___x_3258_; uint8_t v___x_3259_; 
lean_del_object(v___x_3240_);
lean_dec(v_next_3227_);
v_fst_3254_ = lean_ctor_get(v_snd_3242_, 0);
lean_inc(v_fst_3254_);
v_snd_3255_ = lean_ctor_get(v_snd_3242_, 1);
lean_inc(v_snd_3255_);
lean_dec(v_snd_3242_);
v_head_3256_ = lean_ctor_get(v_rest_3228_, 0);
v_tail_3257_ = lean_ctor_get(v_rest_3228_, 1);
v___x_3258_ = lean_box(3);
v___x_3259_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_head_3256_, v___x_3258_);
if (v___x_3259_ == 0)
{
lean_object* v___x_3260_; 
lean_dec(v_fst_3254_);
v___x_3260_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_snd_3255_, v_head_3256_, v___x_3235_);
lean_dec(v_snd_3255_);
v_next_3227_ = v___x_3260_;
v_rest_3228_ = v_tail_3257_;
goto _start;
}
else
{
lean_dec(v_snd_3255_);
v_next_3227_ = v_fst_3254_;
v_rest_3228_ = v_tail_3257_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3264_; lean_object* v___x_3266_; uint8_t v_isShared_3267_; uint8_t v_isSharedCheck_3271_; 
lean_dec(v_next_3227_);
v_a_3264_ = lean_ctor_get(v___x_3237_, 0);
v_isSharedCheck_3271_ = !lean_is_exclusive(v___x_3237_);
if (v_isSharedCheck_3271_ == 0)
{
v___x_3266_ = v___x_3237_;
v_isShared_3267_ = v_isSharedCheck_3271_;
goto v_resetjp_3265_;
}
else
{
lean_inc(v_a_3264_);
lean_dec(v___x_3237_);
v___x_3266_ = lean_box(0);
v_isShared_3267_ = v_isSharedCheck_3271_;
goto v_resetjp_3265_;
}
v_resetjp_3265_:
{
lean_object* v___x_3269_; 
if (v_isShared_3267_ == 0)
{
v___x_3269_ = v___x_3266_;
goto v_reusejp_3268_;
}
else
{
lean_object* v_reuseFailAlloc_3270_; 
v_reuseFailAlloc_3270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3270_, 0, v_a_3264_);
v___x_3269_ = v_reuseFailAlloc_3270_;
goto v_reusejp_3268_;
}
v_reusejp_3268_:
{
return v___x_3269_;
}
}
}
}
else
{
lean_object* v___x_3272_; lean_object* v___x_3273_; 
lean_dec(v_next_3227_);
v___x_3272_ = lean_box(0);
v___x_3273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3273_, 0, v___x_3272_);
return v___x_3273_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg___boxed(lean_object* v_next_3274_, lean_object* v_rest_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_){
_start:
{
lean_object* v_res_3282_; 
v_res_3282_ = l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg(v_next_3274_, v_rest_3275_, v_a_3276_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_);
lean_dec(v_a_3280_);
lean_dec_ref(v_a_3279_);
lean_dec(v_a_3278_);
lean_dec_ref(v_a_3277_);
lean_dec(v_a_3276_);
lean_dec(v_rest_3275_);
return v_res_3282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux(lean_object* v_00_u03b1_3283_, lean_object* v_next_3284_, lean_object* v_rest_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_, lean_object* v_a_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_){
_start:
{
lean_object* v___x_3292_; 
v___x_3292_ = l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg(v_next_3284_, v_rest_3285_, v_a_3286_, v_a_3287_, v_a_3288_, v_a_3289_, v_a_3290_);
return v___x_3292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux___boxed(lean_object* v_00_u03b1_3293_, lean_object* v_next_3294_, lean_object* v_rest_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_){
_start:
{
lean_object* v_res_3302_; 
v_res_3302_ = l_Lean_Meta_LazyDiscrTree_dropKeyAux(v_00_u03b1_3293_, v_next_3294_, v_rest_3295_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_, v_a_3300_);
lean_dec(v_a_3300_);
lean_dec_ref(v_a_3299_);
lean_dec(v_a_3298_);
lean_dec_ref(v_a_3297_);
lean_dec(v_a_3296_);
lean_dec(v_rest_3295_);
return v_res_3302_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0(lean_object* v_00_u03b2_3303_, lean_object* v_m_3304_, lean_object* v_a_3305_, lean_object* v_fallback_3306_){
_start:
{
lean_object* v___x_3307_; 
v___x_3307_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_m_3304_, v_a_3305_, v_fallback_3306_);
return v___x_3307_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___boxed(lean_object* v_00_u03b2_3308_, lean_object* v_m_3309_, lean_object* v_a_3310_, lean_object* v_fallback_3311_){
_start:
{
lean_object* v_res_3312_; 
v_res_3312_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0(v_00_u03b2_3308_, v_m_3309_, v_a_3310_, v_fallback_3311_);
lean_dec(v_fallback_3311_);
lean_dec(v_a_3310_);
lean_dec_ref(v_m_3309_);
return v_res_3312_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0(lean_object* v_00_u03b2_3313_, lean_object* v_a_3314_, lean_object* v_fallback_3315_, lean_object* v_x_3316_){
_start:
{
lean_object* v___x_3317_; 
v___x_3317_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(v_a_3314_, v_fallback_3315_, v_x_3316_);
return v___x_3317_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3318_, lean_object* v_a_3319_, lean_object* v_fallback_3320_, lean_object* v_x_3321_){
_start:
{
lean_object* v_res_3322_; 
v_res_3322_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0(v_00_u03b2_3318_, v_a_3319_, v_fallback_3320_, v_x_3321_);
lean_dec(v_x_3321_);
lean_dec(v_fallback_3320_);
lean_dec(v_a_3319_);
return v_res_3322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey___redArg(lean_object* v_t_3323_, lean_object* v_path_3324_, lean_object* v_a_3325_, lean_object* v_a_3326_, lean_object* v_a_3327_, lean_object* v_a_3328_){
_start:
{
if (lean_obj_tag(v_path_3324_) == 0)
{
lean_object* v___x_3330_; 
v___x_3330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3330_, 0, v_t_3323_);
return v___x_3330_;
}
else
{
lean_object* v_head_3331_; lean_object* v_tail_3332_; lean_object* v_roots_3333_; lean_object* v___x_3334_; lean_object* v_idx_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; 
v_head_3331_ = lean_ctor_get(v_path_3324_, 0);
lean_inc(v_head_3331_);
v_tail_3332_ = lean_ctor_get(v_path_3324_, 1);
lean_inc(v_tail_3332_);
lean_dec_ref_known(v_path_3324_, 2);
v_roots_3333_ = lean_ctor_get(v_t_3323_, 1);
v___x_3334_ = lean_unsigned_to_nat(0u);
v_idx_3335_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_roots_3333_, v_head_3331_, v___x_3334_);
lean_dec(v_head_3331_);
v___x_3336_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_dropKeyAux___boxed), 9, 3);
lean_closure_set(v___x_3336_, 0, lean_box(0));
lean_closure_set(v___x_3336_, 1, v_idx_3335_);
lean_closure_set(v___x_3336_, 2, v_tail_3332_);
v___x_3337_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_t_3323_, v___x_3336_, v_a_3325_, v_a_3326_, v_a_3327_, v_a_3328_);
if (lean_obj_tag(v___x_3337_) == 0)
{
lean_object* v_a_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3346_; 
v_a_3338_ = lean_ctor_get(v___x_3337_, 0);
v_isSharedCheck_3346_ = !lean_is_exclusive(v___x_3337_);
if (v_isSharedCheck_3346_ == 0)
{
v___x_3340_ = v___x_3337_;
v_isShared_3341_ = v_isSharedCheck_3346_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_a_3338_);
lean_dec(v___x_3337_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3346_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
lean_object* v_snd_3342_; lean_object* v___x_3344_; 
v_snd_3342_ = lean_ctor_get(v_a_3338_, 1);
lean_inc(v_snd_3342_);
lean_dec(v_a_3338_);
if (v_isShared_3341_ == 0)
{
lean_ctor_set(v___x_3340_, 0, v_snd_3342_);
v___x_3344_ = v___x_3340_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v_snd_3342_);
v___x_3344_ = v_reuseFailAlloc_3345_;
goto v_reusejp_3343_;
}
v_reusejp_3343_:
{
return v___x_3344_;
}
}
}
else
{
lean_object* v_a_3347_; lean_object* v___x_3349_; uint8_t v_isShared_3350_; uint8_t v_isSharedCheck_3354_; 
v_a_3347_ = lean_ctor_get(v___x_3337_, 0);
v_isSharedCheck_3354_ = !lean_is_exclusive(v___x_3337_);
if (v_isSharedCheck_3354_ == 0)
{
v___x_3349_ = v___x_3337_;
v_isShared_3350_ = v_isSharedCheck_3354_;
goto v_resetjp_3348_;
}
else
{
lean_inc(v_a_3347_);
lean_dec(v___x_3337_);
v___x_3349_ = lean_box(0);
v_isShared_3350_ = v_isSharedCheck_3354_;
goto v_resetjp_3348_;
}
v_resetjp_3348_:
{
lean_object* v___x_3352_; 
if (v_isShared_3350_ == 0)
{
v___x_3352_ = v___x_3349_;
goto v_reusejp_3351_;
}
else
{
lean_object* v_reuseFailAlloc_3353_; 
v_reuseFailAlloc_3353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3353_, 0, v_a_3347_);
v___x_3352_ = v_reuseFailAlloc_3353_;
goto v_reusejp_3351_;
}
v_reusejp_3351_:
{
return v___x_3352_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey___redArg___boxed(lean_object* v_t_3355_, lean_object* v_path_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_){
_start:
{
lean_object* v_res_3362_; 
v_res_3362_ = l_Lean_Meta_LazyDiscrTree_dropKey___redArg(v_t_3355_, v_path_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_);
lean_dec(v_a_3360_);
lean_dec_ref(v_a_3359_);
lean_dec(v_a_3358_);
lean_dec_ref(v_a_3357_);
return v_res_3362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey(lean_object* v_00_u03b1_3363_, lean_object* v_t_3364_, lean_object* v_path_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_){
_start:
{
lean_object* v___x_3371_; 
v___x_3371_ = l_Lean_Meta_LazyDiscrTree_dropKey___redArg(v_t_3364_, v_path_3365_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_);
return v___x_3371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey___boxed(lean_object* v_00_u03b1_3372_, lean_object* v_t_3373_, lean_object* v_path_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_){
_start:
{
lean_object* v_res_3380_; 
v_res_3380_ = l_Lean_Meta_LazyDiscrTree_dropKey(v_00_u03b1_3372_, v_t_3373_, v_path_3374_, v_a_3375_, v_a_3376_, v_a_3377_, v_a_3378_);
lean_dec(v_a_3378_);
lean_dec_ref(v_a_3377_);
lean_dec(v_a_3376_);
lean_dec_ref(v_a_3375_);
return v_res_3380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(lean_object* v_score_3383_, lean_object* v_e_3384_, lean_object* v_a_3385_){
_start:
{
lean_object* v___x_3386_; uint8_t v___x_3387_; 
v___x_3386_ = lean_array_get_size(v_a_3385_);
v___x_3387_ = lean_nat_dec_lt(v___x_3386_, v_score_3383_);
if (v___x_3387_ == 0)
{
lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; 
v___x_3388_ = lean_unsigned_to_nat(1u);
v___x_3389_ = lean_mk_empty_array_with_capacity(v___x_3388_);
v___x_3390_ = lean_array_push(v___x_3389_, v_e_3384_);
v___x_3391_ = lean_array_push(v_a_3385_, v___x_3390_);
return v___x_3391_;
}
else
{
lean_object* v___x_3392_; lean_object* v___x_3393_; 
v___x_3392_ = ((lean_object*)(l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg___closed__0));
v___x_3393_ = lean_array_push(v_a_3385_, v___x_3392_);
v_a_3385_ = v___x_3393_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg___boxed(lean_object* v_score_3395_, lean_object* v_e_3396_, lean_object* v_a_3397_){
_start:
{
lean_object* v_res_3398_; 
v_res_3398_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(v_score_3395_, v_e_3396_, v_a_3397_);
lean_dec(v_score_3395_);
return v_res_3398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop(lean_object* v_00_u03b1_3399_, lean_object* v_score_3400_, lean_object* v_e_3401_, lean_object* v_a_3402_){
_start:
{
lean_object* v___x_3403_; 
v___x_3403_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(v_score_3400_, v_e_3401_, v_a_3402_);
return v___x_3403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___boxed(lean_object* v_00_u03b1_3404_, lean_object* v_score_3405_, lean_object* v_e_3406_, lean_object* v_a_3407_){
_start:
{
lean_object* v_res_3408_; 
v_res_3408_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop(v_00_u03b1_3404_, v_score_3405_, v_e_3406_, v_a_3407_);
lean_dec(v_score_3405_);
return v_res_3408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(lean_object* v_r_3409_, lean_object* v_score_3410_, lean_object* v_e_3411_){
_start:
{
lean_object* v___x_3412_; lean_object* v___x_3413_; uint8_t v___x_3414_; 
v___x_3412_ = lean_array_get_size(v_e_3411_);
v___x_3413_ = lean_unsigned_to_nat(0u);
v___x_3414_ = lean_nat_dec_eq(v___x_3412_, v___x_3413_);
if (v___x_3414_ == 0)
{
lean_object* v___x_3415_; uint8_t v___x_3416_; 
v___x_3415_ = lean_array_get_size(v_r_3409_);
v___x_3416_ = lean_nat_dec_lt(v_score_3410_, v___x_3415_);
if (v___x_3416_ == 0)
{
lean_object* v___x_3417_; 
v___x_3417_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(v_score_3410_, v_e_3411_, v_r_3409_);
return v___x_3417_;
}
else
{
if (v___x_3416_ == 0)
{
lean_dec_ref(v_e_3411_);
return v_r_3409_;
}
else
{
lean_object* v_v_3418_; lean_object* v___x_3419_; lean_object* v_xs_x27_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; 
v_v_3418_ = lean_array_fget(v_r_3409_, v_score_3410_);
v___x_3419_ = lean_box(0);
v_xs_x27_3420_ = lean_array_fset(v_r_3409_, v_score_3410_, v___x_3419_);
v___x_3421_ = lean_array_push(v_v_3418_, v_e_3411_);
v___x_3422_ = lean_array_fset(v_xs_x27_3420_, v_score_3410_, v___x_3421_);
return v___x_3422_;
}
}
}
else
{
lean_dec_ref(v_e_3411_);
return v_r_3409_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg___boxed(lean_object* v_r_3423_, lean_object* v_score_3424_, lean_object* v_e_3425_){
_start:
{
lean_object* v_res_3426_; 
v_res_3426_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v_r_3423_, v_score_3424_, v_e_3425_);
lean_dec(v_score_3424_);
return v_res_3426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push(lean_object* v_00_u03b1_3427_, lean_object* v_r_3428_, lean_object* v_score_3429_, lean_object* v_e_3430_){
_start:
{
lean_object* v___x_3431_; 
v___x_3431_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v_r_3428_, v_score_3429_, v_e_3430_);
return v___x_3431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push___boxed(lean_object* v_00_u03b1_3432_, lean_object* v_r_3433_, lean_object* v_score_3434_, lean_object* v_e_3435_){
_start:
{
lean_object* v_res_3436_; 
v_res_3436_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push(v_00_u03b1_3432_, v_r_3433_, v_score_3434_, v_e_3435_);
lean_dec(v_score_3434_);
return v_res_3436_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(lean_object* v_as_3437_, size_t v_i_3438_, size_t v_stop_3439_, lean_object* v_b_3440_){
_start:
{
uint8_t v___x_3441_; 
v___x_3441_ = lean_usize_dec_eq(v_i_3438_, v_stop_3439_);
if (v___x_3441_ == 0)
{
lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; size_t v___x_3445_; size_t v___x_3446_; 
v___x_3442_ = lean_array_uget_borrowed(v_as_3437_, v_i_3438_);
v___x_3443_ = lean_array_get_size(v___x_3442_);
v___x_3444_ = lean_nat_add(v_b_3440_, v___x_3443_);
lean_dec(v_b_3440_);
v___x_3445_ = ((size_t)1ULL);
v___x_3446_ = lean_usize_add(v_i_3438_, v___x_3445_);
v_i_3438_ = v___x_3446_;
v_b_3440_ = v___x_3444_;
goto _start;
}
else
{
return v_b_3440_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg___boxed(lean_object* v_as_3448_, lean_object* v_i_3449_, lean_object* v_stop_3450_, lean_object* v_b_3451_){
_start:
{
size_t v_i_boxed_3452_; size_t v_stop_boxed_3453_; lean_object* v_res_3454_; 
v_i_boxed_3452_ = lean_unbox_usize(v_i_3449_);
lean_dec(v_i_3449_);
v_stop_boxed_3453_ = lean_unbox_usize(v_stop_3450_);
lean_dec(v_stop_3450_);
v_res_3454_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v_as_3448_, v_i_boxed_3452_, v_stop_boxed_3453_, v_b_3451_);
lean_dec_ref(v_as_3448_);
return v_res_3454_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(lean_object* v_as_3455_, size_t v_i_3456_, size_t v_stop_3457_, lean_object* v_b_3458_){
_start:
{
lean_object* v___y_3460_; uint8_t v___x_3464_; 
v___x_3464_ = lean_usize_dec_eq(v_i_3456_, v_stop_3457_);
if (v___x_3464_ == 0)
{
lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; uint8_t v___x_3468_; 
v___x_3465_ = lean_array_uget_borrowed(v_as_3455_, v_i_3456_);
v___x_3466_ = lean_unsigned_to_nat(0u);
v___x_3467_ = lean_array_get_size(v___x_3465_);
v___x_3468_ = lean_nat_dec_lt(v___x_3466_, v___x_3467_);
if (v___x_3468_ == 0)
{
v___y_3460_ = v_b_3458_;
goto v___jp_3459_;
}
else
{
uint8_t v___x_3469_; 
v___x_3469_ = lean_nat_dec_le(v___x_3467_, v___x_3467_);
if (v___x_3469_ == 0)
{
if (v___x_3468_ == 0)
{
v___y_3460_ = v_b_3458_;
goto v___jp_3459_;
}
else
{
size_t v___x_3470_; size_t v___x_3471_; lean_object* v___x_3472_; 
v___x_3470_ = ((size_t)0ULL);
v___x_3471_ = lean_usize_of_nat(v___x_3467_);
v___x_3472_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v___x_3465_, v___x_3470_, v___x_3471_, v_b_3458_);
v___y_3460_ = v___x_3472_;
goto v___jp_3459_;
}
}
else
{
size_t v___x_3473_; size_t v___x_3474_; lean_object* v___x_3475_; 
v___x_3473_ = ((size_t)0ULL);
v___x_3474_ = lean_usize_of_nat(v___x_3467_);
v___x_3475_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v___x_3465_, v___x_3473_, v___x_3474_, v_b_3458_);
v___y_3460_ = v___x_3475_;
goto v___jp_3459_;
}
}
}
else
{
return v_b_3458_;
}
v___jp_3459_:
{
size_t v___x_3461_; size_t v___x_3462_; 
v___x_3461_ = ((size_t)1ULL);
v___x_3462_ = lean_usize_add(v_i_3456_, v___x_3461_);
v_i_3456_ = v___x_3462_;
v_b_3458_ = v___y_3460_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg___boxed(lean_object* v_as_3476_, lean_object* v_i_3477_, lean_object* v_stop_3478_, lean_object* v_b_3479_){
_start:
{
size_t v_i_boxed_3480_; size_t v_stop_boxed_3481_; lean_object* v_res_3482_; 
v_i_boxed_3480_ = lean_unbox_usize(v_i_3477_);
lean_dec(v_i_3477_);
v_stop_boxed_3481_ = lean_unbox_usize(v_stop_3478_);
lean_dec(v_stop_3478_);
v_res_3482_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_as_3476_, v_i_boxed_3480_, v_stop_boxed_3481_, v_b_3479_);
lean_dec_ref(v_as_3476_);
return v_res_3482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(lean_object* v_mr_3483_){
_start:
{
lean_object* v___x_3484_; lean_object* v___x_3485_; uint8_t v___x_3486_; 
v___x_3484_ = lean_unsigned_to_nat(0u);
v___x_3485_ = lean_array_get_size(v_mr_3483_);
v___x_3486_ = lean_nat_dec_lt(v___x_3484_, v___x_3485_);
if (v___x_3486_ == 0)
{
return v___x_3484_;
}
else
{
uint8_t v___x_3487_; 
v___x_3487_ = lean_nat_dec_le(v___x_3485_, v___x_3485_);
if (v___x_3487_ == 0)
{
if (v___x_3486_ == 0)
{
return v___x_3484_;
}
else
{
size_t v___x_3488_; size_t v___x_3489_; lean_object* v___x_3490_; 
v___x_3488_ = ((size_t)0ULL);
v___x_3489_ = lean_usize_of_nat(v___x_3485_);
v___x_3490_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_mr_3483_, v___x_3488_, v___x_3489_, v___x_3484_);
return v___x_3490_;
}
}
else
{
size_t v___x_3491_; size_t v___x_3492_; lean_object* v___x_3493_; 
v___x_3491_ = ((size_t)0ULL);
v___x_3492_ = lean_usize_of_nat(v___x_3485_);
v___x_3493_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_mr_3483_, v___x_3491_, v___x_3492_, v___x_3484_);
return v___x_3493_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg___boxed(lean_object* v_mr_3494_){
_start:
{
lean_object* v_res_3495_; 
v_res_3495_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_mr_3494_);
lean_dec_ref(v_mr_3494_);
return v_res_3495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size(lean_object* v_00_u03b1_3496_, lean_object* v_mr_3497_){
_start:
{
lean_object* v___x_3498_; 
v___x_3498_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_mr_3497_);
return v___x_3498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size___boxed(lean_object* v_00_u03b1_3499_, lean_object* v_mr_3500_){
_start:
{
lean_object* v_res_3501_; 
v_res_3501_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size(v_00_u03b1_3499_, v_mr_3500_);
lean_dec_ref(v_mr_3500_);
return v_res_3501_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0(lean_object* v_00_u03b1_3502_, lean_object* v_as_3503_, size_t v_i_3504_, size_t v_stop_3505_, lean_object* v_b_3506_){
_start:
{
lean_object* v___x_3507_; 
v___x_3507_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v_as_3503_, v_i_3504_, v_stop_3505_, v_b_3506_);
return v___x_3507_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___boxed(lean_object* v_00_u03b1_3508_, lean_object* v_as_3509_, lean_object* v_i_3510_, lean_object* v_stop_3511_, lean_object* v_b_3512_){
_start:
{
size_t v_i_boxed_3513_; size_t v_stop_boxed_3514_; lean_object* v_res_3515_; 
v_i_boxed_3513_ = lean_unbox_usize(v_i_3510_);
lean_dec(v_i_3510_);
v_stop_boxed_3514_ = lean_unbox_usize(v_stop_3511_);
lean_dec(v_stop_3511_);
v_res_3515_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0(v_00_u03b1_3508_, v_as_3509_, v_i_boxed_3513_, v_stop_boxed_3514_, v_b_3512_);
lean_dec_ref(v_as_3509_);
return v_res_3515_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1(lean_object* v_00_u03b1_3516_, lean_object* v_as_3517_, size_t v_i_3518_, size_t v_stop_3519_, lean_object* v_b_3520_){
_start:
{
lean_object* v___x_3521_; 
v___x_3521_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_as_3517_, v_i_3518_, v_stop_3519_, v_b_3520_);
return v___x_3521_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___boxed(lean_object* v_00_u03b1_3522_, lean_object* v_as_3523_, lean_object* v_i_3524_, lean_object* v_stop_3525_, lean_object* v_b_3526_){
_start:
{
size_t v_i_boxed_3527_; size_t v_stop_boxed_3528_; lean_object* v_res_3529_; 
v_i_boxed_3527_ = lean_unbox_usize(v_i_3524_);
lean_dec(v_i_3524_);
v_stop_boxed_3528_ = lean_unbox_usize(v_stop_3525_);
lean_dec(v_stop_3525_);
v_res_3529_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1(v_00_u03b1_3522_, v_as_3523_, v_i_boxed_3527_, v_stop_boxed_3528_, v_b_3526_);
lean_dec_ref(v_as_3523_);
return v_res_3529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__0(lean_object* v_f_3530_, lean_object* v_j_3531_, lean_object* v_x_3532_){
_start:
{
lean_object* v___x_3533_; 
v___x_3533_ = lean_apply_2(v_f_3530_, v_j_3531_, v_x_3532_);
return v___x_3533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1(lean_object* v___f_3553_, lean_object* v_x1_3554_, lean_object* v_x2_3555_){
_start:
{
lean_object* v___x_3556_; size_t v_sz_3557_; size_t v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; 
v___x_3556_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__9));
v_sz_3557_ = lean_array_size(v_x2_3555_);
v___x_3558_ = ((size_t)0ULL);
v___x_3559_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3556_, v___f_3553_, v_sz_3557_, v___x_3558_, v_x2_3555_);
v___x_3560_ = l_Array_append___redArg(v_x1_3554_, v___x_3559_);
lean_dec(v___x_3559_);
return v___x_3560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2(lean_object* v_n_3561_, lean_object* v_mr_3562_, lean_object* v_f_3563_, lean_object* v_i_3564_, lean_object* v_x_3565_, lean_object* v_r_3566_){
_start:
{
lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v_j_3569_; lean_object* v_b_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; uint8_t v___x_3574_; 
v___x_3567_ = lean_unsigned_to_nat(1u);
v___x_3568_ = lean_nat_sub(v_n_3561_, v___x_3567_);
v_j_3569_ = lean_nat_sub(v___x_3568_, v_i_3564_);
lean_dec(v___x_3568_);
v_b_3570_ = lean_array_fget_borrowed(v_mr_3562_, v_j_3569_);
v___x_3571_ = lean_unsigned_to_nat(0u);
v___x_3572_ = lean_array_get_size(v_b_3570_);
v___x_3573_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__9));
v___x_3574_ = lean_nat_dec_lt(v___x_3571_, v___x_3572_);
if (v___x_3574_ == 0)
{
lean_dec(v_j_3569_);
lean_dec(v_f_3563_);
return v_r_3566_;
}
else
{
lean_object* v___f_3575_; lean_object* v___f_3576_; uint8_t v___x_3577_; 
v___f_3575_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3575_, 0, v_f_3563_);
lean_closure_set(v___f_3575_, 1, v_j_3569_);
v___f_3576_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1), 3, 1);
lean_closure_set(v___f_3576_, 0, v___f_3575_);
v___x_3577_ = lean_nat_dec_le(v___x_3572_, v___x_3572_);
if (v___x_3577_ == 0)
{
if (v___x_3574_ == 0)
{
lean_dec_ref(v___f_3576_);
return v_r_3566_;
}
else
{
size_t v___x_3578_; size_t v___x_3579_; lean_object* v___x_3580_; 
v___x_3578_ = ((size_t)0ULL);
v___x_3579_ = lean_usize_of_nat(v___x_3572_);
lean_inc(v_b_3570_);
v___x_3580_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3573_, v___f_3576_, v_b_3570_, v___x_3578_, v___x_3579_, v_r_3566_);
return v___x_3580_;
}
}
else
{
size_t v___x_3581_; size_t v___x_3582_; lean_object* v___x_3583_; 
v___x_3581_ = ((size_t)0ULL);
v___x_3582_ = lean_usize_of_nat(v___x_3572_);
lean_inc(v_b_3570_);
v___x_3583_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3573_, v___f_3576_, v_b_3570_, v___x_3581_, v___x_3582_, v_r_3566_);
return v___x_3583_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2___boxed(lean_object* v_n_3584_, lean_object* v_mr_3585_, lean_object* v_f_3586_, lean_object* v_i_3587_, lean_object* v_x_3588_, lean_object* v_r_3589_){
_start:
{
lean_object* v_res_3590_; 
v_res_3590_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2(v_n_3584_, v_mr_3585_, v_f_3586_, v_i_3587_, v_x_3588_, v_r_3589_);
lean_dec(v_i_3587_);
lean_dec_ref(v_mr_3585_);
lean_dec(v_n_3584_);
return v_res_3590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg(lean_object* v_mr_3591_, lean_object* v_a_3592_, lean_object* v_f_3593_){
_start:
{
lean_object* v_n_3594_; lean_object* v___f_3595_; lean_object* v___x_3596_; 
v_n_3594_ = lean_array_get_size(v_mr_3591_);
v___f_3595_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_3595_, 0, v_n_3594_);
lean_closure_set(v___f_3595_, 1, v_mr_3591_);
lean_closure_set(v___f_3595_, 2, v_f_3593_);
v___x_3596_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop(lean_box(0), v_n_3594_, v___f_3595_, v_n_3594_, lean_box(0), v_a_3592_);
return v___x_3596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux(lean_object* v_00_u03b1_3597_, lean_object* v_00_u03b2_3598_, lean_object* v_mr_3599_, lean_object* v_a_3600_, lean_object* v_f_3601_){
_start:
{
lean_object* v___x_3602_; 
v___x_3602_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg(v_mr_3599_, v_a_3600_, v_f_3601_);
return v___x_3602_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(size_t v_sz_3603_, size_t v_i_3604_, lean_object* v_bs_3605_){
_start:
{
uint8_t v___x_3606_; 
v___x_3606_ = lean_usize_dec_lt(v_i_3604_, v_sz_3603_);
if (v___x_3606_ == 0)
{
return v_bs_3605_;
}
else
{
lean_object* v_v_3607_; lean_object* v___x_3608_; lean_object* v_bs_x27_3609_; size_t v___x_3610_; size_t v___x_3611_; lean_object* v___x_3612_; 
v_v_3607_ = lean_array_uget(v_bs_3605_, v_i_3604_);
v___x_3608_ = lean_unsigned_to_nat(0u);
v_bs_x27_3609_ = lean_array_uset(v_bs_3605_, v_i_3604_, v___x_3608_);
v___x_3610_ = ((size_t)1ULL);
v___x_3611_ = lean_usize_add(v_i_3604_, v___x_3610_);
v___x_3612_ = lean_array_uset(v_bs_x27_3609_, v_i_3604_, v_v_3607_);
v_i_3604_ = v___x_3611_;
v_bs_3605_ = v___x_3612_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg___boxed(lean_object* v_sz_3614_, lean_object* v_i_3615_, lean_object* v_bs_3616_){
_start:
{
size_t v_sz_boxed_3617_; size_t v_i_boxed_3618_; lean_object* v_res_3619_; 
v_sz_boxed_3617_ = lean_unbox_usize(v_sz_3614_);
lean_dec(v_sz_3614_);
v_i_boxed_3618_ = lean_unbox_usize(v_i_3615_);
lean_dec(v_i_3615_);
v_res_3619_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(v_sz_boxed_3617_, v_i_boxed_3618_, v_bs_3616_);
return v_res_3619_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(lean_object* v_as_3620_, size_t v_i_3621_, size_t v_stop_3622_, lean_object* v_b_3623_){
_start:
{
uint8_t v___x_3624_; 
v___x_3624_ = lean_usize_dec_eq(v_i_3621_, v_stop_3622_);
if (v___x_3624_ == 0)
{
lean_object* v___x_3625_; size_t v_sz_3626_; size_t v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; size_t v___x_3630_; size_t v___x_3631_; 
v___x_3625_ = lean_array_uget_borrowed(v_as_3620_, v_i_3621_);
v_sz_3626_ = lean_array_size(v___x_3625_);
v___x_3627_ = ((size_t)0ULL);
lean_inc(v___x_3625_);
v___x_3628_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(v_sz_3626_, v___x_3627_, v___x_3625_);
v___x_3629_ = l_Array_append___redArg(v_b_3623_, v___x_3628_);
lean_dec_ref(v___x_3628_);
v___x_3630_ = ((size_t)1ULL);
v___x_3631_ = lean_usize_add(v_i_3621_, v___x_3630_);
v_i_3621_ = v___x_3631_;
v_b_3623_ = v___x_3629_;
goto _start;
}
else
{
return v_b_3623_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg___boxed(lean_object* v_as_3633_, lean_object* v_i_3634_, lean_object* v_stop_3635_, lean_object* v_b_3636_){
_start:
{
size_t v_i_boxed_3637_; size_t v_stop_boxed_3638_; lean_object* v_res_3639_; 
v_i_boxed_3637_ = lean_unbox_usize(v_i_3634_);
lean_dec(v_i_3634_);
v_stop_boxed_3638_ = lean_unbox_usize(v_stop_3635_);
lean_dec(v_stop_3635_);
v_res_3639_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(v_as_3633_, v_i_boxed_3637_, v_stop_boxed_3638_, v_b_3636_);
lean_dec_ref(v_as_3633_);
return v_res_3639_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(lean_object* v_n_3640_, lean_object* v_aa_3641_, lean_object* v_n_3642_, lean_object* v_j_3643_, lean_object* v_a_3644_){
_start:
{
lean_object* v_zero_3645_; uint8_t v_isZero_3646_; 
v_zero_3645_ = lean_unsigned_to_nat(0u);
v_isZero_3646_ = lean_nat_dec_eq(v_j_3643_, v_zero_3645_);
if (v_isZero_3646_ == 1)
{
lean_dec(v_j_3643_);
return v_a_3644_;
}
else
{
lean_object* v_one_3647_; lean_object* v_n_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v_j_3651_; lean_object* v_b_3652_; lean_object* v___x_3653_; uint8_t v___x_3654_; 
v_one_3647_ = lean_unsigned_to_nat(1u);
v_n_3648_ = lean_nat_sub(v_j_3643_, v_one_3647_);
v___x_3649_ = lean_nat_sub(v_n_3642_, v_j_3643_);
lean_dec(v_j_3643_);
v___x_3650_ = lean_nat_sub(v_n_3640_, v_one_3647_);
v_j_3651_ = lean_nat_sub(v___x_3650_, v___x_3649_);
lean_dec(v___x_3649_);
lean_dec(v___x_3650_);
v_b_3652_ = lean_array_fget_borrowed(v_aa_3641_, v_j_3651_);
lean_dec(v_j_3651_);
v___x_3653_ = lean_array_get_size(v_b_3652_);
v___x_3654_ = lean_nat_dec_lt(v_zero_3645_, v___x_3653_);
if (v___x_3654_ == 0)
{
v_j_3643_ = v_n_3648_;
goto _start;
}
else
{
uint8_t v___x_3656_; 
v___x_3656_ = lean_nat_dec_le(v___x_3653_, v___x_3653_);
if (v___x_3656_ == 0)
{
if (v___x_3654_ == 0)
{
v_j_3643_ = v_n_3648_;
goto _start;
}
else
{
size_t v___x_3658_; size_t v___x_3659_; lean_object* v___x_3660_; 
v___x_3658_ = ((size_t)0ULL);
v___x_3659_ = lean_usize_of_nat(v___x_3653_);
v___x_3660_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(v_b_3652_, v___x_3658_, v___x_3659_, v_a_3644_);
v_j_3643_ = v_n_3648_;
v_a_3644_ = v___x_3660_;
goto _start;
}
}
else
{
size_t v___x_3662_; size_t v___x_3663_; lean_object* v___x_3664_; 
v___x_3662_ = ((size_t)0ULL);
v___x_3663_ = lean_usize_of_nat(v___x_3653_);
v___x_3664_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(v_b_3652_, v___x_3662_, v___x_3663_, v_a_3644_);
v_j_3643_ = v_n_3648_;
v_a_3644_ = v___x_3664_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg___boxed(lean_object* v_n_3666_, lean_object* v_aa_3667_, lean_object* v_n_3668_, lean_object* v_j_3669_, lean_object* v_a_3670_){
_start:
{
lean_object* v_res_3671_; 
v_res_3671_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(v_n_3666_, v_aa_3667_, v_n_3668_, v_j_3669_, v_a_3670_);
lean_dec(v_n_3668_);
lean_dec_ref(v_aa_3667_);
lean_dec(v_n_3666_);
return v_res_3671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(lean_object* v_mr_3672_, lean_object* v_a_3673_){
_start:
{
lean_object* v_n_3674_; lean_object* v___x_3675_; 
v_n_3674_ = lean_array_get_size(v_mr_3672_);
v___x_3675_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(v_n_3674_, v_mr_3672_, v_n_3674_, v_n_3674_, v_a_3673_);
return v___x_3675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg___boxed(lean_object* v_mr_3676_, lean_object* v_a_3677_){
_start:
{
lean_object* v_res_3678_; 
v_res_3678_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3676_, v_a_3677_);
lean_dec_ref(v_mr_3676_);
return v_res_3678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___redArg(lean_object* v_mr_3679_, lean_object* v_a_3680_){
_start:
{
lean_object* v___x_3681_; 
v___x_3681_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3679_, v_a_3680_);
return v___x_3681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___redArg___boxed(lean_object* v_mr_3682_, lean_object* v_a_3683_){
_start:
{
lean_object* v_res_3684_; 
v_res_3684_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___redArg(v_mr_3682_, v_a_3683_);
lean_dec_ref(v_mr_3682_);
return v_res_3684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults(lean_object* v_00_u03b1_3685_, lean_object* v_mr_3686_, lean_object* v_a_3687_){
_start:
{
lean_object* v___x_3688_; 
v___x_3688_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3686_, v_a_3687_);
return v___x_3688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___boxed(lean_object* v_00_u03b1_3689_, lean_object* v_mr_3690_, lean_object* v_a_3691_){
_start:
{
lean_object* v_res_3692_; 
v_res_3692_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults(v_00_u03b1_3689_, v_mr_3690_, v_a_3691_);
lean_dec_ref(v_mr_3690_);
return v_res_3692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0(lean_object* v_00_u03b1_3693_, lean_object* v_mr_3694_, lean_object* v_a_3695_){
_start:
{
lean_object* v___x_3696_; 
v___x_3696_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3694_, v_a_3695_);
return v___x_3696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___boxed(lean_object* v_00_u03b1_3697_, lean_object* v_mr_3698_, lean_object* v_a_3699_){
_start:
{
lean_object* v_res_3700_; 
v_res_3700_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0(v_00_u03b1_3697_, v_mr_3698_, v_a_3699_);
lean_dec_ref(v_mr_3698_);
return v_res_3700_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0(lean_object* v_00_u03b1_3701_, size_t v_sz_3702_, size_t v_i_3703_, lean_object* v_bs_3704_){
_start:
{
lean_object* v___x_3705_; 
v___x_3705_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(v_sz_3702_, v_i_3703_, v_bs_3704_);
return v___x_3705_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3706_, lean_object* v_sz_3707_, lean_object* v_i_3708_, lean_object* v_bs_3709_){
_start:
{
size_t v_sz_boxed_3710_; size_t v_i_boxed_3711_; lean_object* v_res_3712_; 
v_sz_boxed_3710_ = lean_unbox_usize(v_sz_3707_);
lean_dec(v_sz_3707_);
v_i_boxed_3711_ = lean_unbox_usize(v_i_3708_);
lean_dec(v_i_3708_);
v_res_3712_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0(v_00_u03b1_3706_, v_sz_boxed_3710_, v_i_boxed_3711_, v_bs_3709_);
return v_res_3712_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1(lean_object* v_00_u03b1_3713_, lean_object* v_as_3714_, size_t v_i_3715_, size_t v_stop_3716_, lean_object* v_b_3717_){
_start:
{
lean_object* v___x_3718_; 
v___x_3718_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(v_as_3714_, v_i_3715_, v_stop_3716_, v_b_3717_);
return v___x_3718_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3719_, lean_object* v_as_3720_, lean_object* v_i_3721_, lean_object* v_stop_3722_, lean_object* v_b_3723_){
_start:
{
size_t v_i_boxed_3724_; size_t v_stop_boxed_3725_; lean_object* v_res_3726_; 
v_i_boxed_3724_ = lean_unbox_usize(v_i_3721_);
lean_dec(v_i_3721_);
v_stop_boxed_3725_ = lean_unbox_usize(v_stop_3722_);
lean_dec(v_stop_3722_);
v_res_3726_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1(v_00_u03b1_3719_, v_as_3720_, v_i_boxed_3724_, v_stop_boxed_3725_, v_b_3723_);
lean_dec_ref(v_as_3720_);
return v_res_3726_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2(lean_object* v_00_u03b1_3727_, lean_object* v_n_3728_, lean_object* v_aa_3729_, lean_object* v_n_3730_, lean_object* v_j_3731_, lean_object* v_a_3732_, lean_object* v_a_3733_){
_start:
{
lean_object* v___x_3734_; 
v___x_3734_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(v_n_3728_, v_aa_3729_, v_n_3730_, v_j_3731_, v_a_3733_);
return v___x_3734_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___boxed(lean_object* v_00_u03b1_3735_, lean_object* v_n_3736_, lean_object* v_aa_3737_, lean_object* v_n_3738_, lean_object* v_j_3739_, lean_object* v_a_3740_, lean_object* v_a_3741_){
_start:
{
lean_object* v_res_3742_; 
v_res_3742_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2(v_00_u03b1_3735_, v_n_3736_, v_aa_3737_, v_n_3738_, v_j_3739_, v_a_3740_, v_a_3741_);
lean_dec(v_n_3738_);
lean_dec_ref(v_aa_3737_);
lean_dec(v_n_3736_);
return v_res_3742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0(lean_object* v_snd_3750_, lean_object* v___x_3751_, lean_object* v_score_3752_, lean_object* v___x_3753_, lean_object* v_k_3754_, lean_object* v_args_3755_, lean_object* v_cases_3756_){
_start:
{
lean_object* v___x_3757_; 
v___x_3757_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_snd_3750_, v_k_3754_);
if (lean_obj_tag(v___x_3757_) == 0)
{
lean_dec_ref(v___x_3751_);
return v_cases_3756_;
}
else
{
lean_object* v_val_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; 
v_val_3758_ = lean_ctor_get(v___x_3757_, 0);
lean_inc(v_val_3758_);
lean_dec_ref_known(v___x_3757_, 1);
v___x_3759_ = l_Array_append___redArg(v___x_3751_, v_args_3755_);
v___x_3760_ = lean_nat_add(v_score_3752_, v___x_3753_);
v___x_3761_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3761_, 0, v___x_3759_);
lean_ctor_set(v___x_3761_, 1, v___x_3760_);
lean_ctor_set(v___x_3761_, 2, v_val_3758_);
v___x_3762_ = lean_array_push(v_cases_3756_, v___x_3761_);
return v___x_3762_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0___boxed(lean_object* v_snd_3763_, lean_object* v___x_3764_, lean_object* v_score_3765_, lean_object* v___x_3766_, lean_object* v_k_3767_, lean_object* v_args_3768_, lean_object* v_cases_3769_){
_start:
{
lean_object* v_res_3770_; 
v_res_3770_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0(v_snd_3763_, v___x_3764_, v_score_3765_, v___x_3766_, v_k_3767_, v_args_3768_, v_cases_3769_);
lean_dec_ref(v_args_3768_);
lean_dec(v_k_3767_);
lean_dec(v___x_3766_);
lean_dec(v_score_3765_);
lean_dec_ref(v_snd_3763_);
return v_res_3770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(lean_object* v_cases_3771_, lean_object* v_result_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_, lean_object* v_a_3777_){
_start:
{
lean_object* v___x_3779_; lean_object* v___x_3780_; uint8_t v___x_3781_; 
v___x_3779_ = lean_array_get_size(v_cases_3771_);
v___x_3780_ = lean_unsigned_to_nat(0u);
v___x_3781_ = lean_nat_dec_eq(v___x_3779_, v___x_3780_);
if (v___x_3781_ == 0)
{
lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v_ca_3785_; lean_object* v_todo_3786_; lean_object* v_score_3787_; lean_object* v_c_3788_; lean_object* v___x_3790_; uint8_t v_isShared_3791_; uint8_t v_isSharedCheck_3854_; 
v___x_3782_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedPartialMatch_default));
v___x_3783_ = lean_unsigned_to_nat(1u);
v___x_3784_ = lean_nat_sub(v___x_3779_, v___x_3783_);
v_ca_3785_ = lean_array_get(v___x_3782_, v_cases_3771_, v___x_3784_);
lean_dec(v___x_3784_);
v_todo_3786_ = lean_ctor_get(v_ca_3785_, 0);
v_score_3787_ = lean_ctor_get(v_ca_3785_, 1);
v_c_3788_ = lean_ctor_get(v_ca_3785_, 2);
v_isSharedCheck_3854_ = !lean_is_exclusive(v_ca_3785_);
if (v_isSharedCheck_3854_ == 0)
{
v___x_3790_ = v_ca_3785_;
v_isShared_3791_ = v_isSharedCheck_3854_;
goto v_resetjp_3789_;
}
else
{
lean_inc(v_c_3788_);
lean_inc(v_score_3787_);
lean_inc(v_todo_3786_);
lean_dec(v_ca_3785_);
v___x_3790_ = lean_box(0);
v_isShared_3791_ = v_isSharedCheck_3854_;
goto v_resetjp_3789_;
}
v_resetjp_3789_:
{
lean_object* v___x_3792_; 
v___x_3792_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_c_3788_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_);
lean_dec(v_c_3788_);
if (lean_obj_tag(v___x_3792_) == 0)
{
lean_object* v_a_3793_; lean_object* v___y_3795_; uint8_t v___y_3796_; lean_object* v___y_3797_; lean_object* v___y_3798_; lean_object* v_snd_3821_; lean_object* v_fst_3822_; lean_object* v_fst_3823_; lean_object* v_snd_3824_; lean_object* v_cases_3825_; lean_object* v___x_3826_; uint8_t v___y_3828_; uint8_t v___x_3840_; 
v_a_3793_ = lean_ctor_get(v___x_3792_, 0);
lean_inc(v_a_3793_);
lean_dec_ref_known(v___x_3792_, 1);
v_snd_3821_ = lean_ctor_get(v_a_3793_, 1);
lean_inc(v_snd_3821_);
v_fst_3822_ = lean_ctor_get(v_a_3793_, 0);
lean_inc(v_fst_3822_);
lean_dec(v_a_3793_);
v_fst_3823_ = lean_ctor_get(v_snd_3821_, 0);
lean_inc(v_fst_3823_);
v_snd_3824_ = lean_ctor_get(v_snd_3821_, 1);
lean_inc(v_snd_3824_);
lean_dec(v_snd_3821_);
v_cases_3825_ = lean_array_pop(v_cases_3771_);
v___x_3826_ = lean_array_get_size(v_todo_3786_);
v___x_3840_ = lean_nat_dec_eq(v___x_3826_, v___x_3780_);
if (v___x_3840_ == 0)
{
uint8_t v___x_3841_; 
lean_dec(v_fst_3822_);
v___x_3841_ = lean_nat_dec_eq(v_fst_3823_, v___x_3780_);
if (v___x_3841_ == 0)
{
v___y_3828_ = v___x_3841_;
goto v___jp_3827_;
}
else
{
lean_object* v_size_3842_; uint8_t v___x_3843_; 
v_size_3842_ = lean_ctor_get(v_snd_3824_, 0);
v___x_3843_ = lean_nat_dec_eq(v_size_3842_, v___x_3780_);
v___y_3828_ = v___x_3843_;
goto v___jp_3827_;
}
}
else
{
lean_object* v___x_3844_; 
lean_dec(v_snd_3824_);
lean_dec(v_fst_3823_);
lean_del_object(v___x_3790_);
lean_dec_ref(v_todo_3786_);
v___x_3844_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v_result_3772_, v_score_3787_, v_fst_3822_);
lean_dec(v_score_3787_);
v_cases_3771_ = v_cases_3825_;
v_result_3772_ = v___x_3844_;
goto _start;
}
v___jp_3794_:
{
uint8_t v___x_3799_; lean_object* v___x_3800_; 
v___x_3799_ = 1;
v___x_3800_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v___y_3795_, v___x_3799_, v___y_3796_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_);
if (lean_obj_tag(v___x_3800_) == 0)
{
lean_object* v_a_3801_; lean_object* v_fst_3802_; 
v_a_3801_ = lean_ctor_get(v___x_3800_, 0);
lean_inc(v_a_3801_);
lean_dec_ref_known(v___x_3800_, 1);
v_fst_3802_ = lean_ctor_get(v_a_3801_, 0);
lean_inc(v_fst_3802_);
switch(lean_obj_tag(v_fst_3802_))
{
case 3:
{
lean_dec(v_a_3801_);
lean_dec_ref(v___y_3797_);
v_cases_3771_ = v___y_3798_;
goto _start;
}
case 5:
{
lean_object* v_snd_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; 
v_snd_3804_ = lean_ctor_get(v_a_3801_, 1);
lean_inc(v_snd_3804_);
lean_dec(v_a_3801_);
v___x_3805_ = lean_box(4);
v___x_3806_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
lean_inc_ref(v___y_3797_);
v___x_3807_ = lean_apply_3(v___y_3797_, v___x_3805_, v___x_3806_, v___y_3798_);
v___x_3808_ = lean_apply_3(v___y_3797_, v_fst_3802_, v_snd_3804_, v___x_3807_);
v_cases_3771_ = v___x_3808_;
goto _start;
}
default: 
{
lean_object* v_snd_3810_; lean_object* v___x_3811_; 
v_snd_3810_ = lean_ctor_get(v_a_3801_, 1);
lean_inc(v_snd_3810_);
lean_dec(v_a_3801_);
v___x_3811_ = lean_apply_3(v___y_3797_, v_fst_3802_, v_snd_3810_, v___y_3798_);
v_cases_3771_ = v___x_3811_;
goto _start;
}
}
}
else
{
lean_object* v_a_3813_; lean_object* v___x_3815_; uint8_t v_isShared_3816_; uint8_t v_isSharedCheck_3820_; 
lean_dec_ref(v___y_3798_);
lean_dec_ref(v___y_3797_);
lean_dec_ref(v_result_3772_);
v_a_3813_ = lean_ctor_get(v___x_3800_, 0);
v_isSharedCheck_3820_ = !lean_is_exclusive(v___x_3800_);
if (v_isSharedCheck_3820_ == 0)
{
v___x_3815_ = v___x_3800_;
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
else
{
lean_inc(v_a_3813_);
lean_dec(v___x_3800_);
v___x_3815_ = lean_box(0);
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
v_resetjp_3814_:
{
lean_object* v___x_3818_; 
if (v_isShared_3816_ == 0)
{
v___x_3818_ = v___x_3815_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v_a_3813_);
v___x_3818_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3817_;
}
v_reusejp_3817_:
{
return v___x_3818_;
}
}
}
}
v___jp_3827_:
{
if (v___y_3828_ == 0)
{
lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___f_3833_; uint8_t v___x_3834_; 
v___x_3829_ = l_Lean_instInhabitedExpr;
v___x_3830_ = lean_nat_sub(v___x_3826_, v___x_3783_);
v___x_3831_ = lean_array_get(v___x_3829_, v_todo_3786_, v___x_3830_);
lean_dec(v___x_3830_);
v___x_3832_ = lean_array_pop(v_todo_3786_);
lean_inc(v_score_3787_);
lean_inc_ref(v___x_3832_);
v___f_3833_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0___boxed), 7, 4);
lean_closure_set(v___f_3833_, 0, v_snd_3824_);
lean_closure_set(v___f_3833_, 1, v___x_3832_);
lean_closure_set(v___f_3833_, 2, v_score_3787_);
lean_closure_set(v___f_3833_, 3, v___x_3783_);
v___x_3834_ = lean_nat_dec_eq(v_fst_3823_, v___x_3780_);
if (v___x_3834_ == 0)
{
lean_object* v___x_3836_; 
if (v_isShared_3791_ == 0)
{
lean_ctor_set(v___x_3790_, 2, v_fst_3823_);
lean_ctor_set(v___x_3790_, 0, v___x_3832_);
v___x_3836_ = v___x_3790_;
goto v_reusejp_3835_;
}
else
{
lean_object* v_reuseFailAlloc_3838_; 
v_reuseFailAlloc_3838_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3838_, 0, v___x_3832_);
lean_ctor_set(v_reuseFailAlloc_3838_, 1, v_score_3787_);
lean_ctor_set(v_reuseFailAlloc_3838_, 2, v_fst_3823_);
v___x_3836_ = v_reuseFailAlloc_3838_;
goto v_reusejp_3835_;
}
v_reusejp_3835_:
{
lean_object* v___x_3837_; 
v___x_3837_ = lean_array_push(v_cases_3825_, v___x_3836_);
v___y_3795_ = v___x_3831_;
v___y_3796_ = v___y_3828_;
v___y_3797_ = v___f_3833_;
v___y_3798_ = v___x_3837_;
goto v___jp_3794_;
}
}
else
{
lean_dec_ref(v___x_3832_);
lean_dec(v_fst_3823_);
lean_del_object(v___x_3790_);
lean_dec(v_score_3787_);
v___y_3795_ = v___x_3831_;
v___y_3796_ = v___y_3828_;
v___y_3797_ = v___f_3833_;
v___y_3798_ = v_cases_3825_;
goto v___jp_3794_;
}
}
else
{
lean_dec(v_snd_3824_);
lean_dec(v_fst_3823_);
lean_del_object(v___x_3790_);
lean_dec(v_score_3787_);
lean_dec_ref(v_todo_3786_);
v_cases_3771_ = v_cases_3825_;
goto _start;
}
}
}
else
{
lean_object* v_a_3846_; lean_object* v___x_3848_; uint8_t v_isShared_3849_; uint8_t v_isSharedCheck_3853_; 
lean_del_object(v___x_3790_);
lean_dec(v_score_3787_);
lean_dec_ref(v_todo_3786_);
lean_dec_ref(v_result_3772_);
lean_dec_ref(v_cases_3771_);
v_a_3846_ = lean_ctor_get(v___x_3792_, 0);
v_isSharedCheck_3853_ = !lean_is_exclusive(v___x_3792_);
if (v_isSharedCheck_3853_ == 0)
{
v___x_3848_ = v___x_3792_;
v_isShared_3849_ = v_isSharedCheck_3853_;
goto v_resetjp_3847_;
}
else
{
lean_inc(v_a_3846_);
lean_dec(v___x_3792_);
v___x_3848_ = lean_box(0);
v_isShared_3849_ = v_isSharedCheck_3853_;
goto v_resetjp_3847_;
}
v_resetjp_3847_:
{
lean_object* v___x_3851_; 
if (v_isShared_3849_ == 0)
{
v___x_3851_ = v___x_3848_;
goto v_reusejp_3850_;
}
else
{
lean_object* v_reuseFailAlloc_3852_; 
v_reuseFailAlloc_3852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3852_, 0, v_a_3846_);
v___x_3851_ = v_reuseFailAlloc_3852_;
goto v_reusejp_3850_;
}
v_reusejp_3850_:
{
return v___x_3851_;
}
}
}
}
}
else
{
lean_object* v___x_3855_; 
lean_dec_ref(v_cases_3771_);
v___x_3855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3855_, 0, v_result_3772_);
return v___x_3855_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___boxed(lean_object* v_cases_3856_, lean_object* v_result_3857_, lean_object* v_a_3858_, lean_object* v_a_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_){
_start:
{
lean_object* v_res_3864_; 
v_res_3864_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v_cases_3856_, v_result_3857_, v_a_3858_, v_a_3859_, v_a_3860_, v_a_3861_, v_a_3862_);
lean_dec(v_a_3862_);
lean_dec_ref(v_a_3861_);
lean_dec(v_a_3860_);
lean_dec_ref(v_a_3859_);
lean_dec(v_a_3858_);
return v_res_3864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop(lean_object* v_00_u03b1_3865_, lean_object* v_cases_3866_, lean_object* v_result_3867_, lean_object* v_a_3868_, lean_object* v_a_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_){
_start:
{
lean_object* v___x_3874_; 
v___x_3874_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v_cases_3866_, v_result_3867_, v_a_3868_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_);
return v___x_3874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___boxed(lean_object* v_00_u03b1_3875_, lean_object* v_cases_3876_, lean_object* v_result_3877_, lean_object* v_a_3878_, lean_object* v_a_3879_, lean_object* v_a_3880_, lean_object* v_a_3881_, lean_object* v_a_3882_, lean_object* v_a_3883_){
_start:
{
lean_object* v_res_3884_; 
v_res_3884_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop(v_00_u03b1_3875_, v_cases_3876_, v_result_3877_, v_a_3878_, v_a_3879_, v_a_3880_, v_a_3881_, v_a_3882_);
lean_dec(v_a_3882_);
lean_dec_ref(v_a_3881_);
lean_dec(v_a_3880_);
lean_dec_ref(v_a_3879_);
lean_dec(v_a_3878_);
return v_res_3884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult___redArg(lean_object* v_root_3887_, lean_object* v_a_3888_, lean_object* v_a_3889_, lean_object* v_a_3890_, lean_object* v_a_3891_, lean_object* v_a_3892_){
_start:
{
lean_object* v___x_3894_; lean_object* v___x_3895_; 
v___x_3894_ = lean_box(3);
v___x_3895_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_root_3887_, v___x_3894_);
if (lean_obj_tag(v___x_3895_) == 0)
{
lean_object* v___x_3896_; lean_object* v___x_3897_; 
v___x_3896_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_getStarResult___redArg___closed__0));
v___x_3897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3897_, 0, v___x_3896_);
return v___x_3897_;
}
else
{
lean_object* v_val_3898_; lean_object* v___x_3899_; 
v_val_3898_ = lean_ctor_get(v___x_3895_, 0);
lean_inc(v_val_3898_);
lean_dec_ref_known(v___x_3895_, 1);
v___x_3899_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_val_3898_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_, v_a_3892_);
lean_dec(v_val_3898_);
if (lean_obj_tag(v___x_3899_) == 0)
{
lean_object* v_a_3900_; lean_object* v___x_3902_; uint8_t v_isShared_3903_; uint8_t v_isSharedCheck_3911_; 
v_a_3900_ = lean_ctor_get(v___x_3899_, 0);
v_isSharedCheck_3911_ = !lean_is_exclusive(v___x_3899_);
if (v_isSharedCheck_3911_ == 0)
{
v___x_3902_ = v___x_3899_;
v_isShared_3903_ = v_isSharedCheck_3911_;
goto v_resetjp_3901_;
}
else
{
lean_inc(v_a_3900_);
lean_dec(v___x_3899_);
v___x_3902_ = lean_box(0);
v_isShared_3903_ = v_isSharedCheck_3911_;
goto v_resetjp_3901_;
}
v_resetjp_3901_:
{
lean_object* v_fst_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3909_; 
v_fst_3904_ = lean_ctor_get(v_a_3900_, 0);
lean_inc(v_fst_3904_);
lean_dec(v_a_3900_);
v___x_3905_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_getStarResult___redArg___closed__0));
v___x_3906_ = lean_unsigned_to_nat(1u);
v___x_3907_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v___x_3905_, v___x_3906_, v_fst_3904_);
if (v_isShared_3903_ == 0)
{
lean_ctor_set(v___x_3902_, 0, v___x_3907_);
v___x_3909_ = v___x_3902_;
goto v_reusejp_3908_;
}
else
{
lean_object* v_reuseFailAlloc_3910_; 
v_reuseFailAlloc_3910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3910_, 0, v___x_3907_);
v___x_3909_ = v_reuseFailAlloc_3910_;
goto v_reusejp_3908_;
}
v_reusejp_3908_:
{
return v___x_3909_;
}
}
}
else
{
lean_object* v_a_3912_; lean_object* v___x_3914_; uint8_t v_isShared_3915_; uint8_t v_isSharedCheck_3919_; 
v_a_3912_ = lean_ctor_get(v___x_3899_, 0);
v_isSharedCheck_3919_ = !lean_is_exclusive(v___x_3899_);
if (v_isSharedCheck_3919_ == 0)
{
v___x_3914_ = v___x_3899_;
v_isShared_3915_ = v_isSharedCheck_3919_;
goto v_resetjp_3913_;
}
else
{
lean_inc(v_a_3912_);
lean_dec(v___x_3899_);
v___x_3914_ = lean_box(0);
v_isShared_3915_ = v_isSharedCheck_3919_;
goto v_resetjp_3913_;
}
v_resetjp_3913_:
{
lean_object* v___x_3917_; 
if (v_isShared_3915_ == 0)
{
v___x_3917_ = v___x_3914_;
goto v_reusejp_3916_;
}
else
{
lean_object* v_reuseFailAlloc_3918_; 
v_reuseFailAlloc_3918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3918_, 0, v_a_3912_);
v___x_3917_ = v_reuseFailAlloc_3918_;
goto v_reusejp_3916_;
}
v_reusejp_3916_:
{
return v___x_3917_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult___redArg___boxed(lean_object* v_root_3920_, lean_object* v_a_3921_, lean_object* v_a_3922_, lean_object* v_a_3923_, lean_object* v_a_3924_, lean_object* v_a_3925_, lean_object* v_a_3926_){
_start:
{
lean_object* v_res_3927_; 
v_res_3927_ = l_Lean_Meta_LazyDiscrTree_getStarResult___redArg(v_root_3920_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_);
lean_dec(v_a_3925_);
lean_dec_ref(v_a_3924_);
lean_dec(v_a_3923_);
lean_dec_ref(v_a_3922_);
lean_dec(v_a_3921_);
lean_dec_ref(v_root_3920_);
return v_res_3927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult(lean_object* v_00_u03b1_3928_, lean_object* v_root_3929_, lean_object* v_a_3930_, lean_object* v_a_3931_, lean_object* v_a_3932_, lean_object* v_a_3933_, lean_object* v_a_3934_){
_start:
{
lean_object* v___x_3936_; 
v___x_3936_ = l_Lean_Meta_LazyDiscrTree_getStarResult___redArg(v_root_3929_, v_a_3930_, v_a_3931_, v_a_3932_, v_a_3933_, v_a_3934_);
return v___x_3936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult___boxed(lean_object* v_00_u03b1_3937_, lean_object* v_root_3938_, lean_object* v_a_3939_, lean_object* v_a_3940_, lean_object* v_a_3941_, lean_object* v_a_3942_, lean_object* v_a_3943_, lean_object* v_a_3944_){
_start:
{
lean_object* v_res_3945_; 
v_res_3945_ = l_Lean_Meta_LazyDiscrTree_getStarResult(v_00_u03b1_3937_, v_root_3938_, v_a_3939_, v_a_3940_, v_a_3941_, v_a_3942_, v_a_3943_);
lean_dec(v_a_3943_);
lean_dec_ref(v_a_3942_);
lean_dec(v_a_3941_);
lean_dec_ref(v_a_3940_);
lean_dec(v_a_3939_);
lean_dec_ref(v_root_3938_);
return v_res_3945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushRootCase(lean_object* v_r_3946_, lean_object* v_k_3947_, lean_object* v_args_3948_, lean_object* v_cases_3949_){
_start:
{
lean_object* v___x_3950_; 
v___x_3950_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_r_3946_, v_k_3947_);
if (lean_obj_tag(v___x_3950_) == 0)
{
lean_dec_ref(v_args_3948_);
return v_cases_3949_;
}
else
{
lean_object* v_val_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; 
v_val_3951_ = lean_ctor_get(v___x_3950_, 0);
lean_inc(v_val_3951_);
lean_dec_ref_known(v___x_3950_, 1);
v___x_3952_ = lean_unsigned_to_nat(1u);
v___x_3953_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3953_, 0, v_args_3948_);
lean_ctor_set(v___x_3953_, 1, v___x_3952_);
lean_ctor_set(v___x_3953_, 2, v_val_3951_);
v___x_3954_ = lean_array_push(v_cases_3949_, v___x_3953_);
return v___x_3954_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushRootCase___boxed(lean_object* v_r_3955_, lean_object* v_k_3956_, lean_object* v_args_3957_, lean_object* v_cases_3958_){
_start:
{
lean_object* v_res_3959_; 
v_res_3959_ = l_Lean_Meta_LazyDiscrTree_pushRootCase(v_r_3955_, v_k_3956_, v_args_3957_, v_cases_3958_);
lean_dec(v_k_3956_);
lean_dec_ref(v_r_3955_);
return v_res_3959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg(lean_object* v_root_3962_, lean_object* v_e_3963_, lean_object* v_a_3964_, lean_object* v_a_3965_, lean_object* v_a_3966_, lean_object* v_a_3967_, lean_object* v_a_3968_){
_start:
{
lean_object* v___x_3970_; 
v___x_3970_ = l_Lean_Meta_LazyDiscrTree_getStarResult___redArg(v_root_3962_, v_a_3964_, v_a_3965_, v_a_3966_, v_a_3967_, v_a_3968_);
if (lean_obj_tag(v___x_3970_) == 0)
{
lean_object* v_a_3971_; uint8_t v___x_3972_; lean_object* v___x_3973_; 
v_a_3971_ = lean_ctor_get(v___x_3970_, 0);
lean_inc(v_a_3971_);
lean_dec_ref_known(v___x_3970_, 1);
v___x_3972_ = 1;
v___x_3973_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_3963_, v___x_3972_, v___x_3972_, v_a_3965_, v_a_3966_, v_a_3967_, v_a_3968_);
if (lean_obj_tag(v___x_3973_) == 0)
{
lean_object* v_a_3974_; lean_object* v_fst_3975_; 
v_a_3974_ = lean_ctor_get(v___x_3973_, 0);
lean_inc(v_a_3974_);
lean_dec_ref_known(v___x_3973_, 1);
v_fst_3975_ = lean_ctor_get(v_a_3974_, 0);
lean_inc(v_fst_3975_);
switch(lean_obj_tag(v_fst_3975_))
{
case 3:
{
lean_object* v___x_3976_; lean_object* v___x_3977_; 
lean_dec(v_a_3974_);
v___x_3976_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg___closed__0));
v___x_3977_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v___x_3976_, v_a_3971_, v_a_3964_, v_a_3965_, v_a_3966_, v_a_3967_, v_a_3968_);
return v___x_3977_;
}
case 5:
{
lean_object* v_snd_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; 
v_snd_3978_ = lean_ctor_get(v_a_3974_, 1);
lean_inc(v_snd_3978_);
lean_dec(v_a_3974_);
v___x_3979_ = lean_box(4);
v___x_3980_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
v___x_3981_ = l_Lean_Meta_LazyDiscrTree_pushRootCase(v_root_3962_, v___x_3979_, v___x_3980_, v___x_3980_);
v___x_3982_ = l_Lean_Meta_LazyDiscrTree_pushRootCase(v_root_3962_, v_fst_3975_, v_snd_3978_, v___x_3981_);
v___x_3983_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v___x_3982_, v_a_3971_, v_a_3964_, v_a_3965_, v_a_3966_, v_a_3967_, v_a_3968_);
return v___x_3983_;
}
default: 
{
lean_object* v_snd_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; 
v_snd_3984_ = lean_ctor_get(v_a_3974_, 1);
lean_inc(v_snd_3984_);
lean_dec(v_a_3974_);
v___x_3985_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg___closed__0));
v___x_3986_ = l_Lean_Meta_LazyDiscrTree_pushRootCase(v_root_3962_, v_fst_3975_, v_snd_3984_, v___x_3985_);
lean_dec(v_fst_3975_);
v___x_3987_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v___x_3986_, v_a_3971_, v_a_3964_, v_a_3965_, v_a_3966_, v_a_3967_, v_a_3968_);
return v___x_3987_;
}
}
}
else
{
lean_object* v_a_3988_; lean_object* v___x_3990_; uint8_t v_isShared_3991_; uint8_t v_isSharedCheck_3995_; 
lean_dec(v_a_3971_);
v_a_3988_ = lean_ctor_get(v___x_3973_, 0);
v_isSharedCheck_3995_ = !lean_is_exclusive(v___x_3973_);
if (v_isSharedCheck_3995_ == 0)
{
v___x_3990_ = v___x_3973_;
v_isShared_3991_ = v_isSharedCheck_3995_;
goto v_resetjp_3989_;
}
else
{
lean_inc(v_a_3988_);
lean_dec(v___x_3973_);
v___x_3990_ = lean_box(0);
v_isShared_3991_ = v_isSharedCheck_3995_;
goto v_resetjp_3989_;
}
v_resetjp_3989_:
{
lean_object* v___x_3993_; 
if (v_isShared_3991_ == 0)
{
v___x_3993_ = v___x_3990_;
goto v_reusejp_3992_;
}
else
{
lean_object* v_reuseFailAlloc_3994_; 
v_reuseFailAlloc_3994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3994_, 0, v_a_3988_);
v___x_3993_ = v_reuseFailAlloc_3994_;
goto v_reusejp_3992_;
}
v_reusejp_3992_:
{
return v___x_3993_;
}
}
}
}
else
{
lean_dec_ref(v_e_3963_);
return v___x_3970_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg___boxed(lean_object* v_root_3996_, lean_object* v_e_3997_, lean_object* v_a_3998_, lean_object* v_a_3999_, lean_object* v_a_4000_, lean_object* v_a_4001_, lean_object* v_a_4002_, lean_object* v_a_4003_){
_start:
{
lean_object* v_res_4004_; 
v_res_4004_ = l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg(v_root_3996_, v_e_3997_, v_a_3998_, v_a_3999_, v_a_4000_, v_a_4001_, v_a_4002_);
lean_dec(v_a_4002_);
lean_dec_ref(v_a_4001_);
lean_dec(v_a_4000_);
lean_dec_ref(v_a_3999_);
lean_dec(v_a_3998_);
lean_dec_ref(v_root_3996_);
return v_res_4004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore(lean_object* v_00_u03b1_4005_, lean_object* v_root_4006_, lean_object* v_e_4007_, lean_object* v_a_4008_, lean_object* v_a_4009_, lean_object* v_a_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_){
_start:
{
lean_object* v___x_4014_; 
v___x_4014_ = l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg(v_root_4006_, v_e_4007_, v_a_4008_, v_a_4009_, v_a_4010_, v_a_4011_, v_a_4012_);
return v___x_4014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore___boxed(lean_object* v_00_u03b1_4015_, lean_object* v_root_4016_, lean_object* v_e_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_, lean_object* v_a_4023_){
_start:
{
lean_object* v_res_4024_; 
v_res_4024_ = l_Lean_Meta_LazyDiscrTree_getMatchCore(v_00_u03b1_4015_, v_root_4016_, v_e_4017_, v_a_4018_, v_a_4019_, v_a_4020_, v_a_4021_, v_a_4022_);
lean_dec(v_a_4022_);
lean_dec_ref(v_a_4021_);
lean_dec(v_a_4020_);
lean_dec_ref(v_a_4019_);
lean_dec(v_a_4018_);
lean_dec_ref(v_root_4016_);
return v_res_4024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch___redArg(lean_object* v_d_4025_, lean_object* v_e_4026_, lean_object* v_a_4027_, lean_object* v_a_4028_, lean_object* v_a_4029_, lean_object* v_a_4030_){
_start:
{
lean_object* v_roots_4032_; lean_object* v_keyedConfig_4033_; uint8_t v_trackZetaDelta_4034_; lean_object* v_zetaDeltaSet_4035_; lean_object* v_lctx_4036_; lean_object* v_localInstances_4037_; lean_object* v_defEqCtx_x3f_4038_; lean_object* v_synthPendingDepth_4039_; lean_object* v_customCanUnfoldPredicate_x3f_4040_; uint8_t v_univApprox_4041_; uint8_t v_inTypeClassResolution_4042_; uint8_t v_cacheInferType_4043_; lean_object* v___x_4044_; uint8_t v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; 
v_roots_4032_ = lean_ctor_get(v_d_4025_, 1);
v_keyedConfig_4033_ = lean_ctor_get(v_a_4027_, 0);
v_trackZetaDelta_4034_ = lean_ctor_get_uint8(v_a_4027_, sizeof(void*)*7);
v_zetaDeltaSet_4035_ = lean_ctor_get(v_a_4027_, 1);
v_lctx_4036_ = lean_ctor_get(v_a_4027_, 2);
v_localInstances_4037_ = lean_ctor_get(v_a_4027_, 3);
v_defEqCtx_x3f_4038_ = lean_ctor_get(v_a_4027_, 4);
v_synthPendingDepth_4039_ = lean_ctor_get(v_a_4027_, 5);
v_customCanUnfoldPredicate_x3f_4040_ = lean_ctor_get(v_a_4027_, 6);
v_univApprox_4041_ = lean_ctor_get_uint8(v_a_4027_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4042_ = lean_ctor_get_uint8(v_a_4027_, sizeof(void*)*7 + 2);
v_cacheInferType_4043_ = lean_ctor_get_uint8(v_a_4027_, sizeof(void*)*7 + 3);
lean_inc_ref(v_roots_4032_);
v___x_4044_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getMatchCore___boxed), 9, 3);
lean_closure_set(v___x_4044_, 0, lean_box(0));
lean_closure_set(v___x_4044_, 1, v_roots_4032_);
lean_closure_set(v___x_4044_, 2, v_e_4026_);
v___x_4045_ = 2;
lean_inc_ref(v_keyedConfig_4033_);
v___x_4046_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4045_, v_keyedConfig_4033_);
lean_inc(v_customCanUnfoldPredicate_x3f_4040_);
lean_inc(v_synthPendingDepth_4039_);
lean_inc(v_defEqCtx_x3f_4038_);
lean_inc_ref(v_localInstances_4037_);
lean_inc_ref(v_lctx_4036_);
lean_inc(v_zetaDeltaSet_4035_);
v___x_4047_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4047_, 0, v___x_4046_);
lean_ctor_set(v___x_4047_, 1, v_zetaDeltaSet_4035_);
lean_ctor_set(v___x_4047_, 2, v_lctx_4036_);
lean_ctor_set(v___x_4047_, 3, v_localInstances_4037_);
lean_ctor_set(v___x_4047_, 4, v_defEqCtx_x3f_4038_);
lean_ctor_set(v___x_4047_, 5, v_synthPendingDepth_4039_);
lean_ctor_set(v___x_4047_, 6, v_customCanUnfoldPredicate_x3f_4040_);
lean_ctor_set_uint8(v___x_4047_, sizeof(void*)*7, v_trackZetaDelta_4034_);
lean_ctor_set_uint8(v___x_4047_, sizeof(void*)*7 + 1, v_univApprox_4041_);
lean_ctor_set_uint8(v___x_4047_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4042_);
lean_ctor_set_uint8(v___x_4047_, sizeof(void*)*7 + 3, v_cacheInferType_4043_);
v___x_4048_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_d_4025_, v___x_4044_, v___x_4047_, v_a_4028_, v_a_4029_, v_a_4030_);
lean_dec_ref_known(v___x_4047_, 7);
return v___x_4048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch___redArg___boxed(lean_object* v_d_4049_, lean_object* v_e_4050_, lean_object* v_a_4051_, lean_object* v_a_4052_, lean_object* v_a_4053_, lean_object* v_a_4054_, lean_object* v_a_4055_){
_start:
{
lean_object* v_res_4056_; 
v_res_4056_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v_d_4049_, v_e_4050_, v_a_4051_, v_a_4052_, v_a_4053_, v_a_4054_);
lean_dec(v_a_4054_);
lean_dec_ref(v_a_4053_);
lean_dec(v_a_4052_);
lean_dec_ref(v_a_4051_);
return v_res_4056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch(lean_object* v_00_u03b1_4057_, lean_object* v_d_4058_, lean_object* v_e_4059_, lean_object* v_a_4060_, lean_object* v_a_4061_, lean_object* v_a_4062_, lean_object* v_a_4063_){
_start:
{
lean_object* v___x_4065_; 
v___x_4065_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v_d_4058_, v_e_4059_, v_a_4060_, v_a_4061_, v_a_4062_, v_a_4063_);
return v___x_4065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch___boxed(lean_object* v_00_u03b1_4066_, lean_object* v_d_4067_, lean_object* v_e_4068_, lean_object* v_a_4069_, lean_object* v_a_4070_, lean_object* v_a_4071_, lean_object* v_a_4072_, lean_object* v_a_4073_){
_start:
{
lean_object* v_res_4074_; 
v_res_4074_ = l_Lean_Meta_LazyDiscrTree_getMatch(v_00_u03b1_4066_, v_d_4067_, v_e_4068_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_);
lean_dec(v_a_4072_);
lean_dec_ref(v_a_4071_);
lean_dec(v_a_4070_);
lean_dec_ref(v_a_4069_);
return v_res_4074_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1(void){
_start:
{
lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; 
v___x_4077_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0));
v___x_4078_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_4079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4079_, 0, v___x_4078_);
lean_ctor_set(v___x_4079_, 1, v___x_4077_);
return v___x_4079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default(lean_object* v_00_u03b1_4080_){
_start:
{
lean_object* v___x_4081_; 
v___x_4081_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1);
return v___x_4081_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___closed__0(void){
_start:
{
lean_object* v___x_4082_; 
v___x_4082_ = l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default(lean_box(0));
return v___x_4082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree(lean_object* v_a_4083_){
_start:
{
lean_object* v___x_4084_; 
v___x_4084_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___closed__0);
return v___x_4084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(lean_object* v_d_4085_, lean_object* v_k_4086_, lean_object* v_f_4087_){
_start:
{
lean_object* v_roots_4088_; lean_object* v_tries_4089_; lean_object* v___x_4090_; 
v_roots_4088_ = lean_ctor_get(v_d_4085_, 0);
v_tries_4089_ = lean_ctor_get(v_d_4085_, 1);
v___x_4090_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_roots_4088_, v_k_4086_);
if (lean_obj_tag(v___x_4090_) == 0)
{
lean_object* v___x_4092_; uint8_t v_isShared_4093_; uint8_t v_isSharedCheck_4102_; 
lean_inc_ref(v_tries_4089_);
lean_inc_ref(v_roots_4088_);
v_isSharedCheck_4102_ = !lean_is_exclusive(v_d_4085_);
if (v_isSharedCheck_4102_ == 0)
{
lean_object* v_unused_4103_; lean_object* v_unused_4104_; 
v_unused_4103_ = lean_ctor_get(v_d_4085_, 1);
lean_dec(v_unused_4103_);
v_unused_4104_ = lean_ctor_get(v_d_4085_, 0);
lean_dec(v_unused_4104_);
v___x_4092_ = v_d_4085_;
v_isShared_4093_ = v_isSharedCheck_4102_;
goto v_resetjp_4091_;
}
else
{
lean_dec(v_d_4085_);
v___x_4092_ = lean_box(0);
v_isShared_4093_ = v_isSharedCheck_4102_;
goto v_resetjp_4091_;
}
v_resetjp_4091_:
{
lean_object* v___x_4094_; lean_object* v_roots_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4100_; 
v___x_4094_ = lean_array_get_size(v_tries_4089_);
v_roots_4095_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_roots_4088_, v_k_4086_, v___x_4094_);
v___x_4096_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__3));
v___x_4097_ = lean_apply_1(v_f_4087_, v___x_4096_);
v___x_4098_ = lean_array_push(v_tries_4089_, v___x_4097_);
if (v_isShared_4093_ == 0)
{
lean_ctor_set(v___x_4092_, 1, v___x_4098_);
lean_ctor_set(v___x_4092_, 0, v_roots_4095_);
v___x_4100_ = v___x_4092_;
goto v_reusejp_4099_;
}
else
{
lean_object* v_reuseFailAlloc_4101_; 
v_reuseFailAlloc_4101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4101_, 0, v_roots_4095_);
lean_ctor_set(v_reuseFailAlloc_4101_, 1, v___x_4098_);
v___x_4100_ = v_reuseFailAlloc_4101_;
goto v_reusejp_4099_;
}
v_reusejp_4099_:
{
return v___x_4100_;
}
}
}
else
{
lean_object* v_val_4105_; lean_object* v___x_4106_; uint8_t v___x_4107_; 
lean_dec(v_k_4086_);
v_val_4105_ = lean_ctor_get(v___x_4090_, 0);
lean_inc(v_val_4105_);
lean_dec_ref_known(v___x_4090_, 1);
v___x_4106_ = lean_array_get_size(v_tries_4089_);
v___x_4107_ = lean_nat_dec_lt(v_val_4105_, v___x_4106_);
if (v___x_4107_ == 0)
{
lean_dec(v_val_4105_);
lean_dec_ref(v_f_4087_);
return v_d_4085_;
}
else
{
lean_object* v___x_4109_; uint8_t v_isShared_4110_; uint8_t v_isSharedCheck_4119_; 
lean_inc_ref(v_tries_4089_);
lean_inc_ref(v_roots_4088_);
v_isSharedCheck_4119_ = !lean_is_exclusive(v_d_4085_);
if (v_isSharedCheck_4119_ == 0)
{
lean_object* v_unused_4120_; lean_object* v_unused_4121_; 
v_unused_4120_ = lean_ctor_get(v_d_4085_, 1);
lean_dec(v_unused_4120_);
v_unused_4121_ = lean_ctor_get(v_d_4085_, 0);
lean_dec(v_unused_4121_);
v___x_4109_ = v_d_4085_;
v_isShared_4110_ = v_isSharedCheck_4119_;
goto v_resetjp_4108_;
}
else
{
lean_dec(v_d_4085_);
v___x_4109_ = lean_box(0);
v_isShared_4110_ = v_isSharedCheck_4119_;
goto v_resetjp_4108_;
}
v_resetjp_4108_:
{
lean_object* v_v_4111_; lean_object* v___x_4112_; lean_object* v_xs_x27_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4117_; 
v_v_4111_ = lean_array_fget(v_tries_4089_, v_val_4105_);
v___x_4112_ = lean_box(0);
v_xs_x27_4113_ = lean_array_fset(v_tries_4089_, v_val_4105_, v___x_4112_);
v___x_4114_ = lean_apply_1(v_f_4087_, v_v_4111_);
v___x_4115_ = lean_array_fset(v_xs_x27_4113_, v_val_4105_, v___x_4114_);
lean_dec(v_val_4105_);
if (v_isShared_4110_ == 0)
{
lean_ctor_set(v___x_4109_, 1, v___x_4115_);
v___x_4117_ = v___x_4109_;
goto v_reusejp_4116_;
}
else
{
lean_object* v_reuseFailAlloc_4118_; 
v_reuseFailAlloc_4118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4118_, 0, v_roots_4088_);
lean_ctor_set(v_reuseFailAlloc_4118_, 1, v___x_4115_);
v___x_4117_ = v_reuseFailAlloc_4118_;
goto v_reusejp_4116_;
}
v_reusejp_4116_:
{
return v___x_4117_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt(lean_object* v_00_u03b1_4122_, lean_object* v_d_4123_, lean_object* v_k_4124_, lean_object* v_f_4125_){
_start:
{
lean_object* v___x_4126_; 
v___x_4126_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(v_d_4123_, v_k_4124_, v_f_4125_);
return v___x_4126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg___lam__0(lean_object* v_e_4127_, lean_object* v_x_4128_){
_start:
{
lean_object* v___x_4129_; 
v___x_4129_ = lean_array_push(v_x_4128_, v_e_4127_);
return v___x_4129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg(lean_object* v_d_4130_, lean_object* v_k_4131_, lean_object* v_e_4132_){
_start:
{
lean_object* v___f_4133_; lean_object* v___x_4134_; 
v___f_4133_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4133_, 0, v_e_4132_);
v___x_4134_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(v_d_4130_, v_k_4131_, v___f_4133_);
return v___x_4134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push(lean_object* v_00_u03b1_4135_, lean_object* v_d_4136_, lean_object* v_k_4137_, lean_object* v_e_4138_){
_start:
{
lean_object* v___x_4139_; 
v___x_4139_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg(v_d_4136_, v_k_4137_, v_e_4138_);
return v___x_4139_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(size_t v_sz_4140_, size_t v_i_4141_, lean_object* v_bs_4142_){
_start:
{
uint8_t v___x_4143_; 
v___x_4143_ = lean_usize_dec_lt(v_i_4141_, v_sz_4140_);
if (v___x_4143_ == 0)
{
return v_bs_4142_;
}
else
{
lean_object* v_v_4144_; lean_object* v___x_4145_; lean_object* v_bs_x27_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; size_t v___x_4150_; size_t v___x_4151_; lean_object* v___x_4152_; 
v_v_4144_ = lean_array_uget(v_bs_4142_, v_i_4141_);
v___x_4145_ = lean_unsigned_to_nat(0u);
v_bs_x27_4146_ = lean_array_uset(v_bs_4142_, v_i_4141_, v___x_4145_);
v___x_4147_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0));
v___x_4148_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_4149_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4149_, 0, v___x_4147_);
lean_ctor_set(v___x_4149_, 1, v___x_4145_);
lean_ctor_set(v___x_4149_, 2, v___x_4148_);
lean_ctor_set(v___x_4149_, 3, v_v_4144_);
v___x_4150_ = ((size_t)1ULL);
v___x_4151_ = lean_usize_add(v_i_4141_, v___x_4150_);
v___x_4152_ = lean_array_uset(v_bs_x27_4146_, v_i_4141_, v___x_4149_);
v_i_4141_ = v___x_4151_;
v_bs_4142_ = v___x_4152_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg___boxed(lean_object* v_sz_4154_, lean_object* v_i_4155_, lean_object* v_bs_4156_){
_start:
{
size_t v_sz_boxed_4157_; size_t v_i_boxed_4158_; lean_object* v_res_4159_; 
v_sz_boxed_4157_ = lean_unbox_usize(v_sz_4154_);
lean_dec(v_sz_4154_);
v_i_boxed_4158_ = lean_unbox_usize(v_i_4155_);
lean_dec(v_i_4155_);
v_res_4159_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(v_sz_boxed_4157_, v_i_boxed_4158_, v_bs_4156_);
return v_res_4159_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__1(lean_object* v_x_4160_, lean_object* v_x_4161_){
_start:
{
if (lean_obj_tag(v_x_4161_) == 0)
{
return v_x_4160_;
}
else
{
lean_object* v_key_4162_; lean_object* v_value_4163_; lean_object* v_tail_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; 
v_key_4162_ = lean_ctor_get(v_x_4161_, 0);
lean_inc(v_key_4162_);
v_value_4163_ = lean_ctor_get(v_x_4161_, 1);
lean_inc(v_value_4163_);
v_tail_4164_ = lean_ctor_get(v_x_4161_, 2);
lean_inc(v_tail_4164_);
lean_dec_ref_known(v_x_4161_, 3);
v___x_4165_ = lean_unsigned_to_nat(1u);
v___x_4166_ = lean_nat_add(v_value_4163_, v___x_4165_);
lean_dec(v_value_4163_);
v___x_4167_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_x_4160_, v_key_4162_, v___x_4166_);
v_x_4160_ = v___x_4167_;
v_x_4161_ = v_tail_4164_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(lean_object* v_as_4169_, size_t v_i_4170_, size_t v_stop_4171_, lean_object* v_b_4172_){
_start:
{
uint8_t v___x_4173_; 
v___x_4173_ = lean_usize_dec_eq(v_i_4170_, v_stop_4171_);
if (v___x_4173_ == 0)
{
lean_object* v___x_4174_; lean_object* v___x_4175_; size_t v___x_4176_; size_t v___x_4177_; 
v___x_4174_ = lean_array_uget_borrowed(v_as_4169_, v_i_4170_);
lean_inc(v___x_4174_);
v___x_4175_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__1(v_b_4172_, v___x_4174_);
v___x_4176_ = ((size_t)1ULL);
v___x_4177_ = lean_usize_add(v_i_4170_, v___x_4176_);
v_i_4170_ = v___x_4177_;
v_b_4172_ = v___x_4175_;
goto _start;
}
else
{
return v_b_4172_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2___boxed(lean_object* v_as_4179_, lean_object* v_i_4180_, lean_object* v_stop_4181_, lean_object* v_b_4182_){
_start:
{
size_t v_i_boxed_4183_; size_t v_stop_boxed_4184_; lean_object* v_res_4185_; 
v_i_boxed_4183_ = lean_unbox_usize(v_i_4180_);
lean_dec(v_i_4180_);
v_stop_boxed_4184_ = lean_unbox_usize(v_stop_4181_);
lean_dec(v_stop_4181_);
v_res_4185_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(v_as_4179_, v_i_boxed_4183_, v_stop_boxed_4184_, v_b_4182_);
lean_dec_ref(v_as_4179_);
return v_res_4185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(lean_object* v_d_4186_){
_start:
{
lean_object* v_roots_4187_; lean_object* v_tries_4188_; lean_object* v___x_4190_; uint8_t v_isShared_4191_; uint8_t v_isSharedCheck_4215_; 
v_roots_4187_ = lean_ctor_get(v_d_4186_, 0);
v_tries_4188_ = lean_ctor_get(v_d_4186_, 1);
v_isSharedCheck_4215_ = !lean_is_exclusive(v_d_4186_);
if (v_isSharedCheck_4215_ == 0)
{
v___x_4190_ = v_d_4186_;
v_isShared_4191_ = v_isSharedCheck_4215_;
goto v_resetjp_4189_;
}
else
{
lean_inc(v_tries_4188_);
lean_inc(v_roots_4187_);
lean_dec(v_d_4186_);
v___x_4190_ = lean_box(0);
v_isShared_4191_ = v_isSharedCheck_4215_;
goto v_resetjp_4189_;
}
v_resetjp_4189_:
{
lean_object* v___y_4193_; lean_object* v_buckets_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; uint8_t v___x_4207_; 
v_buckets_4204_ = lean_ctor_get(v_roots_4187_, 1);
v___x_4205_ = lean_unsigned_to_nat(0u);
v___x_4206_ = lean_array_get_size(v_buckets_4204_);
v___x_4207_ = lean_nat_dec_lt(v___x_4205_, v___x_4206_);
if (v___x_4207_ == 0)
{
v___y_4193_ = v_roots_4187_;
goto v___jp_4192_;
}
else
{
uint8_t v___x_4208_; 
v___x_4208_ = lean_nat_dec_le(v___x_4206_, v___x_4206_);
if (v___x_4208_ == 0)
{
if (v___x_4207_ == 0)
{
v___y_4193_ = v_roots_4187_;
goto v___jp_4192_;
}
else
{
size_t v___x_4209_; size_t v___x_4210_; lean_object* v___x_4211_; 
lean_inc_ref(v_buckets_4204_);
v___x_4209_ = ((size_t)0ULL);
v___x_4210_ = lean_usize_of_nat(v___x_4206_);
v___x_4211_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(v_buckets_4204_, v___x_4209_, v___x_4210_, v_roots_4187_);
lean_dec_ref(v_buckets_4204_);
v___y_4193_ = v___x_4211_;
goto v___jp_4192_;
}
}
else
{
size_t v___x_4212_; size_t v___x_4213_; lean_object* v___x_4214_; 
lean_inc_ref(v_buckets_4204_);
v___x_4212_ = ((size_t)0ULL);
v___x_4213_ = lean_usize_of_nat(v___x_4206_);
v___x_4214_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(v_buckets_4204_, v___x_4212_, v___x_4213_, v_roots_4187_);
lean_dec_ref(v_buckets_4204_);
v___y_4193_ = v___x_4214_;
goto v___jp_4192_;
}
}
v___jp_4192_:
{
lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; size_t v_sz_4197_; size_t v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4202_; 
v___x_4194_ = lean_unsigned_to_nat(1u);
v___x_4195_ = lean_mk_empty_array_with_capacity(v___x_4194_);
lean_dec_ref(v___x_4195_);
v___x_4196_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0);
v_sz_4197_ = lean_array_size(v_tries_4188_);
v___x_4198_ = ((size_t)0ULL);
v___x_4199_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(v_sz_4197_, v___x_4198_, v_tries_4188_);
v___x_4200_ = l_Array_append___redArg(v___x_4196_, v___x_4199_);
lean_dec_ref(v___x_4199_);
if (v_isShared_4191_ == 0)
{
lean_ctor_set(v___x_4190_, 1, v___y_4193_);
lean_ctor_set(v___x_4190_, 0, v___x_4200_);
v___x_4202_ = v___x_4190_;
goto v_reusejp_4201_;
}
else
{
lean_object* v_reuseFailAlloc_4203_; 
v_reuseFailAlloc_4203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4203_, 0, v___x_4200_);
lean_ctor_set(v_reuseFailAlloc_4203_, 1, v___y_4193_);
v___x_4202_ = v_reuseFailAlloc_4203_;
goto v_reusejp_4201_;
}
v_reusejp_4201_:
{
return v___x_4202_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy(lean_object* v_00_u03b1_4216_, lean_object* v_d_4217_){
_start:
{
lean_object* v___x_4218_; 
v___x_4218_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_d_4217_);
return v___x_4218_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0(lean_object* v_00_u03b1_4219_, size_t v_sz_4220_, size_t v_i_4221_, lean_object* v_bs_4222_){
_start:
{
lean_object* v___x_4223_; 
v___x_4223_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(v_sz_4220_, v_i_4221_, v_bs_4222_);
return v___x_4223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___boxed(lean_object* v_00_u03b1_4224_, lean_object* v_sz_4225_, lean_object* v_i_4226_, lean_object* v_bs_4227_){
_start:
{
size_t v_sz_boxed_4228_; size_t v_i_boxed_4229_; lean_object* v_res_4230_; 
v_sz_boxed_4228_ = lean_unbox_usize(v_sz_4225_);
lean_dec(v_sz_4225_);
v_i_boxed_4229_ = lean_unbox_usize(v_i_4226_);
lean_dec(v_i_4226_);
v_res_4230_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0(v_00_u03b1_4224_, v_sz_boxed_4228_, v_i_boxed_4229_, v_bs_4227_);
return v_res_4230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___lam__0(lean_object* v_y_4231_, lean_object* v_x_4232_){
_start:
{
lean_object* v___x_4233_; 
v___x_4233_ = l_Array_append___redArg(v_x_4232_, v_y_4231_);
return v___x_4233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___lam__0___boxed(lean_object* v_y_4234_, lean_object* v_x_4235_){
_start:
{
lean_object* v_res_4236_; 
v_res_4236_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___lam__0(v_y_4234_, v_x_4235_);
lean_dec_ref(v_y_4234_);
return v_res_4236_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4237_; 
v___x_4237_ = l_Array_instInhabited(lean_box(0));
return v___x_4237_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(lean_object* v_tries_4238_, lean_object* v_snd_4239_, lean_object* v_x_4240_, lean_object* v_x_4241_){
_start:
{
if (lean_obj_tag(v_x_4241_) == 0)
{
lean_dec_ref(v_snd_4239_);
return v_x_4240_;
}
else
{
lean_object* v_key_4242_; lean_object* v_value_4243_; lean_object* v_tail_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; 
v_key_4242_ = lean_ctor_get(v_x_4241_, 0);
lean_inc(v_key_4242_);
v_value_4243_ = lean_ctor_get(v_x_4241_, 1);
lean_inc(v_value_4243_);
v_tail_4244_ = lean_ctor_get(v_x_4241_, 2);
lean_inc(v_tail_4244_);
lean_dec_ref_known(v_x_4241_, 3);
v___x_4245_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0);
v___x_4246_ = lean_array_get_borrowed(v___x_4245_, v_tries_4238_, v_value_4243_);
lean_dec(v_value_4243_);
lean_inc_ref(v_snd_4239_);
lean_inc(v___x_4246_);
v___x_4247_ = lean_apply_1(v_snd_4239_, v___x_4246_);
v___x_4248_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(v_x_4240_, v_key_4242_, v___x_4247_);
v_x_4240_ = v___x_4248_;
v_x_4241_ = v_tail_4244_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___boxed(lean_object* v_tries_4250_, lean_object* v_snd_4251_, lean_object* v_x_4252_, lean_object* v_x_4253_){
_start:
{
lean_object* v_res_4254_; 
v_res_4254_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(v_tries_4250_, v_snd_4251_, v_x_4252_, v_x_4253_);
lean_dec_ref(v_tries_4250_);
return v_res_4254_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(lean_object* v_tries_4255_, lean_object* v_snd_4256_, lean_object* v_as_4257_, size_t v_i_4258_, size_t v_stop_4259_, lean_object* v_b_4260_){
_start:
{
uint8_t v___x_4261_; 
v___x_4261_ = lean_usize_dec_eq(v_i_4258_, v_stop_4259_);
if (v___x_4261_ == 0)
{
lean_object* v___x_4262_; lean_object* v___x_4263_; size_t v___x_4264_; size_t v___x_4265_; 
v___x_4262_ = lean_array_uget_borrowed(v_as_4257_, v_i_4258_);
lean_inc(v___x_4262_);
lean_inc_ref(v_snd_4256_);
v___x_4263_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(v_tries_4255_, v_snd_4256_, v_b_4260_, v___x_4262_);
v___x_4264_ = ((size_t)1ULL);
v___x_4265_ = lean_usize_add(v_i_4258_, v___x_4264_);
v_i_4258_ = v___x_4265_;
v_b_4260_ = v___x_4263_;
goto _start;
}
else
{
lean_dec_ref(v_snd_4256_);
return v_b_4260_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg___boxed(lean_object* v_tries_4267_, lean_object* v_snd_4268_, lean_object* v_as_4269_, lean_object* v_i_4270_, lean_object* v_stop_4271_, lean_object* v_b_4272_){
_start:
{
size_t v_i_boxed_4273_; size_t v_stop_boxed_4274_; lean_object* v_res_4275_; 
v_i_boxed_4273_ = lean_unbox_usize(v_i_4270_);
lean_dec(v_i_4270_);
v_stop_boxed_4274_ = lean_unbox_usize(v_stop_4271_);
lean_dec(v_stop_4271_);
v_res_4275_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(v_tries_4267_, v_snd_4268_, v_as_4269_, v_i_boxed_4273_, v_stop_boxed_4274_, v_b_4272_);
lean_dec_ref(v_as_4269_);
lean_dec_ref(v_tries_4267_);
return v_res_4275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg(lean_object* v_x_4278_, lean_object* v_y_4279_){
_start:
{
lean_object* v_fst_4281_; lean_object* v_buckets_4282_; lean_object* v_tries_4283_; lean_object* v_snd_4284_; lean_object* v_roots_4295_; lean_object* v_roots_4296_; lean_object* v_tries_4297_; lean_object* v_size_4298_; lean_object* v_buckets_4299_; lean_object* v_tries_4300_; lean_object* v_size_4301_; lean_object* v_buckets_4302_; uint8_t v___x_4303_; 
v_roots_4295_ = lean_ctor_get(v_y_4279_, 0);
v_roots_4296_ = lean_ctor_get(v_x_4278_, 0);
v_tries_4297_ = lean_ctor_get(v_y_4279_, 1);
v_size_4298_ = lean_ctor_get(v_roots_4295_, 0);
v_buckets_4299_ = lean_ctor_get(v_roots_4295_, 1);
v_tries_4300_ = lean_ctor_get(v_x_4278_, 1);
v_size_4301_ = lean_ctor_get(v_roots_4296_, 0);
v_buckets_4302_ = lean_ctor_get(v_roots_4296_, 1);
v___x_4303_ = lean_nat_dec_le(v_size_4298_, v_size_4301_);
if (v___x_4303_ == 0)
{
lean_object* v___f_4304_; 
lean_inc_ref(v_buckets_4302_);
lean_inc_ref(v_tries_4300_);
lean_dec_ref(v_x_4278_);
v___f_4304_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___closed__0));
v_fst_4281_ = v_y_4279_;
v_buckets_4282_ = v_buckets_4302_;
v_tries_4283_ = v_tries_4300_;
v_snd_4284_ = v___f_4304_;
goto v___jp_4280_;
}
else
{
lean_object* v___f_4305_; 
lean_inc_ref(v_buckets_4299_);
lean_inc_ref(v_tries_4297_);
lean_dec_ref(v_y_4279_);
v___f_4305_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___closed__1));
v_fst_4281_ = v_x_4278_;
v_buckets_4282_ = v_buckets_4299_;
v_tries_4283_ = v_tries_4297_;
v_snd_4284_ = v___f_4305_;
goto v___jp_4280_;
}
v___jp_4280_:
{
lean_object* v___x_4285_; lean_object* v___x_4286_; uint8_t v___x_4287_; 
v___x_4285_ = lean_unsigned_to_nat(0u);
v___x_4286_ = lean_array_get_size(v_buckets_4282_);
v___x_4287_ = lean_nat_dec_lt(v___x_4285_, v___x_4286_);
if (v___x_4287_ == 0)
{
lean_dec_ref(v_tries_4283_);
lean_dec_ref(v_buckets_4282_);
return v_fst_4281_;
}
else
{
uint8_t v___x_4288_; 
v___x_4288_ = lean_nat_dec_le(v___x_4286_, v___x_4286_);
if (v___x_4288_ == 0)
{
if (v___x_4287_ == 0)
{
lean_dec_ref(v_tries_4283_);
lean_dec_ref(v_buckets_4282_);
return v_fst_4281_;
}
else
{
size_t v___x_4289_; size_t v___x_4290_; lean_object* v___x_4291_; 
v___x_4289_ = ((size_t)0ULL);
v___x_4290_ = lean_usize_of_nat(v___x_4286_);
lean_inc_ref(v_snd_4284_);
v___x_4291_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(v_tries_4283_, v_snd_4284_, v_buckets_4282_, v___x_4289_, v___x_4290_, v_fst_4281_);
lean_dec_ref(v_buckets_4282_);
lean_dec_ref(v_tries_4283_);
return v___x_4291_;
}
}
else
{
size_t v___x_4292_; size_t v___x_4293_; lean_object* v___x_4294_; 
v___x_4292_ = ((size_t)0ULL);
v___x_4293_ = lean_usize_of_nat(v___x_4286_);
lean_inc_ref(v_snd_4284_);
v___x_4294_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(v_tries_4283_, v_snd_4284_, v_buckets_4282_, v___x_4292_, v___x_4293_, v_fst_4281_);
lean_dec_ref(v_buckets_4282_);
lean_dec_ref(v_tries_4283_);
return v___x_4294_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append(lean_object* v_00_u03b1_4306_, lean_object* v_x_4307_, lean_object* v_y_4308_){
_start:
{
lean_object* v___x_4309_; 
v___x_4309_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg(v_x_4307_, v_y_4308_);
return v___x_4309_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0(lean_object* v_00_u03b1_4310_, lean_object* v_tries_4311_, lean_object* v_snd_4312_, lean_object* v_x_4313_, lean_object* v_x_4314_){
_start:
{
lean_object* v___x_4315_; 
v___x_4315_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(v_tries_4311_, v_snd_4312_, v_x_4313_, v_x_4314_);
return v___x_4315_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___boxed(lean_object* v_00_u03b1_4316_, lean_object* v_tries_4317_, lean_object* v_snd_4318_, lean_object* v_x_4319_, lean_object* v_x_4320_){
_start:
{
lean_object* v_res_4321_; 
v_res_4321_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0(v_00_u03b1_4316_, v_tries_4317_, v_snd_4318_, v_x_4319_, v_x_4320_);
lean_dec_ref(v_tries_4317_);
return v_res_4321_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1(lean_object* v_00_u03b1_4322_, lean_object* v_tries_4323_, lean_object* v_snd_4324_, lean_object* v_as_4325_, size_t v_i_4326_, size_t v_stop_4327_, lean_object* v_b_4328_){
_start:
{
lean_object* v___x_4329_; 
v___x_4329_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(v_tries_4323_, v_snd_4324_, v_as_4325_, v_i_4326_, v_stop_4327_, v_b_4328_);
return v___x_4329_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___boxed(lean_object* v_00_u03b1_4330_, lean_object* v_tries_4331_, lean_object* v_snd_4332_, lean_object* v_as_4333_, lean_object* v_i_4334_, lean_object* v_stop_4335_, lean_object* v_b_4336_){
_start:
{
size_t v_i_boxed_4337_; size_t v_stop_boxed_4338_; lean_object* v_res_4339_; 
v_i_boxed_4337_ = lean_unbox_usize(v_i_4334_);
lean_dec(v_i_4334_);
v_stop_boxed_4338_ = lean_unbox_usize(v_stop_4335_);
lean_dec(v_stop_4335_);
v_res_4339_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1(v_00_u03b1_4330_, v_tries_4331_, v_snd_4332_, v_as_4333_, v_i_boxed_4337_, v_stop_boxed_4338_, v_b_4336_);
lean_dec_ref(v_as_4333_);
lean_dec_ref(v_tries_4331_);
return v_res_4339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend(lean_object* v_00_u03b1_4341_){
_start:
{
lean_object* v___x_4342_; 
v___x_4342_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend___closed__0));
return v___x_4342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(lean_object* v_expr_4343_, lean_object* v_value_4344_, lean_object* v_a_4345_, lean_object* v_a_4346_, lean_object* v_a_4347_, lean_object* v_a_4348_){
_start:
{
lean_object* v___x_4350_; 
v___x_4350_ = l_Lean_Meta_LazyDiscrTree_rootKey(v_expr_4343_, v_a_4345_, v_a_4346_, v_a_4347_, v_a_4348_);
if (lean_obj_tag(v___x_4350_) == 0)
{
lean_object* v_a_4351_; lean_object* v___x_4353_; uint8_t v_isShared_4354_; uint8_t v_isSharedCheck_4372_; 
v_a_4351_ = lean_ctor_get(v___x_4350_, 0);
v_isSharedCheck_4372_ = !lean_is_exclusive(v___x_4350_);
if (v_isSharedCheck_4372_ == 0)
{
v___x_4353_ = v___x_4350_;
v_isShared_4354_ = v_isSharedCheck_4372_;
goto v_resetjp_4352_;
}
else
{
lean_inc(v_a_4351_);
lean_dec(v___x_4350_);
v___x_4353_ = lean_box(0);
v_isShared_4354_ = v_isSharedCheck_4372_;
goto v_resetjp_4352_;
}
v_resetjp_4352_:
{
lean_object* v_fst_4355_; lean_object* v_snd_4356_; lean_object* v___x_4358_; uint8_t v_isShared_4359_; uint8_t v_isSharedCheck_4371_; 
v_fst_4355_ = lean_ctor_get(v_a_4351_, 0);
v_snd_4356_ = lean_ctor_get(v_a_4351_, 1);
v_isSharedCheck_4371_ = !lean_is_exclusive(v_a_4351_);
if (v_isSharedCheck_4371_ == 0)
{
v___x_4358_ = v_a_4351_;
v_isShared_4359_ = v_isSharedCheck_4371_;
goto v_resetjp_4357_;
}
else
{
lean_inc(v_snd_4356_);
lean_inc(v_fst_4355_);
lean_dec(v_a_4351_);
v___x_4358_ = lean_box(0);
v_isShared_4359_ = v_isSharedCheck_4371_;
goto v_resetjp_4357_;
}
v_resetjp_4357_:
{
lean_object* v_lctx_4360_; lean_object* v_localInstances_4361_; lean_object* v___x_4363_; 
v_lctx_4360_ = lean_ctor_get(v_a_4345_, 2);
v_localInstances_4361_ = lean_ctor_get(v_a_4345_, 3);
lean_inc_ref(v_localInstances_4361_);
lean_inc_ref(v_lctx_4360_);
if (v_isShared_4359_ == 0)
{
lean_ctor_set(v___x_4358_, 1, v_localInstances_4361_);
lean_ctor_set(v___x_4358_, 0, v_lctx_4360_);
v___x_4363_ = v___x_4358_;
goto v_reusejp_4362_;
}
else
{
lean_object* v_reuseFailAlloc_4370_; 
v_reuseFailAlloc_4370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4370_, 0, v_lctx_4360_);
lean_ctor_set(v_reuseFailAlloc_4370_, 1, v_localInstances_4361_);
v___x_4363_ = v_reuseFailAlloc_4370_;
goto v_reusejp_4362_;
}
v_reusejp_4362_:
{
lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4368_; 
v___x_4364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4364_, 0, v___x_4363_);
lean_ctor_set(v___x_4364_, 1, v_value_4344_);
v___x_4365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4365_, 0, v_snd_4356_);
lean_ctor_set(v___x_4365_, 1, v___x_4364_);
v___x_4366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4366_, 0, v_fst_4355_);
lean_ctor_set(v___x_4366_, 1, v___x_4365_);
if (v_isShared_4354_ == 0)
{
lean_ctor_set(v___x_4353_, 0, v___x_4366_);
v___x_4368_ = v___x_4353_;
goto v_reusejp_4367_;
}
else
{
lean_object* v_reuseFailAlloc_4369_; 
v_reuseFailAlloc_4369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4369_, 0, v___x_4366_);
v___x_4368_ = v_reuseFailAlloc_4369_;
goto v_reusejp_4367_;
}
v_reusejp_4367_:
{
return v___x_4368_;
}
}
}
}
}
else
{
lean_object* v_a_4373_; lean_object* v___x_4375_; uint8_t v_isShared_4376_; uint8_t v_isSharedCheck_4380_; 
lean_dec(v_value_4344_);
v_a_4373_ = lean_ctor_get(v___x_4350_, 0);
v_isSharedCheck_4380_ = !lean_is_exclusive(v___x_4350_);
if (v_isSharedCheck_4380_ == 0)
{
v___x_4375_ = v___x_4350_;
v_isShared_4376_ = v_isSharedCheck_4380_;
goto v_resetjp_4374_;
}
else
{
lean_inc(v_a_4373_);
lean_dec(v___x_4350_);
v___x_4375_ = lean_box(0);
v_isShared_4376_ = v_isSharedCheck_4380_;
goto v_resetjp_4374_;
}
v_resetjp_4374_:
{
lean_object* v___x_4378_; 
if (v_isShared_4376_ == 0)
{
v___x_4378_ = v___x_4375_;
goto v_reusejp_4377_;
}
else
{
lean_object* v_reuseFailAlloc_4379_; 
v_reuseFailAlloc_4379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4379_, 0, v_a_4373_);
v___x_4378_ = v_reuseFailAlloc_4379_;
goto v_reusejp_4377_;
}
v_reusejp_4377_:
{
return v___x_4378_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg___boxed(lean_object* v_expr_4381_, lean_object* v_value_4382_, lean_object* v_a_4383_, lean_object* v_a_4384_, lean_object* v_a_4385_, lean_object* v_a_4386_, lean_object* v_a_4387_){
_start:
{
lean_object* v_res_4388_; 
v_res_4388_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(v_expr_4381_, v_value_4382_, v_a_4383_, v_a_4384_, v_a_4385_, v_a_4386_);
lean_dec(v_a_4386_);
lean_dec_ref(v_a_4385_);
lean_dec(v_a_4384_);
lean_dec_ref(v_a_4383_);
return v_res_4388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr(lean_object* v_00_u03b1_4389_, lean_object* v_expr_4390_, lean_object* v_value_4391_, lean_object* v_a_4392_, lean_object* v_a_4393_, lean_object* v_a_4394_, lean_object* v_a_4395_){
_start:
{
lean_object* v___x_4397_; 
v___x_4397_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(v_expr_4390_, v_value_4391_, v_a_4392_, v_a_4393_, v_a_4394_, v_a_4395_);
return v___x_4397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___boxed(lean_object* v_00_u03b1_4398_, lean_object* v_expr_4399_, lean_object* v_value_4400_, lean_object* v_a_4401_, lean_object* v_a_4402_, lean_object* v_a_4403_, lean_object* v_a_4404_, lean_object* v_a_4405_){
_start:
{
lean_object* v_res_4406_; 
v_res_4406_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr(v_00_u03b1_4398_, v_expr_4399_, v_value_4400_, v_a_4401_, v_a_4402_, v_a_4403_, v_a_4404_);
lean_dec(v_a_4404_);
lean_dec_ref(v_a_4403_);
lean_dec(v_a_4402_);
lean_dec_ref(v_a_4401_);
return v_res_4406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(lean_object* v_e_4407_, lean_object* v_idx_4408_, lean_object* v_value_4409_, lean_object* v_a_4410_, lean_object* v_a_4411_, lean_object* v_a_4412_, lean_object* v_a_4413_){
_start:
{
lean_object* v_entry_4415_; lean_object* v___x_4417_; uint8_t v_isShared_4418_; uint8_t v_isSharedCheck_4461_; 
v_entry_4415_ = lean_ctor_get(v_e_4407_, 1);
v_isSharedCheck_4461_ = !lean_is_exclusive(v_e_4407_);
if (v_isSharedCheck_4461_ == 0)
{
lean_object* v_unused_4462_; 
v_unused_4462_ = lean_ctor_get(v_e_4407_, 0);
lean_dec(v_unused_4462_);
v___x_4417_ = v_e_4407_;
v_isShared_4418_ = v_isSharedCheck_4461_;
goto v_resetjp_4416_;
}
else
{
lean_inc(v_entry_4415_);
lean_dec(v_e_4407_);
v___x_4417_ = lean_box(0);
v_isShared_4418_ = v_isSharedCheck_4461_;
goto v_resetjp_4416_;
}
v_resetjp_4416_:
{
lean_object* v_snd_4419_; lean_object* v_fst_4420_; lean_object* v_fst_4421_; lean_object* v___x_4423_; uint8_t v_isShared_4424_; uint8_t v_isSharedCheck_4459_; 
v_snd_4419_ = lean_ctor_get(v_entry_4415_, 1);
lean_inc(v_snd_4419_);
v_fst_4420_ = lean_ctor_get(v_entry_4415_, 0);
lean_inc(v_fst_4420_);
lean_dec_ref(v_entry_4415_);
v_fst_4421_ = lean_ctor_get(v_snd_4419_, 0);
v_isSharedCheck_4459_ = !lean_is_exclusive(v_snd_4419_);
if (v_isSharedCheck_4459_ == 0)
{
lean_object* v_unused_4460_; 
v_unused_4460_ = lean_ctor_get(v_snd_4419_, 1);
lean_dec(v_unused_4460_);
v___x_4423_ = v_snd_4419_;
v_isShared_4424_ = v_isSharedCheck_4459_;
goto v_resetjp_4422_;
}
else
{
lean_inc(v_fst_4421_);
lean_dec(v_snd_4419_);
v___x_4423_ = lean_box(0);
v_isShared_4424_ = v_isSharedCheck_4459_;
goto v_resetjp_4422_;
}
v_resetjp_4422_:
{
lean_object* v___x_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; 
v___x_4425_ = l_Lean_instInhabitedExpr;
v___x_4426_ = lean_array_get(v___x_4425_, v_fst_4420_, v_idx_4408_);
lean_dec(v_fst_4420_);
v___x_4427_ = l_Lean_Meta_LazyDiscrTree_rootKey(v___x_4426_, v_a_4410_, v_a_4411_, v_a_4412_, v_a_4413_);
if (lean_obj_tag(v___x_4427_) == 0)
{
lean_object* v_a_4428_; lean_object* v___x_4430_; uint8_t v_isShared_4431_; uint8_t v_isSharedCheck_4450_; 
v_a_4428_ = lean_ctor_get(v___x_4427_, 0);
v_isSharedCheck_4450_ = !lean_is_exclusive(v___x_4427_);
if (v_isSharedCheck_4450_ == 0)
{
v___x_4430_ = v___x_4427_;
v_isShared_4431_ = v_isSharedCheck_4450_;
goto v_resetjp_4429_;
}
else
{
lean_inc(v_a_4428_);
lean_dec(v___x_4427_);
v___x_4430_ = lean_box(0);
v_isShared_4431_ = v_isSharedCheck_4450_;
goto v_resetjp_4429_;
}
v_resetjp_4429_:
{
lean_object* v_fst_4432_; lean_object* v_snd_4433_; lean_object* v___x_4435_; uint8_t v_isShared_4436_; uint8_t v_isSharedCheck_4449_; 
v_fst_4432_ = lean_ctor_get(v_a_4428_, 0);
v_snd_4433_ = lean_ctor_get(v_a_4428_, 1);
v_isSharedCheck_4449_ = !lean_is_exclusive(v_a_4428_);
if (v_isSharedCheck_4449_ == 0)
{
v___x_4435_ = v_a_4428_;
v_isShared_4436_ = v_isSharedCheck_4449_;
goto v_resetjp_4434_;
}
else
{
lean_inc(v_snd_4433_);
lean_inc(v_fst_4432_);
lean_dec(v_a_4428_);
v___x_4435_ = lean_box(0);
v_isShared_4436_ = v_isSharedCheck_4449_;
goto v_resetjp_4434_;
}
v_resetjp_4434_:
{
lean_object* v___x_4438_; 
if (v_isShared_4436_ == 0)
{
lean_ctor_set(v___x_4435_, 1, v_value_4409_);
lean_ctor_set(v___x_4435_, 0, v_fst_4421_);
v___x_4438_ = v___x_4435_;
goto v_reusejp_4437_;
}
else
{
lean_object* v_reuseFailAlloc_4448_; 
v_reuseFailAlloc_4448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4448_, 0, v_fst_4421_);
lean_ctor_set(v_reuseFailAlloc_4448_, 1, v_value_4409_);
v___x_4438_ = v_reuseFailAlloc_4448_;
goto v_reusejp_4437_;
}
v_reusejp_4437_:
{
lean_object* v___x_4440_; 
if (v_isShared_4424_ == 0)
{
lean_ctor_set(v___x_4423_, 1, v___x_4438_);
lean_ctor_set(v___x_4423_, 0, v_snd_4433_);
v___x_4440_ = v___x_4423_;
goto v_reusejp_4439_;
}
else
{
lean_object* v_reuseFailAlloc_4447_; 
v_reuseFailAlloc_4447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4447_, 0, v_snd_4433_);
lean_ctor_set(v_reuseFailAlloc_4447_, 1, v___x_4438_);
v___x_4440_ = v_reuseFailAlloc_4447_;
goto v_reusejp_4439_;
}
v_reusejp_4439_:
{
lean_object* v___x_4442_; 
if (v_isShared_4418_ == 0)
{
lean_ctor_set(v___x_4417_, 1, v___x_4440_);
lean_ctor_set(v___x_4417_, 0, v_fst_4432_);
v___x_4442_ = v___x_4417_;
goto v_reusejp_4441_;
}
else
{
lean_object* v_reuseFailAlloc_4446_; 
v_reuseFailAlloc_4446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4446_, 0, v_fst_4432_);
lean_ctor_set(v_reuseFailAlloc_4446_, 1, v___x_4440_);
v___x_4442_ = v_reuseFailAlloc_4446_;
goto v_reusejp_4441_;
}
v_reusejp_4441_:
{
lean_object* v___x_4444_; 
if (v_isShared_4431_ == 0)
{
lean_ctor_set(v___x_4430_, 0, v___x_4442_);
v___x_4444_ = v___x_4430_;
goto v_reusejp_4443_;
}
else
{
lean_object* v_reuseFailAlloc_4445_; 
v_reuseFailAlloc_4445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4445_, 0, v___x_4442_);
v___x_4444_ = v_reuseFailAlloc_4445_;
goto v_reusejp_4443_;
}
v_reusejp_4443_:
{
return v___x_4444_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4451_; lean_object* v___x_4453_; uint8_t v_isShared_4454_; uint8_t v_isSharedCheck_4458_; 
lean_del_object(v___x_4423_);
lean_dec(v_fst_4421_);
lean_del_object(v___x_4417_);
lean_dec(v_value_4409_);
v_a_4451_ = lean_ctor_get(v___x_4427_, 0);
v_isSharedCheck_4458_ = !lean_is_exclusive(v___x_4427_);
if (v_isSharedCheck_4458_ == 0)
{
v___x_4453_ = v___x_4427_;
v_isShared_4454_ = v_isSharedCheck_4458_;
goto v_resetjp_4452_;
}
else
{
lean_inc(v_a_4451_);
lean_dec(v___x_4427_);
v___x_4453_ = lean_box(0);
v_isShared_4454_ = v_isSharedCheck_4458_;
goto v_resetjp_4452_;
}
v_resetjp_4452_:
{
lean_object* v___x_4456_; 
if (v_isShared_4454_ == 0)
{
v___x_4456_ = v___x_4453_;
goto v_reusejp_4455_;
}
else
{
lean_object* v_reuseFailAlloc_4457_; 
v_reuseFailAlloc_4457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4457_, 0, v_a_4451_);
v___x_4456_ = v_reuseFailAlloc_4457_;
goto v_reusejp_4455_;
}
v_reusejp_4455_:
{
return v___x_4456_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg___boxed(lean_object* v_e_4463_, lean_object* v_idx_4464_, lean_object* v_value_4465_, lean_object* v_a_4466_, lean_object* v_a_4467_, lean_object* v_a_4468_, lean_object* v_a_4469_, lean_object* v_a_4470_){
_start:
{
lean_object* v_res_4471_; 
v_res_4471_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(v_e_4463_, v_idx_4464_, v_value_4465_, v_a_4466_, v_a_4467_, v_a_4468_, v_a_4469_);
lean_dec(v_a_4469_);
lean_dec_ref(v_a_4468_);
lean_dec(v_a_4467_);
lean_dec_ref(v_a_4466_);
lean_dec(v_idx_4464_);
return v_res_4471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry(lean_object* v_00_u03b1_4472_, lean_object* v_e_4473_, lean_object* v_idx_4474_, lean_object* v_value_4475_, lean_object* v_a_4476_, lean_object* v_a_4477_, lean_object* v_a_4478_, lean_object* v_a_4479_){
_start:
{
lean_object* v___x_4481_; 
v___x_4481_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(v_e_4473_, v_idx_4474_, v_value_4475_, v_a_4476_, v_a_4477_, v_a_4478_, v_a_4479_);
return v___x_4481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___boxed(lean_object* v_00_u03b1_4482_, lean_object* v_e_4483_, lean_object* v_idx_4484_, lean_object* v_value_4485_, lean_object* v_a_4486_, lean_object* v_a_4487_, lean_object* v_a_4488_, lean_object* v_a_4489_, lean_object* v_a_4490_){
_start:
{
lean_object* v_res_4491_; 
v_res_4491_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry(v_00_u03b1_4482_, v_e_4483_, v_idx_4484_, v_value_4485_, v_a_4486_, v_a_4487_, v_a_4488_, v_a_4489_);
lean_dec(v_a_4489_);
lean_dec_ref(v_a_4488_);
lean_dec(v_a_4487_);
lean_dec_ref(v_a_4486_);
lean_dec(v_idx_4484_);
return v_res_4491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_ImportData_new(){
_start:
{
lean_object* v___x_4495_; lean_object* v___x_4496_; 
v___x_4495_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_ImportData_new___closed__0));
v___x_4496_ = lean_st_mk_ref(v___x_4495_);
return v___x_4496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_ImportData_new___boxed(lean_object* v_a_4497_){
_start:
{
lean_object* v_res_4498_; 
v_res_4498_ = l_Lean_Meta_LazyDiscrTree_ImportData_new();
return v_res_4498_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0(void){
_start:
{
lean_object* v___x_4499_; 
v___x_4499_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4499_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1(void){
_start:
{
lean_object* v___x_4500_; lean_object* v___x_4501_; 
v___x_4500_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0);
v___x_4501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4501_, 0, v___x_4500_);
return v___x_4501_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2(void){
_start:
{
lean_object* v___x_4502_; lean_object* v___x_4503_; 
v___x_4502_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1);
v___x_4503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4503_, 0, v___x_4502_);
lean_ctor_set(v___x_4503_, 1, v___x_4502_);
return v___x_4503_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3(void){
_start:
{
lean_object* v___x_4504_; lean_object* v___x_4505_; 
v___x_4504_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1);
v___x_4505_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4505_, 0, v___x_4504_);
lean_ctor_set(v___x_4505_, 1, v___x_4504_);
lean_ctor_set(v___x_4505_, 2, v___x_4504_);
lean_ctor_set(v___x_4505_, 3, v___x_4504_);
lean_ctor_set(v___x_4505_, 4, v___x_4504_);
lean_ctor_set(v___x_4505_, 5, v___x_4504_);
return v___x_4505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Cache_empty(lean_object* v_ngen_4506_){
_start:
{
lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; 
v___x_4507_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2);
v___x_4508_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3);
v___x_4509_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4509_, 0, v_ngen_4506_);
lean_ctor_set(v___x_4509_, 1, v___x_4507_);
lean_ctor_set(v___x_4509_, 2, v___x_4508_);
return v___x_4509_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName(lean_object* v_env_4510_, lean_object* v_declName_4511_){
_start:
{
uint8_t v___x_4512_; 
v___x_4512_ = l_Lean_isPrivateName(v_declName_4511_);
if (v___x_4512_ == 0)
{
return v___x_4512_;
}
else
{
lean_object* v___x_4513_; 
v___x_4513_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4510_, v_declName_4511_);
if (lean_obj_tag(v___x_4513_) == 0)
{
return v___x_4512_;
}
else
{
lean_object* v_val_4514_; lean_object* v___x_4515_; uint8_t v_isModule_4516_; 
v_val_4514_ = lean_ctor_get(v___x_4513_, 0);
lean_inc(v_val_4514_);
lean_dec_ref_known(v___x_4513_, 1);
v___x_4515_ = l_Lean_Environment_header(v_env_4510_);
v_isModule_4516_ = lean_ctor_get_uint8(v___x_4515_, sizeof(void*)*7 + 4);
if (v_isModule_4516_ == 0)
{
lean_dec_ref(v___x_4515_);
lean_dec(v_val_4514_);
return v_isModule_4516_;
}
else
{
lean_object* v_modules_4517_; lean_object* v___x_4518_; uint8_t v___x_4519_; 
v_modules_4517_ = lean_ctor_get(v___x_4515_, 3);
lean_inc_ref(v_modules_4517_);
lean_dec_ref(v___x_4515_);
v___x_4518_ = lean_array_get_size(v_modules_4517_);
v___x_4519_ = lean_nat_dec_lt(v_val_4514_, v___x_4518_);
if (v___x_4519_ == 0)
{
lean_dec_ref(v_modules_4517_);
lean_dec(v_val_4514_);
return v___x_4519_;
}
else
{
lean_object* v___x_4520_; lean_object* v_toImport_4521_; uint8_t v_importAll_4522_; 
v___x_4520_ = lean_array_fget(v_modules_4517_, v_val_4514_);
lean_dec(v_val_4514_);
lean_dec_ref(v_modules_4517_);
v_toImport_4521_ = lean_ctor_get(v___x_4520_, 0);
lean_inc_ref(v_toImport_4521_);
lean_dec(v___x_4520_);
v_importAll_4522_ = lean_ctor_get_uint8(v_toImport_4521_, sizeof(void*)*1);
lean_dec_ref(v_toImport_4521_);
return v_importAll_4522_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName___boxed(lean_object* v_env_4523_, lean_object* v_declName_4524_){
_start:
{
uint8_t v_res_4525_; lean_object* v_r_4526_; 
v_res_4525_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName(v_env_4523_, v_declName_4524_);
lean_dec(v_declName_4524_);
lean_dec_ref(v_env_4523_);
v_r_4526_ = lean_box(v_res_4525_);
return v_r_4526_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_LazyDiscrTree_blacklistInsertion(lean_object* v_env_4532_, lean_object* v_declName_4533_){
_start:
{
uint8_t v___x_4534_; 
lean_inc(v_declName_4533_);
lean_inc_ref(v_env_4532_);
v___x_4534_ = l_Lean_Meta_allowCompletion(v_env_4532_, v_declName_4533_);
if (v___x_4534_ == 0)
{
uint8_t v___x_4535_; 
lean_dec(v_declName_4533_);
lean_dec_ref(v_env_4532_);
v___x_4535_ = 1;
return v___x_4535_;
}
else
{
lean_object* v___x_4536_; uint8_t v___x_4537_; uint8_t v___y_4547_; 
v___x_4536_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__1));
v___x_4537_ = lean_name_eq(v_declName_4533_, v___x_4536_);
if (v___x_4537_ == 0)
{
uint8_t v___x_4548_; 
lean_inc(v_declName_4533_);
v___x_4548_ = l_Lean_Name_isInternalDetail(v_declName_4533_);
if (v___x_4548_ == 0)
{
lean_dec_ref(v_env_4532_);
v___y_4547_ = v___x_4548_;
goto v___jp_4546_;
}
else
{
uint8_t v___x_4549_; 
v___x_4549_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName(v_env_4532_, v_declName_4533_);
lean_dec_ref(v_env_4532_);
if (v___x_4549_ == 0)
{
v___y_4547_ = v___x_4548_;
goto v___jp_4546_;
}
else
{
goto v___jp_4542_;
}
}
}
else
{
lean_dec(v_declName_4533_);
lean_dec_ref(v_env_4532_);
return v___x_4537_;
}
v___jp_4538_:
{
if (lean_obj_tag(v_declName_4533_) == 1)
{
lean_object* v_str_4539_; lean_object* v___x_4540_; uint8_t v___x_4541_; 
v_str_4539_ = lean_ctor_get(v_declName_4533_, 1);
lean_inc_ref(v_str_4539_);
lean_dec_ref_known(v_declName_4533_, 2);
v___x_4540_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__2));
v___x_4541_ = lean_string_dec_eq(v_str_4539_, v___x_4540_);
lean_dec_ref(v_str_4539_);
if (v___x_4541_ == 0)
{
return v___x_4537_;
}
else
{
return v___x_4534_;
}
}
else
{
lean_dec(v_declName_4533_);
return v___x_4537_;
}
}
v___jp_4542_:
{
if (lean_obj_tag(v_declName_4533_) == 1)
{
lean_object* v_str_4543_; lean_object* v___x_4544_; uint8_t v___x_4545_; 
v_str_4543_ = lean_ctor_get(v_declName_4533_, 1);
v___x_4544_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__3));
v___x_4545_ = lean_string_dec_eq(v_str_4543_, v___x_4544_);
if (v___x_4545_ == 0)
{
goto v___jp_4538_;
}
else
{
lean_dec_ref_known(v_declName_4533_, 2);
return v___x_4534_;
}
}
else
{
goto v___jp_4538_;
}
}
v___jp_4546_:
{
if (v___y_4547_ == 0)
{
goto v___jp_4542_;
}
else
{
lean_dec(v_declName_4533_);
return v___y_4547_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_blacklistInsertion___boxed(lean_object* v_env_4550_, lean_object* v_declName_4551_){
_start:
{
uint8_t v_res_4552_; lean_object* v_r_4553_; 
v_res_4552_ = l_Lean_Meta_LazyDiscrTree_blacklistInsertion(v_env_4550_, v_declName_4551_);
v_r_4553_ = lean_box(v_res_4552_);
return v_r_4553_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(lean_object* v_opts_4554_, lean_object* v_opt_4555_){
_start:
{
lean_object* v_name_4556_; lean_object* v_defValue_4557_; lean_object* v_map_4558_; lean_object* v___x_4559_; 
v_name_4556_ = lean_ctor_get(v_opt_4555_, 0);
v_defValue_4557_ = lean_ctor_get(v_opt_4555_, 1);
v_map_4558_ = lean_ctor_get(v_opts_4554_, 0);
v___x_4559_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4558_, v_name_4556_);
if (lean_obj_tag(v___x_4559_) == 0)
{
uint8_t v___x_4560_; 
v___x_4560_ = lean_unbox(v_defValue_4557_);
return v___x_4560_;
}
else
{
lean_object* v_val_4561_; 
v_val_4561_ = lean_ctor_get(v___x_4559_, 0);
lean_inc(v_val_4561_);
lean_dec_ref_known(v___x_4559_, 1);
if (lean_obj_tag(v_val_4561_) == 1)
{
uint8_t v_v_4562_; 
v_v_4562_ = lean_ctor_get_uint8(v_val_4561_, 0);
lean_dec_ref_known(v_val_4561_, 0);
return v_v_4562_;
}
else
{
uint8_t v___x_4563_; 
lean_dec(v_val_4561_);
v___x_4563_ = lean_unbox(v_defValue_4557_);
return v___x_4563_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0___boxed(lean_object* v_opts_4564_, lean_object* v_opt_4565_){
_start:
{
uint8_t v_res_4566_; lean_object* v_r_4567_; 
v_res_4566_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(v_opts_4564_, v_opt_4565_);
lean_dec_ref(v_opt_4565_);
lean_dec_ref(v_opts_4564_);
v_r_4567_ = lean_box(v_res_4566_);
return v_r_4567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1(lean_object* v_opts_4568_, lean_object* v_opt_4569_){
_start:
{
lean_object* v_name_4570_; lean_object* v_defValue_4571_; lean_object* v_map_4572_; lean_object* v___x_4573_; 
v_name_4570_ = lean_ctor_get(v_opt_4569_, 0);
v_defValue_4571_ = lean_ctor_get(v_opt_4569_, 1);
v_map_4572_ = lean_ctor_get(v_opts_4568_, 0);
v___x_4573_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4572_, v_name_4570_);
if (lean_obj_tag(v___x_4573_) == 0)
{
lean_inc(v_defValue_4571_);
return v_defValue_4571_;
}
else
{
lean_object* v_val_4574_; 
v_val_4574_ = lean_ctor_get(v___x_4573_, 0);
lean_inc(v_val_4574_);
lean_dec_ref_known(v___x_4573_, 1);
if (lean_obj_tag(v_val_4574_) == 3)
{
lean_object* v_v_4575_; 
v_v_4575_ = lean_ctor_get(v_val_4574_, 0);
lean_inc(v_v_4575_);
lean_dec_ref_known(v_val_4574_, 1);
return v_v_4575_;
}
else
{
lean_dec(v_val_4574_);
lean_inc(v_defValue_4571_);
return v_defValue_4571_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1___boxed(lean_object* v_opts_4576_, lean_object* v_opt_4577_){
_start:
{
lean_object* v_res_4578_; 
v_res_4578_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1(v_opts_4576_, v_opt_4577_);
lean_dec_ref(v_opt_4577_);
lean_dec_ref(v_opts_4576_);
return v_res_4578_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg(lean_object* v_as_4579_, size_t v_i_4580_, size_t v_stop_4581_, lean_object* v_b_4582_){
_start:
{
uint8_t v___x_4583_; 
v___x_4583_ = lean_usize_dec_eq(v_i_4580_, v_stop_4581_);
if (v___x_4583_ == 0)
{
lean_object* v___x_4584_; lean_object* v_key_4585_; lean_object* v_entry_4586_; lean_object* v___x_4587_; size_t v___x_4588_; size_t v___x_4589_; 
v___x_4584_ = lean_array_uget_borrowed(v_as_4579_, v_i_4580_);
v_key_4585_ = lean_ctor_get(v___x_4584_, 0);
v_entry_4586_ = lean_ctor_get(v___x_4584_, 1);
lean_inc_ref(v_entry_4586_);
lean_inc(v_key_4585_);
v___x_4587_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg(v_b_4582_, v_key_4585_, v_entry_4586_);
v___x_4588_ = ((size_t)1ULL);
v___x_4589_ = lean_usize_add(v_i_4580_, v___x_4588_);
v_i_4580_ = v___x_4589_;
v_b_4582_ = v___x_4587_;
goto _start;
}
else
{
return v_b_4582_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg___boxed(lean_object* v_as_4591_, lean_object* v_i_4592_, lean_object* v_stop_4593_, lean_object* v_b_4594_){
_start:
{
size_t v_i_boxed_4595_; size_t v_stop_boxed_4596_; lean_object* v_res_4597_; 
v_i_boxed_4595_ = lean_unbox_usize(v_i_4592_);
lean_dec(v_i_4592_);
v_stop_boxed_4596_ = lean_unbox_usize(v_stop_4593_);
lean_dec(v_stop_4593_);
v_res_4597_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg(v_as_4591_, v_i_boxed_4595_, v_stop_boxed_4596_, v_b_4594_);
lean_dec_ref(v_as_4591_);
return v_res_4597_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0(void){
_start:
{
lean_object* v___x_4598_; 
v___x_4598_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4598_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1(void){
_start:
{
lean_object* v___x_4599_; lean_object* v___x_4600_; 
v___x_4599_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0);
v___x_4600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4600_, 0, v___x_4599_);
return v___x_4600_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2(void){
_start:
{
lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; 
v___x_4601_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4602_ = lean_unsigned_to_nat(0u);
v___x_4603_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4603_, 0, v___x_4602_);
lean_ctor_set(v___x_4603_, 1, v___x_4602_);
lean_ctor_set(v___x_4603_, 2, v___x_4602_);
lean_ctor_set(v___x_4603_, 3, v___x_4602_);
lean_ctor_set(v___x_4603_, 4, v___x_4601_);
lean_ctor_set(v___x_4603_, 5, v___x_4601_);
lean_ctor_set(v___x_4603_, 6, v___x_4601_);
lean_ctor_set(v___x_4603_, 7, v___x_4601_);
lean_ctor_set(v___x_4603_, 8, v___x_4601_);
lean_ctor_set(v___x_4603_, 9, v___x_4601_);
return v___x_4603_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3(void){
_start:
{
lean_object* v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; 
v___x_4604_ = lean_unsigned_to_nat(32u);
v___x_4605_ = lean_mk_empty_array_with_capacity(v___x_4604_);
v___x_4606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4606_, 0, v___x_4605_);
return v___x_4606_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4(void){
_start:
{
size_t v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; 
v___x_4607_ = ((size_t)5ULL);
v___x_4608_ = lean_unsigned_to_nat(0u);
v___x_4609_ = lean_unsigned_to_nat(32u);
v___x_4610_ = lean_mk_empty_array_with_capacity(v___x_4609_);
v___x_4611_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3);
v___x_4612_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4612_, 0, v___x_4611_);
lean_ctor_set(v___x_4612_, 1, v___x_4610_);
lean_ctor_set(v___x_4612_, 2, v___x_4608_);
lean_ctor_set(v___x_4612_, 3, v___x_4608_);
lean_ctor_set_usize(v___x_4612_, 4, v___x_4607_);
return v___x_4612_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5(void){
_start:
{
lean_object* v___x_4613_; lean_object* v___x_4614_; 
v___x_4613_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4614_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4614_, 0, v___x_4613_);
lean_ctor_set(v___x_4614_, 1, v___x_4613_);
lean_ctor_set(v___x_4614_, 2, v___x_4613_);
lean_ctor_set(v___x_4614_, 3, v___x_4613_);
lean_ctor_set(v___x_4614_, 4, v___x_4613_);
return v___x_4614_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6(void){
_start:
{
lean_object* v___x_4615_; lean_object* v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; 
v___x_4615_ = lean_box(1);
v___x_4616_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4617_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4618_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4618_, 0, v___x_4617_);
lean_ctor_set(v___x_4618_, 1, v___x_4616_);
lean_ctor_set(v___x_4618_, 2, v___x_4615_);
return v___x_4618_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__8(void){
_start:
{
lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; 
v___x_4621_ = lean_unsigned_to_nat(1u);
v___x_4622_ = l_Lean_firstFrontendMacroScope;
v___x_4623_ = lean_nat_add(v___x_4622_, v___x_4621_);
return v___x_4623_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10(void){
_start:
{
lean_object* v___x_4628_; uint64_t v___x_4629_; lean_object* v___x_4630_; 
v___x_4628_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4629_ = 0ULL;
v___x_4630_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4630_, 0, v___x_4628_);
lean_ctor_set_uint64(v___x_4630_, sizeof(void*)*1, v___x_4629_);
return v___x_4630_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11(void){
_start:
{
lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; 
v___x_4631_ = l_Lean_NameSet_empty;
v___x_4632_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4633_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4633_, 0, v___x_4632_);
lean_ctor_set(v___x_4633_, 1, v___x_4632_);
lean_ctor_set(v___x_4633_, 2, v___x_4631_);
return v___x_4633_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12(void){
_start:
{
lean_object* v___x_4634_; lean_object* v___x_4635_; uint8_t v___x_4636_; lean_object* v___x_4637_; 
v___x_4634_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4635_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4636_ = 1;
v___x_4637_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4637_, 0, v___x_4635_);
lean_ctor_set(v___x_4637_, 1, v___x_4635_);
lean_ctor_set(v___x_4637_, 2, v___x_4634_);
lean_ctor_set_uint8(v___x_4637_, sizeof(void*)*3, v___x_4636_);
return v___x_4637_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13(void){
_start:
{
lean_object* v___x_4638_; lean_object* v___x_4639_; 
v___x_4638_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4639_, 0, v___x_4638_);
lean_ctor_set(v___x_4639_, 1, v___x_4638_);
return v___x_4639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(lean_object* v_cctx_4640_, lean_object* v_env_4641_, lean_object* v_modName_4642_, lean_object* v_d_4643_, lean_object* v_cacheRef_4644_, lean_object* v_tree_4645_, lean_object* v_act_4646_, lean_object* v_c_4647_){
_start:
{
uint8_t v___x_4649_; 
lean_inc_ref(v_c_4647_);
v___x_4649_ = l_Lean_AsyncConstantInfo_isUnsafe(v_c_4647_);
if (v___x_4649_ == 0)
{
lean_object* v_name_4650_; uint8_t v___x_4651_; 
v_name_4650_ = lean_ctor_get(v_c_4647_, 0);
lean_inc_n(v_name_4650_, 2);
lean_inc_ref(v_env_4641_);
v___x_4651_ = l_Lean_Meta_LazyDiscrTree_blacklistInsertion(v_env_4641_, v_name_4650_);
if (v___x_4651_ == 0)
{
lean_object* v___x_4652_; lean_object* v_ngen_4653_; lean_object* v_core_4654_; lean_object* v_meta_4655_; lean_object* v___x_4657_; uint8_t v_isShared_4658_; uint8_t v_isSharedCheck_4789_; 
v___x_4652_ = lean_st_ref_get(v_cacheRef_4644_);
v_ngen_4653_ = lean_ctor_get(v___x_4652_, 0);
v_core_4654_ = lean_ctor_get(v___x_4652_, 1);
v_meta_4655_ = lean_ctor_get(v___x_4652_, 2);
v_isSharedCheck_4789_ = !lean_is_exclusive(v___x_4652_);
if (v_isSharedCheck_4789_ == 0)
{
v___x_4657_ = v___x_4652_;
v_isShared_4658_ = v_isSharedCheck_4789_;
goto v_resetjp_4656_;
}
else
{
lean_inc(v_meta_4655_);
lean_inc(v_core_4654_);
lean_inc(v_ngen_4653_);
lean_dec(v___x_4652_);
v___x_4657_ = lean_box(0);
v_isShared_4658_ = v_isSharedCheck_4789_;
goto v_resetjp_4656_;
}
v_resetjp_4656_:
{
lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4664_; lean_object* v___x_4665_; uint8_t v___x_4666_; lean_object* v___x_4667_; uint8_t v___x_4668_; uint8_t v___x_4669_; uint8_t v___x_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v_fileName_4687_; lean_object* v_fileMap_4688_; lean_object* v_options_4689_; lean_object* v_currRecDepth_4690_; lean_object* v_maxRecDepth_4691_; lean_object* v_ref_4692_; lean_object* v_currNamespace_4693_; lean_object* v_openDecls_4694_; lean_object* v_initHeartbeats_4695_; lean_object* v_maxHeartbeats_4696_; lean_object* v_quotContext_4697_; lean_object* v_currMacroScope_4698_; uint8_t v_diag_4699_; lean_object* v_cancelTk_x3f_4700_; uint8_t v_suppressElabErrors_4701_; lean_object* v___x_4703_; uint8_t v_isShared_4704_; uint8_t v_isSharedCheck_4787_; 
v___x_4659_ = lean_unsigned_to_nat(0u);
v___x_4660_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2);
v___x_4661_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4662_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5);
lean_inc_ref(v_ngen_4653_);
v___x_4663_ = l_Lean_Meta_LazyDiscrTree_Cache_empty(v_ngen_4653_);
v___x_4664_ = lean_st_ref_set(v_cacheRef_4644_, v___x_4663_);
v___x_4665_ = lean_box(1);
v___x_4666_ = 1;
v___x_4667_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4667_, 0, v___x_4660_);
lean_ctor_set(v___x_4667_, 1, v_meta_4655_);
lean_ctor_set(v___x_4667_, 2, v___x_4665_);
lean_ctor_set(v___x_4667_, 3, v___x_4661_);
lean_ctor_set(v___x_4667_, 4, v___x_4662_);
v___x_4668_ = 2;
v___x_4669_ = 0;
v___x_4670_ = 2;
v___x_4671_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_4671_, 0, v___x_4651_);
lean_ctor_set_uint8(v___x_4671_, 1, v___x_4651_);
lean_ctor_set_uint8(v___x_4671_, 2, v___x_4651_);
lean_ctor_set_uint8(v___x_4671_, 3, v___x_4651_);
lean_ctor_set_uint8(v___x_4671_, 4, v___x_4651_);
lean_ctor_set_uint8(v___x_4671_, 5, v___x_4666_);
lean_ctor_set_uint8(v___x_4671_, 6, v___x_4666_);
lean_ctor_set_uint8(v___x_4671_, 7, v___x_4651_);
lean_ctor_set_uint8(v___x_4671_, 8, v___x_4666_);
lean_ctor_set_uint8(v___x_4671_, 9, v___x_4668_);
lean_ctor_set_uint8(v___x_4671_, 10, v___x_4669_);
lean_ctor_set_uint8(v___x_4671_, 11, v___x_4666_);
lean_ctor_set_uint8(v___x_4671_, 12, v___x_4666_);
lean_ctor_set_uint8(v___x_4671_, 13, v___x_4666_);
lean_ctor_set_uint8(v___x_4671_, 14, v___x_4670_);
lean_ctor_set_uint8(v___x_4671_, 15, v___x_4666_);
lean_ctor_set_uint8(v___x_4671_, 16, v___x_4666_);
lean_ctor_set_uint8(v___x_4671_, 17, v___x_4666_);
lean_ctor_set_uint8(v___x_4671_, 18, v___x_4666_);
lean_ctor_set_uint8(v___x_4671_, 19, v___x_4651_);
v___x_4672_ = l_Lean_Meta_Config_toConfigWithKey(v___x_4671_);
v___x_4673_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6);
v___x_4674_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__7));
v___x_4675_ = lean_box(0);
v___x_4676_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4676_, 0, v___x_4672_);
lean_ctor_set(v___x_4676_, 1, v___x_4665_);
lean_ctor_set(v___x_4676_, 2, v___x_4673_);
lean_ctor_set(v___x_4676_, 3, v___x_4674_);
lean_ctor_set(v___x_4676_, 4, v___x_4675_);
lean_ctor_set(v___x_4676_, 5, v___x_4659_);
lean_ctor_set(v___x_4676_, 6, v___x_4675_);
lean_ctor_set_uint8(v___x_4676_, sizeof(void*)*7, v___x_4651_);
lean_ctor_set_uint8(v___x_4676_, sizeof(void*)*7 + 1, v___x_4651_);
lean_ctor_set_uint8(v___x_4676_, sizeof(void*)*7 + 2, v___x_4651_);
lean_ctor_set_uint8(v___x_4676_, sizeof(void*)*7 + 3, v___x_4666_);
v___x_4677_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__8, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__8_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__8);
v___x_4678_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__9));
v___x_4679_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10);
v___x_4680_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11);
v___x_4681_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12);
v___x_4682_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_4682_, 0, v_env_4641_);
lean_ctor_set(v___x_4682_, 1, v___x_4677_);
lean_ctor_set(v___x_4682_, 2, v_ngen_4653_);
lean_ctor_set(v___x_4682_, 3, v___x_4678_);
lean_ctor_set(v___x_4682_, 4, v___x_4679_);
lean_ctor_set(v___x_4682_, 5, v_core_4654_);
lean_ctor_set(v___x_4682_, 6, v___x_4680_);
lean_ctor_set(v___x_4682_, 7, v___x_4681_);
lean_ctor_set(v___x_4682_, 8, v___x_4674_);
v___x_4683_ = lean_st_mk_ref(v___x_4682_);
v___x_4684_ = l_Lean_inheritedTraceOptions;
v___x_4685_ = lean_st_ref_get(v___x_4684_);
v___x_4686_ = lean_st_ref_get(v___x_4683_);
v_fileName_4687_ = lean_ctor_get(v_cctx_4640_, 0);
v_fileMap_4688_ = lean_ctor_get(v_cctx_4640_, 1);
v_options_4689_ = lean_ctor_get(v_cctx_4640_, 2);
v_currRecDepth_4690_ = lean_ctor_get(v_cctx_4640_, 3);
v_maxRecDepth_4691_ = lean_ctor_get(v_cctx_4640_, 4);
v_ref_4692_ = lean_ctor_get(v_cctx_4640_, 5);
v_currNamespace_4693_ = lean_ctor_get(v_cctx_4640_, 6);
v_openDecls_4694_ = lean_ctor_get(v_cctx_4640_, 7);
v_initHeartbeats_4695_ = lean_ctor_get(v_cctx_4640_, 8);
v_maxHeartbeats_4696_ = lean_ctor_get(v_cctx_4640_, 9);
v_quotContext_4697_ = lean_ctor_get(v_cctx_4640_, 10);
v_currMacroScope_4698_ = lean_ctor_get(v_cctx_4640_, 11);
v_diag_4699_ = lean_ctor_get_uint8(v_cctx_4640_, sizeof(void*)*14);
v_cancelTk_x3f_4700_ = lean_ctor_get(v_cctx_4640_, 12);
v_suppressElabErrors_4701_ = lean_ctor_get_uint8(v_cctx_4640_, sizeof(void*)*14 + 1);
v_isSharedCheck_4787_ = !lean_is_exclusive(v_cctx_4640_);
if (v_isSharedCheck_4787_ == 0)
{
lean_object* v_unused_4788_; 
v_unused_4788_ = lean_ctor_get(v_cctx_4640_, 13);
lean_dec(v_unused_4788_);
v___x_4703_ = v_cctx_4640_;
v_isShared_4704_ = v_isSharedCheck_4787_;
goto v_resetjp_4702_;
}
else
{
lean_inc(v_cancelTk_x3f_4700_);
lean_inc(v_currMacroScope_4698_);
lean_inc(v_quotContext_4697_);
lean_inc(v_maxHeartbeats_4696_);
lean_inc(v_initHeartbeats_4695_);
lean_inc(v_openDecls_4694_);
lean_inc(v_currNamespace_4693_);
lean_inc(v_ref_4692_);
lean_inc(v_maxRecDepth_4691_);
lean_inc(v_currRecDepth_4690_);
lean_inc(v_options_4689_);
lean_inc(v_fileMap_4688_);
lean_inc(v_fileName_4687_);
lean_dec(v_cctx_4640_);
v___x_4703_ = lean_box(0);
v_isShared_4704_ = v_isSharedCheck_4787_;
goto v_resetjp_4702_;
}
v_resetjp_4702_:
{
lean_object* v_env_4705_; lean_object* v___x_4707_; 
v_env_4705_ = lean_ctor_get(v___x_4686_, 0);
lean_inc_ref(v_env_4705_);
lean_dec(v___x_4686_);
lean_inc_ref(v_options_4689_);
if (v_isShared_4704_ == 0)
{
lean_ctor_set(v___x_4703_, 13, v___x_4685_);
v___x_4707_ = v___x_4703_;
goto v_reusejp_4706_;
}
else
{
lean_object* v_reuseFailAlloc_4786_; 
v_reuseFailAlloc_4786_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_4786_, 0, v_fileName_4687_);
lean_ctor_set(v_reuseFailAlloc_4786_, 1, v_fileMap_4688_);
lean_ctor_set(v_reuseFailAlloc_4786_, 2, v_options_4689_);
lean_ctor_set(v_reuseFailAlloc_4786_, 3, v_currRecDepth_4690_);
lean_ctor_set(v_reuseFailAlloc_4786_, 4, v_maxRecDepth_4691_);
lean_ctor_set(v_reuseFailAlloc_4786_, 5, v_ref_4692_);
lean_ctor_set(v_reuseFailAlloc_4786_, 6, v_currNamespace_4693_);
lean_ctor_set(v_reuseFailAlloc_4786_, 7, v_openDecls_4694_);
lean_ctor_set(v_reuseFailAlloc_4786_, 8, v_initHeartbeats_4695_);
lean_ctor_set(v_reuseFailAlloc_4786_, 9, v_maxHeartbeats_4696_);
lean_ctor_set(v_reuseFailAlloc_4786_, 10, v_quotContext_4697_);
lean_ctor_set(v_reuseFailAlloc_4786_, 11, v_currMacroScope_4698_);
lean_ctor_set(v_reuseFailAlloc_4786_, 12, v_cancelTk_x3f_4700_);
lean_ctor_set(v_reuseFailAlloc_4786_, 13, v___x_4685_);
lean_ctor_set_uint8(v_reuseFailAlloc_4786_, sizeof(void*)*14, v_diag_4699_);
lean_ctor_set_uint8(v_reuseFailAlloc_4786_, sizeof(void*)*14 + 1, v_suppressElabErrors_4701_);
v___x_4707_ = v_reuseFailAlloc_4786_;
goto v_reusejp_4706_;
}
v_reusejp_4706_:
{
lean_object* v___x_4708_; uint8_t v___x_4709_; lean_object* v___y_4711_; lean_object* v___y_4712_; uint8_t v___y_4764_; uint8_t v___x_4785_; 
v___x_4708_ = l_Lean_diagnostics;
v___x_4709_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(v_options_4689_, v___x_4708_);
v___x_4785_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4705_);
lean_dec_ref(v_env_4705_);
if (v___x_4785_ == 0)
{
if (v___x_4709_ == 0)
{
lean_inc(v___x_4683_);
v___y_4711_ = v___x_4707_;
v___y_4712_ = v___x_4683_;
goto v___jp_4710_;
}
else
{
v___y_4764_ = v___x_4785_;
goto v___jp_4763_;
}
}
else
{
v___y_4764_ = v___x_4709_;
goto v___jp_4763_;
}
v___jp_4710_:
{
lean_object* v___x_4713_; lean_object* v_fileName_4714_; lean_object* v_fileMap_4715_; lean_object* v_currRecDepth_4716_; lean_object* v_ref_4717_; lean_object* v_currNamespace_4718_; lean_object* v_openDecls_4719_; lean_object* v_initHeartbeats_4720_; lean_object* v_maxHeartbeats_4721_; lean_object* v_quotContext_4722_; lean_object* v_currMacroScope_4723_; lean_object* v_cancelTk_x3f_4724_; uint8_t v_suppressElabErrors_4725_; lean_object* v_inheritedTraceOptions_4726_; lean_object* v___x_4728_; uint8_t v_isShared_4729_; uint8_t v_isSharedCheck_4760_; 
v___x_4713_ = lean_st_mk_ref(v___x_4667_);
v_fileName_4714_ = lean_ctor_get(v___y_4711_, 0);
v_fileMap_4715_ = lean_ctor_get(v___y_4711_, 1);
v_currRecDepth_4716_ = lean_ctor_get(v___y_4711_, 3);
v_ref_4717_ = lean_ctor_get(v___y_4711_, 5);
v_currNamespace_4718_ = lean_ctor_get(v___y_4711_, 6);
v_openDecls_4719_ = lean_ctor_get(v___y_4711_, 7);
v_initHeartbeats_4720_ = lean_ctor_get(v___y_4711_, 8);
v_maxHeartbeats_4721_ = lean_ctor_get(v___y_4711_, 9);
v_quotContext_4722_ = lean_ctor_get(v___y_4711_, 10);
v_currMacroScope_4723_ = lean_ctor_get(v___y_4711_, 11);
v_cancelTk_x3f_4724_ = lean_ctor_get(v___y_4711_, 12);
v_suppressElabErrors_4725_ = lean_ctor_get_uint8(v___y_4711_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_4726_ = lean_ctor_get(v___y_4711_, 13);
v_isSharedCheck_4760_ = !lean_is_exclusive(v___y_4711_);
if (v_isSharedCheck_4760_ == 0)
{
lean_object* v_unused_4761_; lean_object* v_unused_4762_; 
v_unused_4761_ = lean_ctor_get(v___y_4711_, 4);
lean_dec(v_unused_4761_);
v_unused_4762_ = lean_ctor_get(v___y_4711_, 2);
lean_dec(v_unused_4762_);
v___x_4728_ = v___y_4711_;
v_isShared_4729_ = v_isSharedCheck_4760_;
goto v_resetjp_4727_;
}
else
{
lean_inc(v_inheritedTraceOptions_4726_);
lean_inc(v_cancelTk_x3f_4724_);
lean_inc(v_currMacroScope_4723_);
lean_inc(v_quotContext_4722_);
lean_inc(v_maxHeartbeats_4721_);
lean_inc(v_initHeartbeats_4720_);
lean_inc(v_openDecls_4719_);
lean_inc(v_currNamespace_4718_);
lean_inc(v_ref_4717_);
lean_inc(v_currRecDepth_4716_);
lean_inc(v_fileMap_4715_);
lean_inc(v_fileName_4714_);
lean_dec(v___y_4711_);
v___x_4728_ = lean_box(0);
v_isShared_4729_ = v_isSharedCheck_4760_;
goto v_resetjp_4727_;
}
v_resetjp_4727_:
{
lean_object* v___x_4730_; lean_object* v___x_4731_; lean_object* v___x_4733_; 
v___x_4730_ = l_Lean_maxRecDepth;
v___x_4731_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1(v_options_4689_, v___x_4730_);
if (v_isShared_4729_ == 0)
{
lean_ctor_set(v___x_4728_, 4, v___x_4731_);
lean_ctor_set(v___x_4728_, 2, v_options_4689_);
v___x_4733_ = v___x_4728_;
goto v_reusejp_4732_;
}
else
{
lean_object* v_reuseFailAlloc_4759_; 
v_reuseFailAlloc_4759_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_4759_, 0, v_fileName_4714_);
lean_ctor_set(v_reuseFailAlloc_4759_, 1, v_fileMap_4715_);
lean_ctor_set(v_reuseFailAlloc_4759_, 2, v_options_4689_);
lean_ctor_set(v_reuseFailAlloc_4759_, 3, v_currRecDepth_4716_);
lean_ctor_set(v_reuseFailAlloc_4759_, 4, v___x_4731_);
lean_ctor_set(v_reuseFailAlloc_4759_, 5, v_ref_4717_);
lean_ctor_set(v_reuseFailAlloc_4759_, 6, v_currNamespace_4718_);
lean_ctor_set(v_reuseFailAlloc_4759_, 7, v_openDecls_4719_);
lean_ctor_set(v_reuseFailAlloc_4759_, 8, v_initHeartbeats_4720_);
lean_ctor_set(v_reuseFailAlloc_4759_, 9, v_maxHeartbeats_4721_);
lean_ctor_set(v_reuseFailAlloc_4759_, 10, v_quotContext_4722_);
lean_ctor_set(v_reuseFailAlloc_4759_, 11, v_currMacroScope_4723_);
lean_ctor_set(v_reuseFailAlloc_4759_, 12, v_cancelTk_x3f_4724_);
lean_ctor_set(v_reuseFailAlloc_4759_, 13, v_inheritedTraceOptions_4726_);
lean_ctor_set_uint8(v_reuseFailAlloc_4759_, sizeof(void*)*14 + 1, v_suppressElabErrors_4725_);
v___x_4733_ = v_reuseFailAlloc_4759_;
goto v_reusejp_4732_;
}
v_reusejp_4732_:
{
lean_object* v___x_4734_; 
lean_ctor_set_uint8(v___x_4733_, sizeof(void*)*14, v___x_4709_);
lean_inc(v___x_4713_);
lean_inc(v_name_4650_);
v___x_4734_ = lean_apply_7(v_act_4646_, v_name_4650_, v_c_4647_, v___x_4676_, v___x_4713_, v___x_4733_, v___y_4712_, lean_box(0));
if (lean_obj_tag(v___x_4734_) == 0)
{
lean_object* v_a_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; lean_object* v_ngen_4738_; lean_object* v_cache_4739_; lean_object* v_cache_4740_; lean_object* v___x_4742_; 
lean_dec(v_name_4650_);
lean_dec(v_modName_4642_);
v_a_4735_ = lean_ctor_get(v___x_4734_, 0);
lean_inc(v_a_4735_);
lean_dec_ref_known(v___x_4734_, 1);
v___x_4736_ = lean_st_ref_get(v___x_4713_);
lean_dec(v___x_4713_);
v___x_4737_ = lean_st_ref_get(v___x_4683_);
lean_dec(v___x_4683_);
v_ngen_4738_ = lean_ctor_get(v___x_4737_, 2);
lean_inc_ref(v_ngen_4738_);
v_cache_4739_ = lean_ctor_get(v___x_4737_, 5);
lean_inc_ref(v_cache_4739_);
lean_dec(v___x_4737_);
v_cache_4740_ = lean_ctor_get(v___x_4736_, 1);
lean_inc_ref(v_cache_4740_);
lean_dec(v___x_4736_);
if (v_isShared_4658_ == 0)
{
lean_ctor_set(v___x_4657_, 2, v_cache_4740_);
lean_ctor_set(v___x_4657_, 1, v_cache_4739_);
lean_ctor_set(v___x_4657_, 0, v_ngen_4738_);
v___x_4742_ = v___x_4657_;
goto v_reusejp_4741_;
}
else
{
lean_object* v_reuseFailAlloc_4753_; 
v_reuseFailAlloc_4753_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4753_, 0, v_ngen_4738_);
lean_ctor_set(v_reuseFailAlloc_4753_, 1, v_cache_4739_);
lean_ctor_set(v_reuseFailAlloc_4753_, 2, v_cache_4740_);
v___x_4742_ = v_reuseFailAlloc_4753_;
goto v_reusejp_4741_;
}
v_reusejp_4741_:
{
lean_object* v___x_4743_; lean_object* v___x_4744_; uint8_t v___x_4745_; 
v___x_4743_ = lean_st_ref_set(v_cacheRef_4644_, v___x_4742_);
v___x_4744_ = lean_array_get_size(v_a_4735_);
v___x_4745_ = lean_nat_dec_lt(v___x_4659_, v___x_4744_);
if (v___x_4745_ == 0)
{
lean_dec(v_a_4735_);
return v_tree_4645_;
}
else
{
uint8_t v___x_4746_; 
v___x_4746_ = lean_nat_dec_le(v___x_4744_, v___x_4744_);
if (v___x_4746_ == 0)
{
if (v___x_4745_ == 0)
{
lean_dec(v_a_4735_);
return v_tree_4645_;
}
else
{
size_t v___x_4747_; size_t v___x_4748_; lean_object* v___x_4749_; 
v___x_4747_ = ((size_t)0ULL);
v___x_4748_ = lean_usize_of_nat(v___x_4744_);
v___x_4749_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg(v_a_4735_, v___x_4747_, v___x_4748_, v_tree_4645_);
lean_dec(v_a_4735_);
return v___x_4749_;
}
}
else
{
size_t v___x_4750_; size_t v___x_4751_; lean_object* v___x_4752_; 
v___x_4750_ = ((size_t)0ULL);
v___x_4751_ = lean_usize_of_nat(v___x_4744_);
v___x_4752_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg(v_a_4735_, v___x_4750_, v___x_4751_, v_tree_4645_);
lean_dec(v_a_4735_);
return v___x_4752_;
}
}
}
}
else
{
lean_object* v_a_4754_; lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; 
lean_dec(v___x_4713_);
lean_dec(v___x_4683_);
lean_del_object(v___x_4657_);
v_a_4754_ = lean_ctor_get(v___x_4734_, 0);
lean_inc(v_a_4754_);
lean_dec_ref_known(v___x_4734_, 1);
v___x_4755_ = lean_st_ref_take(v_d_4643_);
v___x_4756_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4756_, 0, v_modName_4642_);
lean_ctor_set(v___x_4756_, 1, v_name_4650_);
lean_ctor_set(v___x_4756_, 2, v_a_4754_);
v___x_4757_ = lean_array_push(v___x_4755_, v___x_4756_);
v___x_4758_ = lean_st_ref_set(v_d_4643_, v___x_4757_);
return v_tree_4645_;
}
}
}
}
v___jp_4763_:
{
if (v___y_4764_ == 0)
{
lean_object* v___x_4765_; lean_object* v_env_4766_; lean_object* v_nextMacroScope_4767_; lean_object* v_ngen_4768_; lean_object* v_auxDeclNGen_4769_; lean_object* v_traceState_4770_; lean_object* v_messages_4771_; lean_object* v_infoState_4772_; lean_object* v_snapshotTasks_4773_; lean_object* v___x_4775_; uint8_t v_isShared_4776_; uint8_t v_isSharedCheck_4783_; 
v___x_4765_ = lean_st_ref_take(v___x_4683_);
v_env_4766_ = lean_ctor_get(v___x_4765_, 0);
v_nextMacroScope_4767_ = lean_ctor_get(v___x_4765_, 1);
v_ngen_4768_ = lean_ctor_get(v___x_4765_, 2);
v_auxDeclNGen_4769_ = lean_ctor_get(v___x_4765_, 3);
v_traceState_4770_ = lean_ctor_get(v___x_4765_, 4);
v_messages_4771_ = lean_ctor_get(v___x_4765_, 6);
v_infoState_4772_ = lean_ctor_get(v___x_4765_, 7);
v_snapshotTasks_4773_ = lean_ctor_get(v___x_4765_, 8);
v_isSharedCheck_4783_ = !lean_is_exclusive(v___x_4765_);
if (v_isSharedCheck_4783_ == 0)
{
lean_object* v_unused_4784_; 
v_unused_4784_ = lean_ctor_get(v___x_4765_, 5);
lean_dec(v_unused_4784_);
v___x_4775_ = v___x_4765_;
v_isShared_4776_ = v_isSharedCheck_4783_;
goto v_resetjp_4774_;
}
else
{
lean_inc(v_snapshotTasks_4773_);
lean_inc(v_infoState_4772_);
lean_inc(v_messages_4771_);
lean_inc(v_traceState_4770_);
lean_inc(v_auxDeclNGen_4769_);
lean_inc(v_ngen_4768_);
lean_inc(v_nextMacroScope_4767_);
lean_inc(v_env_4766_);
lean_dec(v___x_4765_);
v___x_4775_ = lean_box(0);
v_isShared_4776_ = v_isSharedCheck_4783_;
goto v_resetjp_4774_;
}
v_resetjp_4774_:
{
lean_object* v___x_4777_; lean_object* v___x_4778_; lean_object* v___x_4780_; 
v___x_4777_ = l_Lean_Kernel_enableDiag(v_env_4766_, v___x_4709_);
v___x_4778_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13);
if (v_isShared_4776_ == 0)
{
lean_ctor_set(v___x_4775_, 5, v___x_4778_);
lean_ctor_set(v___x_4775_, 0, v___x_4777_);
v___x_4780_ = v___x_4775_;
goto v_reusejp_4779_;
}
else
{
lean_object* v_reuseFailAlloc_4782_; 
v_reuseFailAlloc_4782_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4782_, 0, v___x_4777_);
lean_ctor_set(v_reuseFailAlloc_4782_, 1, v_nextMacroScope_4767_);
lean_ctor_set(v_reuseFailAlloc_4782_, 2, v_ngen_4768_);
lean_ctor_set(v_reuseFailAlloc_4782_, 3, v_auxDeclNGen_4769_);
lean_ctor_set(v_reuseFailAlloc_4782_, 4, v_traceState_4770_);
lean_ctor_set(v_reuseFailAlloc_4782_, 5, v___x_4778_);
lean_ctor_set(v_reuseFailAlloc_4782_, 6, v_messages_4771_);
lean_ctor_set(v_reuseFailAlloc_4782_, 7, v_infoState_4772_);
lean_ctor_set(v_reuseFailAlloc_4782_, 8, v_snapshotTasks_4773_);
v___x_4780_ = v_reuseFailAlloc_4782_;
goto v_reusejp_4779_;
}
v_reusejp_4779_:
{
lean_object* v___x_4781_; 
v___x_4781_ = lean_st_ref_set(v___x_4683_, v___x_4780_);
lean_inc(v___x_4683_);
v___y_4711_ = v___x_4707_;
v___y_4712_ = v___x_4683_;
goto v___jp_4710_;
}
}
}
else
{
lean_inc(v___x_4683_);
v___y_4711_ = v___x_4707_;
v___y_4712_ = v___x_4683_;
goto v___jp_4710_;
}
}
}
}
}
}
else
{
lean_dec(v_name_4650_);
lean_dec_ref(v_c_4647_);
lean_dec_ref(v_act_4646_);
lean_dec(v_modName_4642_);
lean_dec_ref(v_env_4641_);
lean_dec_ref(v_cctx_4640_);
return v_tree_4645_;
}
}
else
{
lean_dec_ref(v_c_4647_);
lean_dec_ref(v_act_4646_);
lean_dec(v_modName_4642_);
lean_dec_ref(v_env_4641_);
lean_dec_ref(v_cctx_4640_);
return v_tree_4645_;
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
lean_object* v___x_4948_; lean_object* v_moduleData_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; lean_object* v_mname_4952_; lean_object* v___x_4953_; lean_object* v_mdata_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; 
v___x_4948_ = l_Lean_Environment_header(v_env_4938_);
v_moduleData_4949_ = lean_ctor_get(v___x_4948_, 6);
lean_inc_ref(v_moduleData_4949_);
v___x_4950_ = lean_box(0);
v___x_4951_ = l_Lean_EnvironmentHeader_moduleNames(v___x_4948_);
v_mname_4952_ = lean_array_get(v___x_4950_, v___x_4951_, v_start_4943_);
lean_dec_ref(v___x_4951_);
v___x_4953_ = l_Lean_instInhabitedModuleData_default;
v_mdata_4954_ = lean_array_get(v___x_4953_, v_moduleData_4949_, v_start_4943_);
lean_dec_ref(v_moduleData_4949_);
v___x_4955_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_act_4939_);
lean_inc_ref(v_env_4938_);
lean_inc_ref(v_cctx_4937_);
v___x_4956_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(v_cctx_4937_, v_env_4938_, v_act_4939_, v_d_4940_, v_cacheRef_4941_, v_tree_4942_, v_mname_4952_, v_mdata_4954_, v___x_4955_);
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
v___x_5327_ = lean_st_ref_set(v_a_5299_, v___x_5326_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__0(lean_object* v_toApplicative_5711_, lean_object* v_tasks_5712_, lean_object* v_t_5713_){
_start:
{
lean_object* v_toPure_5714_; lean_object* v___x_5715_; lean_object* v___x_5716_; 
v_toPure_5714_ = lean_ctor_get(v_toApplicative_5711_, 1);
lean_inc(v_toPure_5714_);
lean_dec_ref(v_toApplicative_5711_);
v___x_5715_ = lean_array_push(v_tasks_5712_, v_t_5713_);
v___x_5716_ = lean_apply_2(v_toPure_5714_, lean_box(0), v___x_5715_);
return v___x_5716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(lean_object* v_inst_5717_, lean_object* v_inst_5718_, lean_object* v_cctx_5719_, lean_object* v_env_5720_, lean_object* v_act_5721_, lean_object* v_constantsPerTask_5722_, lean_object* v_n_5723_, lean_object* v_ngen_5724_, lean_object* v_tasks_5725_, lean_object* v_start_5726_, lean_object* v_cnt_5727_, lean_object* v_idx_5728_){
_start:
{
lean_object* v___x_5729_; lean_object* v_moduleData_5730_; lean_object* v___x_5731_; uint8_t v___x_5732_; 
v___x_5729_ = l_Lean_Environment_header(v_env_5720_);
v_moduleData_5730_ = lean_ctor_get(v___x_5729_, 6);
lean_inc_ref(v_moduleData_5730_);
lean_dec_ref(v___x_5729_);
v___x_5731_ = lean_array_get_size(v_moduleData_5730_);
v___x_5732_ = lean_nat_dec_lt(v_idx_5728_, v___x_5731_);
if (v___x_5732_ == 0)
{
uint8_t v___x_5733_; 
lean_dec_ref(v_moduleData_5730_);
lean_dec(v_idx_5728_);
lean_dec(v_cnt_5727_);
lean_dec(v_constantsPerTask_5722_);
v___x_5733_ = lean_nat_dec_lt(v_start_5726_, v_n_5723_);
if (v___x_5733_ == 0)
{
lean_object* v_toApplicative_5734_; lean_object* v_toPure_5735_; lean_object* v___x_5736_; 
lean_dec(v_start_5726_);
lean_dec_ref(v_ngen_5724_);
lean_dec(v_n_5723_);
lean_dec_ref(v_act_5721_);
lean_dec_ref(v_env_5720_);
lean_dec_ref(v_cctx_5719_);
lean_dec(v_inst_5718_);
v_toApplicative_5734_ = lean_ctor_get(v_inst_5717_, 0);
lean_inc_ref(v_toApplicative_5734_);
lean_dec_ref(v_inst_5717_);
v_toPure_5735_ = lean_ctor_get(v_toApplicative_5734_, 1);
lean_inc(v_toPure_5735_);
lean_dec_ref(v_toApplicative_5734_);
v___x_5736_ = lean_apply_2(v_toPure_5735_, lean_box(0), v_tasks_5725_);
return v___x_5736_;
}
else
{
lean_object* v_namePrefix_5737_; lean_object* v_idx_5738_; lean_object* v___x_5740_; uint8_t v_isShared_5741_; uint8_t v_isSharedCheck_5755_; 
v_namePrefix_5737_ = lean_ctor_get(v_ngen_5724_, 0);
v_idx_5738_ = lean_ctor_get(v_ngen_5724_, 1);
v_isSharedCheck_5755_ = !lean_is_exclusive(v_ngen_5724_);
if (v_isSharedCheck_5755_ == 0)
{
v___x_5740_ = v_ngen_5724_;
v_isShared_5741_ = v_isSharedCheck_5755_;
goto v_resetjp_5739_;
}
else
{
lean_inc(v_idx_5738_);
lean_inc(v_namePrefix_5737_);
lean_dec(v_ngen_5724_);
v___x_5740_ = lean_box(0);
v_isShared_5741_ = v_isSharedCheck_5755_;
goto v_resetjp_5739_;
}
v_resetjp_5739_:
{
lean_object* v_toApplicative_5742_; lean_object* v_toBind_5743_; lean_object* v___f_5744_; lean_object* v___x_5745_; lean_object* v___x_5746_; lean_object* v___x_5748_; 
v_toApplicative_5742_ = lean_ctor_get(v_inst_5717_, 0);
lean_inc_ref(v_toApplicative_5742_);
v_toBind_5743_ = lean_ctor_get(v_inst_5717_, 1);
lean_inc(v_toBind_5743_);
lean_dec_ref(v_inst_5717_);
v___f_5744_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5744_, 0, v_toApplicative_5742_);
lean_closure_set(v___f_5744_, 1, v_tasks_5725_);
v___x_5745_ = l_Lean_Name_num___override(v_namePrefix_5737_, v_idx_5738_);
v___x_5746_ = lean_unsigned_to_nat(1u);
if (v_isShared_5741_ == 0)
{
lean_ctor_set(v___x_5740_, 1, v___x_5746_);
lean_ctor_set(v___x_5740_, 0, v___x_5745_);
v___x_5748_ = v___x_5740_;
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
lean_closure_set(v___x_5749_, 1, v_cctx_5719_);
lean_closure_set(v___x_5749_, 2, v___x_5748_);
lean_closure_set(v___x_5749_, 3, v_env_5720_);
lean_closure_set(v___x_5749_, 4, v_act_5721_);
lean_closure_set(v___x_5749_, 5, v_start_5726_);
lean_closure_set(v___x_5749_, 6, v_n_5723_);
v___x_5750_ = lean_unsigned_to_nat(0u);
v___x_5751_ = lean_alloc_closure((void*)(l_BaseIO_asTask___boxed), 4, 3);
lean_closure_set(v___x_5751_, 0, lean_box(0));
lean_closure_set(v___x_5751_, 1, v___x_5749_);
lean_closure_set(v___x_5751_, 2, v___x_5750_);
v___x_5752_ = lean_apply_2(v_inst_5718_, lean_box(0), v___x_5751_);
v___x_5753_ = lean_apply_4(v_toBind_5743_, lean_box(0), lean_box(0), v___x_5752_, v___f_5744_);
return v___x_5753_;
}
}
}
}
else
{
lean_object* v_mdata_5756_; lean_object* v_constants_5757_; lean_object* v___x_5758_; lean_object* v_cnt_5759_; uint8_t v___x_5760_; 
v_mdata_5756_ = lean_array_fget(v_moduleData_5730_, v_idx_5728_);
lean_dec_ref(v_moduleData_5730_);
v_constants_5757_ = lean_ctor_get(v_mdata_5756_, 2);
lean_inc_ref(v_constants_5757_);
lean_dec(v_mdata_5756_);
v___x_5758_ = lean_array_get_size(v_constants_5757_);
lean_dec_ref(v_constants_5757_);
v_cnt_5759_ = lean_nat_add(v_cnt_5727_, v___x_5758_);
lean_dec(v_cnt_5727_);
v___x_5760_ = lean_nat_dec_lt(v_constantsPerTask_5722_, v_cnt_5759_);
if (v___x_5760_ == 0)
{
lean_object* v___x_5761_; lean_object* v___x_5762_; 
v___x_5761_ = lean_unsigned_to_nat(1u);
v___x_5762_ = lean_nat_add(v_idx_5728_, v___x_5761_);
lean_dec(v_idx_5728_);
v_cnt_5727_ = v_cnt_5759_;
v_idx_5728_ = v___x_5762_;
goto _start;
}
else
{
lean_object* v_namePrefix_5764_; lean_object* v_idx_5765_; lean_object* v___x_5767_; uint8_t v_isShared_5768_; uint8_t v_isSharedCheck_5784_; 
lean_dec(v_cnt_5759_);
v_namePrefix_5764_ = lean_ctor_get(v_ngen_5724_, 0);
v_idx_5765_ = lean_ctor_get(v_ngen_5724_, 1);
v_isSharedCheck_5784_ = !lean_is_exclusive(v_ngen_5724_);
if (v_isSharedCheck_5784_ == 0)
{
v___x_5767_ = v_ngen_5724_;
v_isShared_5768_ = v_isSharedCheck_5784_;
goto v_resetjp_5766_;
}
else
{
lean_inc(v_idx_5765_);
lean_inc(v_namePrefix_5764_);
lean_dec(v_ngen_5724_);
v___x_5767_ = lean_box(0);
v_isShared_5768_ = v_isSharedCheck_5784_;
goto v_resetjp_5766_;
}
v_resetjp_5766_:
{
lean_object* v_toBind_5769_; lean_object* v___x_5770_; lean_object* v___x_5771_; lean_object* v___x_5773_; 
v_toBind_5769_ = lean_ctor_get(v_inst_5717_, 1);
lean_inc(v_toBind_5769_);
lean_inc(v_idx_5765_);
lean_inc(v_namePrefix_5764_);
v___x_5770_ = l_Lean_Name_num___override(v_namePrefix_5764_, v_idx_5765_);
v___x_5771_ = lean_unsigned_to_nat(1u);
if (v_isShared_5768_ == 0)
{
lean_ctor_set(v___x_5767_, 1, v___x_5771_);
lean_ctor_set(v___x_5767_, 0, v___x_5770_);
v___x_5773_ = v___x_5767_;
goto v_reusejp_5772_;
}
else
{
lean_object* v_reuseFailAlloc_5783_; 
v_reuseFailAlloc_5783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5783_, 0, v___x_5770_);
lean_ctor_set(v_reuseFailAlloc_5783_, 1, v___x_5771_);
v___x_5773_ = v_reuseFailAlloc_5783_;
goto v_reusejp_5772_;
}
v_reusejp_5772_:
{
lean_object* v___x_5774_; lean_object* v___x_5775_; lean_object* v___x_5776_; lean_object* v___f_5777_; lean_object* v___x_5778_; lean_object* v___x_5779_; lean_object* v___x_5780_; lean_object* v___x_5781_; lean_object* v___x_5782_; 
v___x_5774_ = lean_nat_add(v_idx_5765_, v___x_5771_);
lean_dec(v_idx_5765_);
v___x_5775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5775_, 0, v_namePrefix_5764_);
lean_ctor_set(v___x_5775_, 1, v___x_5774_);
v___x_5776_ = lean_nat_add(v_idx_5728_, v___x_5771_);
lean_dec(v_idx_5728_);
lean_inc(v___x_5776_);
lean_inc_ref(v_act_5721_);
lean_inc_ref(v_env_5720_);
lean_inc_ref(v_cctx_5719_);
lean_inc(v_inst_5718_);
v___f_5777_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__1), 11, 10);
lean_closure_set(v___f_5777_, 0, v_tasks_5725_);
lean_closure_set(v___f_5777_, 1, v_inst_5717_);
lean_closure_set(v___f_5777_, 2, v_inst_5718_);
lean_closure_set(v___f_5777_, 3, v_cctx_5719_);
lean_closure_set(v___f_5777_, 4, v_env_5720_);
lean_closure_set(v___f_5777_, 5, v_act_5721_);
lean_closure_set(v___f_5777_, 6, v_constantsPerTask_5722_);
lean_closure_set(v___f_5777_, 7, v_n_5723_);
lean_closure_set(v___f_5777_, 8, v___x_5775_);
lean_closure_set(v___f_5777_, 9, v___x_5776_);
v___x_5778_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_5778_, 0, lean_box(0));
lean_closure_set(v___x_5778_, 1, v_cctx_5719_);
lean_closure_set(v___x_5778_, 2, v___x_5773_);
lean_closure_set(v___x_5778_, 3, v_env_5720_);
lean_closure_set(v___x_5778_, 4, v_act_5721_);
lean_closure_set(v___x_5778_, 5, v_start_5726_);
lean_closure_set(v___x_5778_, 6, v___x_5776_);
v___x_5779_ = lean_unsigned_to_nat(0u);
v___x_5780_ = lean_alloc_closure((void*)(l_BaseIO_asTask___boxed), 4, 3);
lean_closure_set(v___x_5780_, 0, lean_box(0));
lean_closure_set(v___x_5780_, 1, v___x_5778_);
lean_closure_set(v___x_5780_, 2, v___x_5779_);
v___x_5781_ = lean_apply_2(v_inst_5718_, lean_box(0), v___x_5780_);
v___x_5782_ = lean_apply_4(v_toBind_5769_, lean_box(0), lean_box(0), v___x_5781_, v___f_5777_);
return v___x_5782_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__1(lean_object* v_tasks_5785_, lean_object* v_inst_5786_, lean_object* v_inst_5787_, lean_object* v_cctx_5788_, lean_object* v_env_5789_, lean_object* v_act_5790_, lean_object* v_constantsPerTask_5791_, lean_object* v_n_5792_, lean_object* v___x_5793_, lean_object* v___x_5794_, lean_object* v_t_5795_){
_start:
{
lean_object* v___x_5796_; lean_object* v___x_5797_; lean_object* v___x_5798_; 
v___x_5796_ = lean_array_push(v_tasks_5785_, v_t_5795_);
v___x_5797_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_5794_);
v___x_5798_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(v_inst_5786_, v_inst_5787_, v_cctx_5788_, v_env_5789_, v_act_5790_, v_constantsPerTask_5791_, v_n_5792_, v___x_5793_, v___x_5796_, v___x_5794_, v___x_5797_, v___x_5794_);
return v___x_5798_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go(lean_object* v_m_5799_, lean_object* v_00_u03b1_5800_, lean_object* v_inst_5801_, lean_object* v_inst_5802_, lean_object* v_cctx_5803_, lean_object* v_env_5804_, lean_object* v_act_5805_, lean_object* v_constantsPerTask_5806_, lean_object* v_n_5807_, lean_object* v_ngen_5808_, lean_object* v_tasks_5809_, lean_object* v_start_5810_, lean_object* v_cnt_5811_, lean_object* v_idx_5812_){
_start:
{
lean_object* v___x_5813_; 
v___x_5813_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(v_inst_5801_, v_inst_5802_, v_cctx_5803_, v_env_5804_, v_act_5805_, v_constantsPerTask_5806_, v_n_5807_, v_ngen_5808_, v_tasks_5809_, v_start_5810_, v_cnt_5811_, v_idx_5812_);
return v___x_5813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_getChildNgen_match__1_splitter___redArg(lean_object* v_x_5814_, lean_object* v_h__1_5815_){
_start:
{
lean_object* v_fst_5816_; lean_object* v_snd_5817_; lean_object* v___x_5818_; 
v_fst_5816_ = lean_ctor_get(v_x_5814_, 0);
lean_inc(v_fst_5816_);
v_snd_5817_ = lean_ctor_get(v_x_5814_, 1);
lean_inc(v_snd_5817_);
lean_dec_ref(v_x_5814_);
v___x_5818_ = lean_apply_2(v_h__1_5815_, v_fst_5816_, v_snd_5817_);
return v___x_5818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_getChildNgen_match__1_splitter(lean_object* v_motive_5819_, lean_object* v_x_5820_, lean_object* v_h__1_5821_){
_start:
{
lean_object* v_fst_5822_; lean_object* v_snd_5823_; lean_object* v___x_5824_; 
v_fst_5822_ = lean_ctor_get(v_x_5820_, 0);
lean_inc(v_fst_5822_);
v_snd_5823_ = lean_ctor_get(v_x_5820_, 1);
lean_inc(v_snd_5823_);
lean_dec_ref(v_x_5820_);
v___x_5824_ = lean_apply_2(v_h__1_5821_, v_fst_5822_, v_snd_5823_);
return v___x_5824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__0(lean_object* v_inst_5825_, lean_object* v_inst_5826_, lean_object* v_inst_5827_, lean_object* v_inst_5828_, lean_object* v_x_5829_, lean_object* v___y_5830_){
_start:
{
lean_object* v___x_5831_; 
v___x_5831_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg(v_inst_5825_, v_inst_5826_, v_inst_5827_, v_inst_5828_, v___y_5830_);
return v___x_5831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__1(lean_object* v_r_5832_, lean_object* v_toPure_5833_, lean_object* v_____r_5834_){
_start:
{
lean_object* v_tree_5835_; lean_object* v___x_5836_; lean_object* v___x_5837_; 
v_tree_5835_ = lean_ctor_get(v_r_5832_, 0);
lean_inc_ref(v_tree_5835_);
lean_dec_ref(v_r_5832_);
v___x_5836_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_tree_5835_);
v___x_5837_ = lean_apply_2(v_toPure_5833_, lean_box(0), v___x_5836_);
return v___x_5837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__2(lean_object* v___x_5838_, lean_object* v___x_5839_, lean_object* v_toPure_5840_, lean_object* v_toBind_5841_, lean_object* v_inst_5842_, lean_object* v___f_5843_, lean_object* v_tasks_5844_){
_start:
{
lean_object* v___x_5845_; lean_object* v___x_5846_; lean_object* v___x_5847_; lean_object* v___x_5848_; lean_object* v___x_5849_; lean_object* v_r_5850_; lean_object* v_errors_5851_; lean_object* v___f_5852_; lean_object* v___x_5853_; lean_object* v___x_5854_; uint8_t v___x_5855_; 
v___x_5845_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1);
lean_inc(v___x_5838_);
v___x_5846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5846_, 0, v___x_5838_);
lean_ctor_set(v___x_5846_, 1, v___x_5845_);
v___x_5847_ = lean_mk_empty_array_with_capacity(v___x_5838_);
lean_inc_ref(v___x_5847_);
v___x_5848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5848_, 0, v___x_5846_);
lean_ctor_set(v___x_5848_, 1, v___x_5847_);
v___x_5849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5849_, 0, v___x_5848_);
lean_ctor_set(v___x_5849_, 1, v___x_5847_);
v_r_5850_ = l_Lean_Meta_LazyDiscrTree_combineGet___redArg(v___x_5839_, v___x_5849_, v_tasks_5844_);
v_errors_5851_ = lean_ctor_get(v_r_5850_, 1);
lean_inc_ref(v_errors_5851_);
lean_inc(v_toPure_5840_);
v___f_5852_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__1), 3, 2);
lean_closure_set(v___f_5852_, 0, v_r_5850_);
lean_closure_set(v___f_5852_, 1, v_toPure_5840_);
v___x_5853_ = lean_array_get_size(v_errors_5851_);
v___x_5854_ = lean_box(0);
v___x_5855_ = lean_nat_dec_lt(v___x_5838_, v___x_5853_);
lean_dec(v___x_5838_);
if (v___x_5855_ == 0)
{
lean_object* v___x_5856_; lean_object* v___x_5857_; 
lean_dec_ref(v_errors_5851_);
lean_dec(v___f_5843_);
lean_dec_ref(v_inst_5842_);
v___x_5856_ = lean_apply_2(v_toPure_5840_, lean_box(0), v___x_5854_);
v___x_5857_ = lean_apply_4(v_toBind_5841_, lean_box(0), lean_box(0), v___x_5856_, v___f_5852_);
return v___x_5857_;
}
else
{
uint8_t v___x_5858_; 
v___x_5858_ = lean_nat_dec_le(v___x_5853_, v___x_5853_);
if (v___x_5858_ == 0)
{
if (v___x_5855_ == 0)
{
lean_object* v___x_5859_; lean_object* v___x_5860_; 
lean_dec_ref(v_errors_5851_);
lean_dec(v___f_5843_);
lean_dec_ref(v_inst_5842_);
v___x_5859_ = lean_apply_2(v_toPure_5840_, lean_box(0), v___x_5854_);
v___x_5860_ = lean_apply_4(v_toBind_5841_, lean_box(0), lean_box(0), v___x_5859_, v___f_5852_);
return v___x_5860_;
}
else
{
size_t v___x_5861_; size_t v___x_5862_; lean_object* v___x_5863_; lean_object* v___x_5864_; 
lean_dec(v_toPure_5840_);
v___x_5861_ = ((size_t)0ULL);
v___x_5862_ = lean_usize_of_nat(v___x_5853_);
v___x_5863_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_5842_, v___f_5843_, v_errors_5851_, v___x_5861_, v___x_5862_, v___x_5854_);
v___x_5864_ = lean_apply_4(v_toBind_5841_, lean_box(0), lean_box(0), v___x_5863_, v___f_5852_);
return v___x_5864_;
}
}
else
{
size_t v___x_5865_; size_t v___x_5866_; lean_object* v___x_5867_; lean_object* v___x_5868_; 
lean_dec(v_toPure_5840_);
v___x_5865_ = ((size_t)0ULL);
v___x_5866_ = lean_usize_of_nat(v___x_5853_);
v___x_5867_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_5842_, v___f_5843_, v_errors_5851_, v___x_5865_, v___x_5866_, v___x_5854_);
v___x_5868_ = lean_apply_4(v_toBind_5841_, lean_box(0), lean_box(0), v___x_5867_, v___f_5852_);
return v___x_5868_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg(lean_object* v_inst_5871_, lean_object* v_inst_5872_, lean_object* v_inst_5873_, lean_object* v_inst_5874_, lean_object* v_inst_5875_, lean_object* v_cctx_5876_, lean_object* v_ngen_5877_, lean_object* v_env_5878_, lean_object* v_act_5879_, lean_object* v_constantsPerTask_5880_){
_start:
{
lean_object* v___x_5881_; lean_object* v_moduleData_5882_; lean_object* v_toApplicative_5883_; lean_object* v_toBind_5884_; lean_object* v_n_5885_; lean_object* v___x_5886_; lean_object* v___x_5887_; lean_object* v___x_5888_; lean_object* v_toPure_5889_; lean_object* v___f_5890_; lean_object* v___x_5891_; lean_object* v___f_5892_; lean_object* v___x_5893_; 
v___x_5881_ = l_Lean_Environment_header(v_env_5878_);
v_moduleData_5882_ = lean_ctor_get(v___x_5881_, 6);
lean_inc_ref(v_moduleData_5882_);
lean_dec_ref(v___x_5881_);
v_toApplicative_5883_ = lean_ctor_get(v_inst_5871_, 0);
v_toBind_5884_ = lean_ctor_get(v_inst_5871_, 1);
lean_inc_n(v_toBind_5884_, 2);
v_n_5885_ = lean_array_get_size(v_moduleData_5882_);
lean_dec_ref(v_moduleData_5882_);
v___x_5886_ = lean_unsigned_to_nat(0u);
v___x_5887_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
lean_inc_ref_n(v_inst_5871_, 2);
v___x_5888_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(v_inst_5871_, v_inst_5875_, v_cctx_5876_, v_env_5878_, v_act_5879_, v_constantsPerTask_5880_, v_n_5885_, v_ngen_5877_, v___x_5887_, v___x_5886_, v___x_5886_, v___x_5886_);
v_toPure_5889_ = lean_ctor_get(v_toApplicative_5883_, 1);
lean_inc(v_toPure_5889_);
v___f_5890_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__0), 6, 4);
lean_closure_set(v___f_5890_, 0, v_inst_5871_);
lean_closure_set(v___f_5890_, 1, v_inst_5872_);
lean_closure_set(v___f_5890_, 2, v_inst_5873_);
lean_closure_set(v___f_5890_, 3, v_inst_5874_);
v___x_5891_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___closed__0));
v___f_5892_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__2), 7, 6);
lean_closure_set(v___f_5892_, 0, v___x_5886_);
lean_closure_set(v___f_5892_, 1, v___x_5891_);
lean_closure_set(v___f_5892_, 2, v_toPure_5889_);
lean_closure_set(v___f_5892_, 3, v_toBind_5884_);
lean_closure_set(v___f_5892_, 4, v_inst_5871_);
lean_closure_set(v___f_5892_, 5, v___f_5890_);
v___x_5893_ = lean_apply_4(v_toBind_5884_, lean_box(0), lean_box(0), v___x_5888_, v___f_5892_);
return v___x_5893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree(lean_object* v_m_5894_, lean_object* v_00_u03b1_5895_, lean_object* v_inst_5896_, lean_object* v_inst_5897_, lean_object* v_inst_5898_, lean_object* v_inst_5899_, lean_object* v_inst_5900_, lean_object* v_cctx_5901_, lean_object* v_ngen_5902_, lean_object* v_env_5903_, lean_object* v_act_5904_, lean_object* v_constantsPerTask_5905_){
_start:
{
lean_object* v___x_5906_; 
v___x_5906_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg(v_inst_5896_, v_inst_5897_, v_inst_5898_, v_inst_5899_, v_inst_5900_, v_cctx_5901_, v_ngen_5902_, v_env_5903_, v_act_5904_, v_constantsPerTask_5905_);
return v___x_5906_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0(void){
_start:
{
lean_object* v___x_5907_; lean_object* v___x_5908_; lean_object* v___x_5909_; 
v___x_5907_ = lean_box(0);
v___x_5908_ = lean_unsigned_to_nat(16u);
v___x_5909_ = lean_mk_array(v___x_5908_, v___x_5907_);
return v___x_5909_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1(void){
_start:
{
lean_object* v___x_5910_; lean_object* v___x_5911_; lean_object* v___x_5912_; 
v___x_5910_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0, &l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0);
v___x_5911_ = lean_unsigned_to_nat(0u);
v___x_5912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5912_, 0, v___x_5911_);
lean_ctor_set(v___x_5912_, 1, v___x_5910_);
return v___x_5912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createTreeCtx(lean_object* v_ctx_5913_){
_start:
{
lean_object* v_fileName_5914_; lean_object* v_fileMap_5915_; lean_object* v_options_5916_; lean_object* v_maxRecDepth_5917_; lean_object* v_ref_5918_; lean_object* v___x_5920_; uint8_t v_isShared_5921_; uint8_t v_isSharedCheck_5933_; 
v_fileName_5914_ = lean_ctor_get(v_ctx_5913_, 0);
v_fileMap_5915_ = lean_ctor_get(v_ctx_5913_, 1);
v_options_5916_ = lean_ctor_get(v_ctx_5913_, 2);
v_maxRecDepth_5917_ = lean_ctor_get(v_ctx_5913_, 4);
v_ref_5918_ = lean_ctor_get(v_ctx_5913_, 5);
v_isSharedCheck_5933_ = !lean_is_exclusive(v_ctx_5913_);
if (v_isSharedCheck_5933_ == 0)
{
lean_object* v_unused_5934_; lean_object* v_unused_5935_; lean_object* v_unused_5936_; lean_object* v_unused_5937_; lean_object* v_unused_5938_; lean_object* v_unused_5939_; lean_object* v_unused_5940_; lean_object* v_unused_5941_; lean_object* v_unused_5942_; 
v_unused_5934_ = lean_ctor_get(v_ctx_5913_, 13);
lean_dec(v_unused_5934_);
v_unused_5935_ = lean_ctor_get(v_ctx_5913_, 12);
lean_dec(v_unused_5935_);
v_unused_5936_ = lean_ctor_get(v_ctx_5913_, 11);
lean_dec(v_unused_5936_);
v_unused_5937_ = lean_ctor_get(v_ctx_5913_, 10);
lean_dec(v_unused_5937_);
v_unused_5938_ = lean_ctor_get(v_ctx_5913_, 9);
lean_dec(v_unused_5938_);
v_unused_5939_ = lean_ctor_get(v_ctx_5913_, 8);
lean_dec(v_unused_5939_);
v_unused_5940_ = lean_ctor_get(v_ctx_5913_, 7);
lean_dec(v_unused_5940_);
v_unused_5941_ = lean_ctor_get(v_ctx_5913_, 6);
lean_dec(v_unused_5941_);
v_unused_5942_ = lean_ctor_get(v_ctx_5913_, 3);
lean_dec(v_unused_5942_);
v___x_5920_ = v_ctx_5913_;
v_isShared_5921_ = v_isSharedCheck_5933_;
goto v_resetjp_5919_;
}
else
{
lean_inc(v_ref_5918_);
lean_inc(v_maxRecDepth_5917_);
lean_inc(v_options_5916_);
lean_inc(v_fileMap_5915_);
lean_inc(v_fileName_5914_);
lean_dec(v_ctx_5913_);
v___x_5920_ = lean_box(0);
v_isShared_5921_ = v_isSharedCheck_5933_;
goto v_resetjp_5919_;
}
v_resetjp_5919_:
{
lean_object* v___x_5922_; lean_object* v___x_5923_; lean_object* v___x_5924_; lean_object* v___x_5925_; uint8_t v___x_5926_; lean_object* v___x_5927_; uint8_t v___x_5928_; lean_object* v___x_5929_; lean_object* v___x_5931_; 
v___x_5922_ = lean_unsigned_to_nat(0u);
v___x_5923_ = lean_box(0);
v___x_5924_ = lean_box(0);
v___x_5925_ = l_Lean_firstFrontendMacroScope;
v___x_5926_ = l_Lean_getDiag(v_options_5916_);
v___x_5927_ = lean_box(0);
v___x_5928_ = 0;
v___x_5929_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1, &l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1);
if (v_isShared_5921_ == 0)
{
lean_ctor_set(v___x_5920_, 13, v___x_5929_);
lean_ctor_set(v___x_5920_, 12, v___x_5927_);
lean_ctor_set(v___x_5920_, 11, v___x_5925_);
lean_ctor_set(v___x_5920_, 10, v___x_5923_);
lean_ctor_set(v___x_5920_, 9, v___x_5922_);
lean_ctor_set(v___x_5920_, 8, v___x_5922_);
lean_ctor_set(v___x_5920_, 7, v___x_5924_);
lean_ctor_set(v___x_5920_, 6, v___x_5923_);
lean_ctor_set(v___x_5920_, 3, v___x_5922_);
v___x_5931_ = v___x_5920_;
goto v_reusejp_5930_;
}
else
{
lean_object* v_reuseFailAlloc_5932_; 
v_reuseFailAlloc_5932_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_5932_, 0, v_fileName_5914_);
lean_ctor_set(v_reuseFailAlloc_5932_, 1, v_fileMap_5915_);
lean_ctor_set(v_reuseFailAlloc_5932_, 2, v_options_5916_);
lean_ctor_set(v_reuseFailAlloc_5932_, 3, v___x_5922_);
lean_ctor_set(v_reuseFailAlloc_5932_, 4, v_maxRecDepth_5917_);
lean_ctor_set(v_reuseFailAlloc_5932_, 5, v_ref_5918_);
lean_ctor_set(v_reuseFailAlloc_5932_, 6, v___x_5923_);
lean_ctor_set(v_reuseFailAlloc_5932_, 7, v___x_5924_);
lean_ctor_set(v_reuseFailAlloc_5932_, 8, v___x_5922_);
lean_ctor_set(v_reuseFailAlloc_5932_, 9, v___x_5922_);
lean_ctor_set(v_reuseFailAlloc_5932_, 10, v___x_5923_);
lean_ctor_set(v_reuseFailAlloc_5932_, 11, v___x_5925_);
lean_ctor_set(v_reuseFailAlloc_5932_, 12, v___x_5927_);
lean_ctor_set(v_reuseFailAlloc_5932_, 13, v___x_5929_);
v___x_5931_ = v_reuseFailAlloc_5932_;
goto v_reusejp_5930_;
}
v_reusejp_5930_:
{
lean_ctor_set_uint8(v___x_5931_, sizeof(void*)*14, v___x_5926_);
lean_ctor_set_uint8(v___x_5931_, sizeof(void*)*14 + 1, v___x_5928_);
return v___x_5931_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(lean_object* v_category_5943_, lean_object* v_opts_5944_, lean_object* v_act_5945_, lean_object* v_decl_5946_, lean_object* v___y_5947_, lean_object* v___y_5948_, lean_object* v___y_5949_, lean_object* v___y_5950_){
_start:
{
lean_object* v___x_5952_; lean_object* v___x_5953_; 
lean_inc(v___y_5950_);
lean_inc_ref(v___y_5949_);
lean_inc(v___y_5948_);
lean_inc_ref(v___y_5947_);
v___x_5952_ = lean_apply_4(v_act_5945_, v___y_5947_, v___y_5948_, v___y_5949_, v___y_5950_);
v___x_5953_ = l_Lean_profileitIOUnsafe___redArg(v_category_5943_, v_opts_5944_, v___x_5952_, v_decl_5946_);
return v___x_5953_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg___boxed(lean_object* v_category_5954_, lean_object* v_opts_5955_, lean_object* v_act_5956_, lean_object* v_decl_5957_, lean_object* v___y_5958_, lean_object* v___y_5959_, lean_object* v___y_5960_, lean_object* v___y_5961_, lean_object* v___y_5962_){
_start:
{
lean_object* v_res_5963_; 
v_res_5963_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v_category_5954_, v_opts_5955_, v_act_5956_, v_decl_5957_, v___y_5958_, v___y_5959_, v___y_5960_, v___y_5961_);
lean_dec(v___y_5961_);
lean_dec_ref(v___y_5960_);
lean_dec(v___y_5959_);
lean_dec_ref(v___y_5958_);
lean_dec_ref(v_opts_5955_);
lean_dec_ref(v_category_5954_);
return v_res_5963_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1(lean_object* v_00_u03b1_5964_, lean_object* v_category_5965_, lean_object* v_opts_5966_, lean_object* v_act_5967_, lean_object* v_decl_5968_, lean_object* v___y_5969_, lean_object* v___y_5970_, lean_object* v___y_5971_, lean_object* v___y_5972_){
_start:
{
lean_object* v___x_5974_; 
v___x_5974_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v_category_5965_, v_opts_5966_, v_act_5967_, v_decl_5968_, v___y_5969_, v___y_5970_, v___y_5971_, v___y_5972_);
return v___x_5974_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___boxed(lean_object* v_00_u03b1_5975_, lean_object* v_category_5976_, lean_object* v_opts_5977_, lean_object* v_act_5978_, lean_object* v_decl_5979_, lean_object* v___y_5980_, lean_object* v___y_5981_, lean_object* v___y_5982_, lean_object* v___y_5983_, lean_object* v___y_5984_){
_start:
{
lean_object* v_res_5985_; 
v_res_5985_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1(v_00_u03b1_5975_, v_category_5976_, v_opts_5977_, v_act_5978_, v_decl_5979_, v___y_5980_, v___y_5981_, v___y_5982_, v___y_5983_);
lean_dec(v___y_5983_);
lean_dec_ref(v___y_5982_);
lean_dec(v___y_5981_);
lean_dec_ref(v___y_5980_);
lean_dec_ref(v_opts_5977_);
lean_dec_ref(v_category_5976_);
return v_res_5985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(lean_object* v_cctx_5986_, lean_object* v_env_5987_, lean_object* v_act_5988_, lean_object* v_constantsPerTask_5989_, lean_object* v_n_5990_, lean_object* v_ngen_5991_, lean_object* v_tasks_5992_, lean_object* v_start_5993_, lean_object* v_cnt_5994_, lean_object* v_idx_5995_){
_start:
{
lean_object* v___x_5997_; lean_object* v_moduleData_5998_; lean_object* v___x_5999_; uint8_t v___x_6000_; 
v___x_5997_ = l_Lean_Environment_header(v_env_5987_);
v_moduleData_5998_ = lean_ctor_get(v___x_5997_, 6);
lean_inc_ref(v_moduleData_5998_);
lean_dec_ref(v___x_5997_);
v___x_5999_ = lean_array_get_size(v_moduleData_5998_);
v___x_6000_ = lean_nat_dec_lt(v_idx_5995_, v___x_5999_);
if (v___x_6000_ == 0)
{
uint8_t v___x_6001_; 
lean_dec_ref(v_moduleData_5998_);
lean_dec(v_idx_5995_);
lean_dec(v_cnt_5994_);
v___x_6001_ = lean_nat_dec_lt(v_start_5993_, v_n_5990_);
if (v___x_6001_ == 0)
{
lean_object* v___x_6002_; 
lean_dec(v_start_5993_);
lean_dec_ref(v_ngen_5991_);
lean_dec(v_n_5990_);
lean_dec_ref(v_act_5988_);
lean_dec_ref(v_env_5987_);
lean_dec_ref(v_cctx_5986_);
v___x_6002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6002_, 0, v_tasks_5992_);
return v___x_6002_;
}
else
{
lean_object* v_namePrefix_6003_; lean_object* v_idx_6004_; lean_object* v___x_6006_; uint8_t v_isShared_6007_; uint8_t v_isSharedCheck_6018_; 
v_namePrefix_6003_ = lean_ctor_get(v_ngen_5991_, 0);
v_idx_6004_ = lean_ctor_get(v_ngen_5991_, 1);
v_isSharedCheck_6018_ = !lean_is_exclusive(v_ngen_5991_);
if (v_isSharedCheck_6018_ == 0)
{
v___x_6006_ = v_ngen_5991_;
v_isShared_6007_ = v_isSharedCheck_6018_;
goto v_resetjp_6005_;
}
else
{
lean_inc(v_idx_6004_);
lean_inc(v_namePrefix_6003_);
lean_dec(v_ngen_5991_);
v___x_6006_ = lean_box(0);
v_isShared_6007_ = v_isSharedCheck_6018_;
goto v_resetjp_6005_;
}
v_resetjp_6005_:
{
lean_object* v___x_6008_; lean_object* v___x_6009_; lean_object* v___x_6011_; 
v___x_6008_ = l_Lean_Name_num___override(v_namePrefix_6003_, v_idx_6004_);
v___x_6009_ = lean_unsigned_to_nat(1u);
if (v_isShared_6007_ == 0)
{
lean_ctor_set(v___x_6006_, 1, v___x_6009_);
lean_ctor_set(v___x_6006_, 0, v___x_6008_);
v___x_6011_ = v___x_6006_;
goto v_reusejp_6010_;
}
else
{
lean_object* v_reuseFailAlloc_6017_; 
v_reuseFailAlloc_6017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6017_, 0, v___x_6008_);
lean_ctor_set(v_reuseFailAlloc_6017_, 1, v___x_6009_);
v___x_6011_ = v_reuseFailAlloc_6017_;
goto v_reusejp_6010_;
}
v_reusejp_6010_:
{
lean_object* v___x_6012_; lean_object* v___x_6013_; lean_object* v___x_6014_; lean_object* v___x_6015_; lean_object* v___x_6016_; 
v___x_6012_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_6012_, 0, lean_box(0));
lean_closure_set(v___x_6012_, 1, v_cctx_5986_);
lean_closure_set(v___x_6012_, 2, v___x_6011_);
lean_closure_set(v___x_6012_, 3, v_env_5987_);
lean_closure_set(v___x_6012_, 4, v_act_5988_);
lean_closure_set(v___x_6012_, 5, v_start_5993_);
lean_closure_set(v___x_6012_, 6, v_n_5990_);
v___x_6013_ = lean_unsigned_to_nat(0u);
v___x_6014_ = lean_io_as_task(v___x_6012_, v___x_6013_);
v___x_6015_ = lean_array_push(v_tasks_5992_, v___x_6014_);
v___x_6016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6016_, 0, v___x_6015_);
return v___x_6016_;
}
}
}
}
else
{
lean_object* v_mdata_6019_; lean_object* v_constants_6020_; lean_object* v___x_6021_; lean_object* v_cnt_6022_; uint8_t v___x_6023_; 
v_mdata_6019_ = lean_array_fget(v_moduleData_5998_, v_idx_5995_);
lean_dec_ref(v_moduleData_5998_);
v_constants_6020_ = lean_ctor_get(v_mdata_6019_, 2);
lean_inc_ref(v_constants_6020_);
lean_dec(v_mdata_6019_);
v___x_6021_ = lean_array_get_size(v_constants_6020_);
lean_dec_ref(v_constants_6020_);
v_cnt_6022_ = lean_nat_add(v_cnt_5994_, v___x_6021_);
lean_dec(v_cnt_5994_);
v___x_6023_ = lean_nat_dec_lt(v_constantsPerTask_5989_, v_cnt_6022_);
if (v___x_6023_ == 0)
{
lean_object* v___x_6024_; lean_object* v___x_6025_; 
v___x_6024_ = lean_unsigned_to_nat(1u);
v___x_6025_ = lean_nat_add(v_idx_5995_, v___x_6024_);
lean_dec(v_idx_5995_);
v_cnt_5994_ = v_cnt_6022_;
v_idx_5995_ = v___x_6025_;
goto _start;
}
else
{
lean_object* v_namePrefix_6027_; lean_object* v_idx_6028_; lean_object* v___x_6030_; uint8_t v_isShared_6031_; uint8_t v_isSharedCheck_6045_; 
lean_dec(v_cnt_6022_);
v_namePrefix_6027_ = lean_ctor_get(v_ngen_5991_, 0);
v_idx_6028_ = lean_ctor_get(v_ngen_5991_, 1);
v_isSharedCheck_6045_ = !lean_is_exclusive(v_ngen_5991_);
if (v_isSharedCheck_6045_ == 0)
{
v___x_6030_ = v_ngen_5991_;
v_isShared_6031_ = v_isSharedCheck_6045_;
goto v_resetjp_6029_;
}
else
{
lean_inc(v_idx_6028_);
lean_inc(v_namePrefix_6027_);
lean_dec(v_ngen_5991_);
v___x_6030_ = lean_box(0);
v_isShared_6031_ = v_isSharedCheck_6045_;
goto v_resetjp_6029_;
}
v_resetjp_6029_:
{
lean_object* v___x_6032_; lean_object* v___x_6033_; lean_object* v___x_6035_; 
lean_inc(v_idx_6028_);
lean_inc(v_namePrefix_6027_);
v___x_6032_ = l_Lean_Name_num___override(v_namePrefix_6027_, v_idx_6028_);
v___x_6033_ = lean_unsigned_to_nat(1u);
if (v_isShared_6031_ == 0)
{
lean_ctor_set(v___x_6030_, 1, v___x_6033_);
lean_ctor_set(v___x_6030_, 0, v___x_6032_);
v___x_6035_ = v___x_6030_;
goto v_reusejp_6034_;
}
else
{
lean_object* v_reuseFailAlloc_6044_; 
v_reuseFailAlloc_6044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6044_, 0, v___x_6032_);
lean_ctor_set(v_reuseFailAlloc_6044_, 1, v___x_6033_);
v___x_6035_ = v_reuseFailAlloc_6044_;
goto v_reusejp_6034_;
}
v_reusejp_6034_:
{
lean_object* v___x_6036_; lean_object* v___x_6037_; lean_object* v___x_6038_; lean_object* v___x_6039_; lean_object* v___x_6040_; lean_object* v___x_6041_; lean_object* v___x_6042_; 
v___x_6036_ = lean_nat_add(v_idx_5995_, v___x_6033_);
lean_dec(v_idx_5995_);
lean_inc_n(v___x_6036_, 2);
lean_inc_ref(v_act_5988_);
lean_inc_ref(v_env_5987_);
lean_inc_ref(v_cctx_5986_);
v___x_6037_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_6037_, 0, lean_box(0));
lean_closure_set(v___x_6037_, 1, v_cctx_5986_);
lean_closure_set(v___x_6037_, 2, v___x_6035_);
lean_closure_set(v___x_6037_, 3, v_env_5987_);
lean_closure_set(v___x_6037_, 4, v_act_5988_);
lean_closure_set(v___x_6037_, 5, v_start_5993_);
lean_closure_set(v___x_6037_, 6, v___x_6036_);
v___x_6038_ = lean_unsigned_to_nat(0u);
v___x_6039_ = lean_io_as_task(v___x_6037_, v___x_6038_);
v___x_6040_ = lean_nat_add(v_idx_6028_, v___x_6033_);
lean_dec(v_idx_6028_);
v___x_6041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6041_, 0, v_namePrefix_6027_);
lean_ctor_set(v___x_6041_, 1, v___x_6040_);
v___x_6042_ = lean_array_push(v_tasks_5992_, v___x_6039_);
v_ngen_5991_ = v___x_6041_;
v_tasks_5992_ = v___x_6042_;
v_start_5993_ = v___x_6036_;
v_cnt_5994_ = v___x_6038_;
v_idx_5995_ = v___x_6036_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg___boxed(lean_object* v_cctx_6046_, lean_object* v_env_6047_, lean_object* v_act_6048_, lean_object* v_constantsPerTask_6049_, lean_object* v_n_6050_, lean_object* v_ngen_6051_, lean_object* v_tasks_6052_, lean_object* v_start_6053_, lean_object* v_cnt_6054_, lean_object* v_idx_6055_, lean_object* v___y_6056_){
_start:
{
lean_object* v_res_6057_; 
v_res_6057_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(v_cctx_6046_, v_env_6047_, v_act_6048_, v_constantsPerTask_6049_, v_n_6050_, v_ngen_6051_, v_tasks_6052_, v_start_6053_, v_cnt_6054_, v_idx_6055_);
lean_dec(v_constantsPerTask_6049_);
return v_res_6057_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0(uint8_t v___y_6066_, uint8_t v_suppressElabErrors_6067_, lean_object* v_x_6068_){
_start:
{
if (lean_obj_tag(v_x_6068_) == 1)
{
lean_object* v_pre_6069_; 
v_pre_6069_ = lean_ctor_get(v_x_6068_, 0);
switch(lean_obj_tag(v_pre_6069_))
{
case 1:
{
lean_object* v_pre_6070_; 
v_pre_6070_ = lean_ctor_get(v_pre_6069_, 0);
switch(lean_obj_tag(v_pre_6070_))
{
case 0:
{
lean_object* v_str_6071_; lean_object* v_str_6072_; lean_object* v___x_6073_; uint8_t v___x_6074_; 
v_str_6071_ = lean_ctor_get(v_x_6068_, 1);
v_str_6072_ = lean_ctor_get(v_pre_6069_, 1);
v___x_6073_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__0));
v___x_6074_ = lean_string_dec_eq(v_str_6072_, v___x_6073_);
if (v___x_6074_ == 0)
{
lean_object* v___x_6075_; uint8_t v___x_6076_; 
v___x_6075_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__1));
v___x_6076_ = lean_string_dec_eq(v_str_6072_, v___x_6075_);
if (v___x_6076_ == 0)
{
return v___y_6066_;
}
else
{
lean_object* v___x_6077_; uint8_t v___x_6078_; 
v___x_6077_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__2));
v___x_6078_ = lean_string_dec_eq(v_str_6071_, v___x_6077_);
if (v___x_6078_ == 0)
{
return v___y_6066_;
}
else
{
return v_suppressElabErrors_6067_;
}
}
}
else
{
lean_object* v___x_6079_; uint8_t v___x_6080_; 
v___x_6079_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__3));
v___x_6080_ = lean_string_dec_eq(v_str_6071_, v___x_6079_);
if (v___x_6080_ == 0)
{
return v___y_6066_;
}
else
{
return v_suppressElabErrors_6067_;
}
}
}
case 1:
{
lean_object* v_pre_6081_; 
v_pre_6081_ = lean_ctor_get(v_pre_6070_, 0);
if (lean_obj_tag(v_pre_6081_) == 0)
{
lean_object* v_str_6082_; lean_object* v_str_6083_; lean_object* v_str_6084_; lean_object* v___x_6085_; uint8_t v___x_6086_; 
v_str_6082_ = lean_ctor_get(v_x_6068_, 1);
v_str_6083_ = lean_ctor_get(v_pre_6069_, 1);
v_str_6084_ = lean_ctor_get(v_pre_6070_, 1);
v___x_6085_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__4));
v___x_6086_ = lean_string_dec_eq(v_str_6084_, v___x_6085_);
if (v___x_6086_ == 0)
{
return v___y_6066_;
}
else
{
lean_object* v___x_6087_; uint8_t v___x_6088_; 
v___x_6087_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__5));
v___x_6088_ = lean_string_dec_eq(v_str_6083_, v___x_6087_);
if (v___x_6088_ == 0)
{
return v___y_6066_;
}
else
{
lean_object* v___x_6089_; uint8_t v___x_6090_; 
v___x_6089_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__6));
v___x_6090_ = lean_string_dec_eq(v_str_6082_, v___x_6089_);
if (v___x_6090_ == 0)
{
return v___y_6066_;
}
else
{
return v_suppressElabErrors_6067_;
}
}
}
}
else
{
return v___y_6066_;
}
}
default: 
{
return v___y_6066_;
}
}
}
case 0:
{
lean_object* v_str_6091_; lean_object* v___x_6092_; uint8_t v___x_6093_; 
v_str_6091_ = lean_ctor_get(v_x_6068_, 1);
v___x_6092_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__7));
v___x_6093_ = lean_string_dec_eq(v_str_6091_, v___x_6092_);
if (v___x_6093_ == 0)
{
return v___y_6066_;
}
else
{
return v_suppressElabErrors_6067_;
}
}
default: 
{
return v___y_6066_;
}
}
}
else
{
return v___y_6066_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___boxed(lean_object* v___y_6094_, lean_object* v_suppressElabErrors_6095_, lean_object* v_x_6096_){
_start:
{
uint8_t v___y_7861__boxed_6097_; uint8_t v_suppressElabErrors_boxed_6098_; uint8_t v_res_6099_; lean_object* v_r_6100_; 
v___y_7861__boxed_6097_ = lean_unbox(v___y_6094_);
v_suppressElabErrors_boxed_6098_ = lean_unbox(v_suppressElabErrors_6095_);
v_res_6099_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0(v___y_7861__boxed_6097_, v_suppressElabErrors_boxed_6098_, v_x_6096_);
lean_dec(v_x_6096_);
v_r_6100_ = lean_box(v_res_6099_);
return v_r_6100_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7(lean_object* v_ref_6102_, lean_object* v_msgData_6103_, uint8_t v_severity_6104_, uint8_t v_isSilent_6105_, lean_object* v___y_6106_, lean_object* v___y_6107_, lean_object* v___y_6108_, lean_object* v___y_6109_){
_start:
{
lean_object* v___y_6112_; lean_object* v___y_6113_; uint8_t v___y_6114_; uint8_t v___y_6115_; lean_object* v___y_6116_; lean_object* v___y_6117_; lean_object* v___y_6118_; lean_object* v___y_6119_; lean_object* v___y_6120_; lean_object* v___y_6148_; uint8_t v___y_6149_; uint8_t v___y_6150_; uint8_t v___y_6151_; lean_object* v___y_6152_; lean_object* v___y_6153_; lean_object* v___y_6154_; lean_object* v___y_6155_; lean_object* v___y_6173_; uint8_t v___y_6174_; uint8_t v___y_6175_; uint8_t v___y_6176_; lean_object* v___y_6177_; lean_object* v___y_6178_; lean_object* v___y_6179_; lean_object* v___y_6180_; lean_object* v___y_6184_; uint8_t v___y_6185_; uint8_t v___y_6186_; lean_object* v___y_6187_; lean_object* v___y_6188_; lean_object* v___y_6189_; uint8_t v___y_6190_; uint8_t v___x_6195_; lean_object* v___y_6197_; uint8_t v___y_6198_; lean_object* v___y_6199_; lean_object* v___y_6200_; lean_object* v___y_6201_; uint8_t v___y_6202_; uint8_t v___y_6203_; uint8_t v___y_6205_; uint8_t v___x_6220_; 
v___x_6195_ = 2;
v___x_6220_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6104_, v___x_6195_);
if (v___x_6220_ == 0)
{
v___y_6205_ = v___x_6220_;
goto v___jp_6204_;
}
else
{
uint8_t v___x_6221_; 
lean_inc_ref(v_msgData_6103_);
v___x_6221_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_6103_);
v___y_6205_ = v___x_6221_;
goto v___jp_6204_;
}
v___jp_6111_:
{
lean_object* v___x_6121_; lean_object* v_currNamespace_6122_; lean_object* v_openDecls_6123_; lean_object* v_env_6124_; lean_object* v_nextMacroScope_6125_; lean_object* v_ngen_6126_; lean_object* v_auxDeclNGen_6127_; lean_object* v_traceState_6128_; lean_object* v_cache_6129_; lean_object* v_messages_6130_; lean_object* v_infoState_6131_; lean_object* v_snapshotTasks_6132_; lean_object* v___x_6134_; uint8_t v_isShared_6135_; uint8_t v_isSharedCheck_6146_; 
v___x_6121_ = lean_st_ref_take(v___y_6120_);
v_currNamespace_6122_ = lean_ctor_get(v___y_6119_, 6);
v_openDecls_6123_ = lean_ctor_get(v___y_6119_, 7);
v_env_6124_ = lean_ctor_get(v___x_6121_, 0);
v_nextMacroScope_6125_ = lean_ctor_get(v___x_6121_, 1);
v_ngen_6126_ = lean_ctor_get(v___x_6121_, 2);
v_auxDeclNGen_6127_ = lean_ctor_get(v___x_6121_, 3);
v_traceState_6128_ = lean_ctor_get(v___x_6121_, 4);
v_cache_6129_ = lean_ctor_get(v___x_6121_, 5);
v_messages_6130_ = lean_ctor_get(v___x_6121_, 6);
v_infoState_6131_ = lean_ctor_get(v___x_6121_, 7);
v_snapshotTasks_6132_ = lean_ctor_get(v___x_6121_, 8);
v_isSharedCheck_6146_ = !lean_is_exclusive(v___x_6121_);
if (v_isSharedCheck_6146_ == 0)
{
v___x_6134_ = v___x_6121_;
v_isShared_6135_ = v_isSharedCheck_6146_;
goto v_resetjp_6133_;
}
else
{
lean_inc(v_snapshotTasks_6132_);
lean_inc(v_infoState_6131_);
lean_inc(v_messages_6130_);
lean_inc(v_cache_6129_);
lean_inc(v_traceState_6128_);
lean_inc(v_auxDeclNGen_6127_);
lean_inc(v_ngen_6126_);
lean_inc(v_nextMacroScope_6125_);
lean_inc(v_env_6124_);
lean_dec(v___x_6121_);
v___x_6134_ = lean_box(0);
v_isShared_6135_ = v_isSharedCheck_6146_;
goto v_resetjp_6133_;
}
v_resetjp_6133_:
{
lean_object* v___x_6136_; lean_object* v___x_6137_; lean_object* v___x_6138_; lean_object* v___x_6139_; lean_object* v___x_6141_; 
lean_inc(v_openDecls_6123_);
lean_inc(v_currNamespace_6122_);
v___x_6136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6136_, 0, v_currNamespace_6122_);
lean_ctor_set(v___x_6136_, 1, v_openDecls_6123_);
v___x_6137_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6137_, 0, v___x_6136_);
lean_ctor_set(v___x_6137_, 1, v___y_6113_);
lean_inc_ref(v___y_6116_);
lean_inc_ref(v___y_6118_);
v___x_6138_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_6138_, 0, v___y_6118_);
lean_ctor_set(v___x_6138_, 1, v___y_6117_);
lean_ctor_set(v___x_6138_, 2, v___y_6112_);
lean_ctor_set(v___x_6138_, 3, v___y_6116_);
lean_ctor_set(v___x_6138_, 4, v___x_6137_);
lean_ctor_set_uint8(v___x_6138_, sizeof(void*)*5, v___y_6114_);
lean_ctor_set_uint8(v___x_6138_, sizeof(void*)*5 + 1, v___y_6115_);
lean_ctor_set_uint8(v___x_6138_, sizeof(void*)*5 + 2, v_isSilent_6105_);
v___x_6139_ = l_Lean_MessageLog_add(v___x_6138_, v_messages_6130_);
if (v_isShared_6135_ == 0)
{
lean_ctor_set(v___x_6134_, 6, v___x_6139_);
v___x_6141_ = v___x_6134_;
goto v_reusejp_6140_;
}
else
{
lean_object* v_reuseFailAlloc_6145_; 
v_reuseFailAlloc_6145_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6145_, 0, v_env_6124_);
lean_ctor_set(v_reuseFailAlloc_6145_, 1, v_nextMacroScope_6125_);
lean_ctor_set(v_reuseFailAlloc_6145_, 2, v_ngen_6126_);
lean_ctor_set(v_reuseFailAlloc_6145_, 3, v_auxDeclNGen_6127_);
lean_ctor_set(v_reuseFailAlloc_6145_, 4, v_traceState_6128_);
lean_ctor_set(v_reuseFailAlloc_6145_, 5, v_cache_6129_);
lean_ctor_set(v_reuseFailAlloc_6145_, 6, v___x_6139_);
lean_ctor_set(v_reuseFailAlloc_6145_, 7, v_infoState_6131_);
lean_ctor_set(v_reuseFailAlloc_6145_, 8, v_snapshotTasks_6132_);
v___x_6141_ = v_reuseFailAlloc_6145_;
goto v_reusejp_6140_;
}
v_reusejp_6140_:
{
lean_object* v___x_6142_; lean_object* v___x_6143_; lean_object* v___x_6144_; 
v___x_6142_ = lean_st_ref_set(v___y_6120_, v___x_6141_);
v___x_6143_ = lean_box(0);
v___x_6144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6144_, 0, v___x_6143_);
return v___x_6144_;
}
}
}
v___jp_6147_:
{
lean_object* v___x_6156_; lean_object* v___x_6157_; lean_object* v_a_6158_; lean_object* v___x_6160_; uint8_t v_isShared_6161_; uint8_t v_isSharedCheck_6171_; 
v___x_6156_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_6103_);
v___x_6157_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(v___x_6156_, v___y_6106_, v___y_6107_, v___y_6108_, v___y_6109_);
v_a_6158_ = lean_ctor_get(v___x_6157_, 0);
v_isSharedCheck_6171_ = !lean_is_exclusive(v___x_6157_);
if (v_isSharedCheck_6171_ == 0)
{
v___x_6160_ = v___x_6157_;
v_isShared_6161_ = v_isSharedCheck_6171_;
goto v_resetjp_6159_;
}
else
{
lean_inc(v_a_6158_);
lean_dec(v___x_6157_);
v___x_6160_ = lean_box(0);
v_isShared_6161_ = v_isSharedCheck_6171_;
goto v_resetjp_6159_;
}
v_resetjp_6159_:
{
lean_object* v___x_6162_; lean_object* v___x_6163_; lean_object* v___x_6164_; lean_object* v___x_6165_; 
lean_inc_ref_n(v___y_6152_, 2);
v___x_6162_ = l_Lean_FileMap_toPosition(v___y_6152_, v___y_6153_);
lean_dec(v___y_6153_);
v___x_6163_ = l_Lean_FileMap_toPosition(v___y_6152_, v___y_6155_);
lean_dec(v___y_6155_);
v___x_6164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6164_, 0, v___x_6163_);
v___x_6165_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___closed__0));
if (v___y_6149_ == 0)
{
lean_del_object(v___x_6160_);
lean_dec_ref(v___y_6148_);
v___y_6112_ = v___x_6164_;
v___y_6113_ = v_a_6158_;
v___y_6114_ = v___y_6150_;
v___y_6115_ = v___y_6151_;
v___y_6116_ = v___x_6165_;
v___y_6117_ = v___x_6162_;
v___y_6118_ = v___y_6154_;
v___y_6119_ = v___y_6108_;
v___y_6120_ = v___y_6109_;
goto v___jp_6111_;
}
else
{
uint8_t v___x_6166_; 
lean_inc(v_a_6158_);
v___x_6166_ = l_Lean_MessageData_hasTag(v___y_6148_, v_a_6158_);
if (v___x_6166_ == 0)
{
lean_object* v___x_6167_; lean_object* v___x_6169_; 
lean_dec_ref_known(v___x_6164_, 1);
lean_dec_ref(v___x_6162_);
lean_dec(v_a_6158_);
v___x_6167_ = lean_box(0);
if (v_isShared_6161_ == 0)
{
lean_ctor_set(v___x_6160_, 0, v___x_6167_);
v___x_6169_ = v___x_6160_;
goto v_reusejp_6168_;
}
else
{
lean_object* v_reuseFailAlloc_6170_; 
v_reuseFailAlloc_6170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6170_, 0, v___x_6167_);
v___x_6169_ = v_reuseFailAlloc_6170_;
goto v_reusejp_6168_;
}
v_reusejp_6168_:
{
return v___x_6169_;
}
}
else
{
lean_del_object(v___x_6160_);
v___y_6112_ = v___x_6164_;
v___y_6113_ = v_a_6158_;
v___y_6114_ = v___y_6150_;
v___y_6115_ = v___y_6151_;
v___y_6116_ = v___x_6165_;
v___y_6117_ = v___x_6162_;
v___y_6118_ = v___y_6154_;
v___y_6119_ = v___y_6108_;
v___y_6120_ = v___y_6109_;
goto v___jp_6111_;
}
}
}
}
v___jp_6172_:
{
lean_object* v___x_6181_; 
v___x_6181_ = l_Lean_Syntax_getTailPos_x3f(v___y_6177_, v___y_6174_);
lean_dec(v___y_6177_);
if (lean_obj_tag(v___x_6181_) == 0)
{
lean_inc(v___y_6180_);
v___y_6148_ = v___y_6173_;
v___y_6149_ = v___y_6175_;
v___y_6150_ = v___y_6174_;
v___y_6151_ = v___y_6176_;
v___y_6152_ = v___y_6178_;
v___y_6153_ = v___y_6180_;
v___y_6154_ = v___y_6179_;
v___y_6155_ = v___y_6180_;
goto v___jp_6147_;
}
else
{
lean_object* v_val_6182_; 
v_val_6182_ = lean_ctor_get(v___x_6181_, 0);
lean_inc(v_val_6182_);
lean_dec_ref_known(v___x_6181_, 1);
v___y_6148_ = v___y_6173_;
v___y_6149_ = v___y_6175_;
v___y_6150_ = v___y_6174_;
v___y_6151_ = v___y_6176_;
v___y_6152_ = v___y_6178_;
v___y_6153_ = v___y_6180_;
v___y_6154_ = v___y_6179_;
v___y_6155_ = v_val_6182_;
goto v___jp_6147_;
}
}
v___jp_6183_:
{
lean_object* v_ref_6191_; lean_object* v___x_6192_; 
v_ref_6191_ = l_Lean_replaceRef(v_ref_6102_, v___y_6187_);
v___x_6192_ = l_Lean_Syntax_getPos_x3f(v_ref_6191_, v___y_6186_);
if (lean_obj_tag(v___x_6192_) == 0)
{
lean_object* v___x_6193_; 
v___x_6193_ = lean_unsigned_to_nat(0u);
v___y_6173_ = v___y_6184_;
v___y_6174_ = v___y_6186_;
v___y_6175_ = v___y_6185_;
v___y_6176_ = v___y_6190_;
v___y_6177_ = v_ref_6191_;
v___y_6178_ = v___y_6188_;
v___y_6179_ = v___y_6189_;
v___y_6180_ = v___x_6193_;
goto v___jp_6172_;
}
else
{
lean_object* v_val_6194_; 
v_val_6194_ = lean_ctor_get(v___x_6192_, 0);
lean_inc(v_val_6194_);
lean_dec_ref_known(v___x_6192_, 1);
v___y_6173_ = v___y_6184_;
v___y_6174_ = v___y_6186_;
v___y_6175_ = v___y_6185_;
v___y_6176_ = v___y_6190_;
v___y_6177_ = v_ref_6191_;
v___y_6178_ = v___y_6188_;
v___y_6179_ = v___y_6189_;
v___y_6180_ = v_val_6194_;
goto v___jp_6172_;
}
}
v___jp_6196_:
{
if (v___y_6203_ == 0)
{
v___y_6184_ = v___y_6197_;
v___y_6185_ = v___y_6198_;
v___y_6186_ = v___y_6202_;
v___y_6187_ = v___y_6199_;
v___y_6188_ = v___y_6200_;
v___y_6189_ = v___y_6201_;
v___y_6190_ = v_severity_6104_;
goto v___jp_6183_;
}
else
{
v___y_6184_ = v___y_6197_;
v___y_6185_ = v___y_6198_;
v___y_6186_ = v___y_6202_;
v___y_6187_ = v___y_6199_;
v___y_6188_ = v___y_6200_;
v___y_6189_ = v___y_6201_;
v___y_6190_ = v___x_6195_;
goto v___jp_6183_;
}
}
v___jp_6204_:
{
if (v___y_6205_ == 0)
{
lean_object* v_fileName_6206_; lean_object* v_fileMap_6207_; lean_object* v_options_6208_; lean_object* v_ref_6209_; uint8_t v_suppressElabErrors_6210_; lean_object* v___x_6211_; lean_object* v___x_6212_; lean_object* v___f_6213_; uint8_t v___x_6214_; uint8_t v___x_6215_; 
v_fileName_6206_ = lean_ctor_get(v___y_6108_, 0);
v_fileMap_6207_ = lean_ctor_get(v___y_6108_, 1);
v_options_6208_ = lean_ctor_get(v___y_6108_, 2);
v_ref_6209_ = lean_ctor_get(v___y_6108_, 5);
v_suppressElabErrors_6210_ = lean_ctor_get_uint8(v___y_6108_, sizeof(void*)*14 + 1);
v___x_6211_ = lean_box(v___y_6205_);
v___x_6212_ = lean_box(v_suppressElabErrors_6210_);
v___f_6213_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_6213_, 0, v___x_6211_);
lean_closure_set(v___f_6213_, 1, v___x_6212_);
v___x_6214_ = 1;
v___x_6215_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6104_, v___x_6214_);
if (v___x_6215_ == 0)
{
v___y_6197_ = v___f_6213_;
v___y_6198_ = v_suppressElabErrors_6210_;
v___y_6199_ = v_ref_6209_;
v___y_6200_ = v_fileMap_6207_;
v___y_6201_ = v_fileName_6206_;
v___y_6202_ = v___y_6205_;
v___y_6203_ = v___x_6215_;
goto v___jp_6196_;
}
else
{
lean_object* v___x_6216_; uint8_t v___x_6217_; 
v___x_6216_ = l_Lean_warningAsError;
v___x_6217_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(v_options_6208_, v___x_6216_);
v___y_6197_ = v___f_6213_;
v___y_6198_ = v_suppressElabErrors_6210_;
v___y_6199_ = v_ref_6209_;
v___y_6200_ = v_fileMap_6207_;
v___y_6201_ = v_fileName_6206_;
v___y_6202_ = v___y_6205_;
v___y_6203_ = v___x_6217_;
goto v___jp_6196_;
}
}
else
{
lean_object* v___x_6218_; lean_object* v___x_6219_; 
lean_dec_ref(v_msgData_6103_);
v___x_6218_ = lean_box(0);
v___x_6219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6219_, 0, v___x_6218_);
return v___x_6219_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___boxed(lean_object* v_ref_6222_, lean_object* v_msgData_6223_, lean_object* v_severity_6224_, lean_object* v_isSilent_6225_, lean_object* v___y_6226_, lean_object* v___y_6227_, lean_object* v___y_6228_, lean_object* v___y_6229_, lean_object* v___y_6230_){
_start:
{
uint8_t v_severity_boxed_6231_; uint8_t v_isSilent_boxed_6232_; lean_object* v_res_6233_; 
v_severity_boxed_6231_ = lean_unbox(v_severity_6224_);
v_isSilent_boxed_6232_ = lean_unbox(v_isSilent_6225_);
v_res_6233_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7(v_ref_6222_, v_msgData_6223_, v_severity_boxed_6231_, v_isSilent_boxed_6232_, v___y_6226_, v___y_6227_, v___y_6228_, v___y_6229_);
lean_dec(v___y_6229_);
lean_dec_ref(v___y_6228_);
lean_dec(v___y_6227_);
lean_dec_ref(v___y_6226_);
lean_dec(v_ref_6222_);
return v_res_6233_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3(lean_object* v_msgData_6234_, uint8_t v_severity_6235_, uint8_t v_isSilent_6236_, lean_object* v___y_6237_, lean_object* v___y_6238_, lean_object* v___y_6239_, lean_object* v___y_6240_){
_start:
{
lean_object* v_ref_6242_; lean_object* v___x_6243_; 
v_ref_6242_ = lean_ctor_get(v___y_6239_, 5);
v___x_6243_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7(v_ref_6242_, v_msgData_6234_, v_severity_6235_, v_isSilent_6236_, v___y_6237_, v___y_6238_, v___y_6239_, v___y_6240_);
return v___x_6243_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_msgData_6244_, lean_object* v_severity_6245_, lean_object* v_isSilent_6246_, lean_object* v___y_6247_, lean_object* v___y_6248_, lean_object* v___y_6249_, lean_object* v___y_6250_, lean_object* v___y_6251_){
_start:
{
uint8_t v_severity_boxed_6252_; uint8_t v_isSilent_boxed_6253_; lean_object* v_res_6254_; 
v_severity_boxed_6252_ = lean_unbox(v_severity_6245_);
v_isSilent_boxed_6253_ = lean_unbox(v_isSilent_6246_);
v_res_6254_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3(v_msgData_6244_, v_severity_boxed_6252_, v_isSilent_boxed_6253_, v___y_6247_, v___y_6248_, v___y_6249_, v___y_6250_);
lean_dec(v___y_6250_);
lean_dec_ref(v___y_6249_);
lean_dec(v___y_6248_);
lean_dec_ref(v___y_6247_);
return v_res_6254_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2(lean_object* v_msgData_6255_, lean_object* v___y_6256_, lean_object* v___y_6257_, lean_object* v___y_6258_, lean_object* v___y_6259_){
_start:
{
uint8_t v___x_6261_; uint8_t v___x_6262_; lean_object* v___x_6263_; 
v___x_6261_ = 2;
v___x_6262_ = 0;
v___x_6263_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3(v_msgData_6255_, v___x_6261_, v___x_6262_, v___y_6256_, v___y_6257_, v___y_6258_, v___y_6259_);
return v___x_6263_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_6264_, lean_object* v___y_6265_, lean_object* v___y_6266_, lean_object* v___y_6267_, lean_object* v___y_6268_, lean_object* v___y_6269_){
_start:
{
lean_object* v_res_6270_; 
v_res_6270_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2(v_msgData_6264_, v___y_6265_, v___y_6266_, v___y_6267_, v___y_6268_);
lean_dec(v___y_6268_);
lean_dec_ref(v___y_6267_);
lean_dec(v___y_6266_);
lean_dec_ref(v___y_6265_);
return v_res_6270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0(lean_object* v_f_6271_, lean_object* v___y_6272_, lean_object* v___y_6273_, lean_object* v___y_6274_, lean_object* v___y_6275_){
_start:
{
lean_object* v_module_6277_; lean_object* v_const_6278_; lean_object* v_exception_6279_; lean_object* v___x_6280_; lean_object* v___x_6281_; lean_object* v___x_6282_; lean_object* v___x_6283_; lean_object* v___x_6284_; lean_object* v___x_6285_; lean_object* v___x_6286_; lean_object* v___x_6287_; lean_object* v___x_6288_; lean_object* v___x_6289_; lean_object* v___x_6290_; lean_object* v___x_6291_; 
v_module_6277_ = lean_ctor_get(v_f_6271_, 0);
lean_inc(v_module_6277_);
v_const_6278_ = lean_ctor_get(v_f_6271_, 1);
lean_inc(v_const_6278_);
v_exception_6279_ = lean_ctor_get(v_f_6271_, 2);
lean_inc_ref(v_exception_6279_);
lean_dec_ref(v_f_6271_);
v___x_6280_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1);
v___x_6281_ = l_Lean_MessageData_ofName(v_const_6278_);
v___x_6282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6282_, 0, v___x_6280_);
lean_ctor_set(v___x_6282_, 1, v___x_6281_);
v___x_6283_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3);
v___x_6284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6284_, 0, v___x_6282_);
lean_ctor_set(v___x_6284_, 1, v___x_6283_);
v___x_6285_ = l_Lean_MessageData_ofName(v_module_6277_);
v___x_6286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6286_, 0, v___x_6284_);
lean_ctor_set(v___x_6286_, 1, v___x_6285_);
v___x_6287_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5);
v___x_6288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6288_, 0, v___x_6286_);
lean_ctor_set(v___x_6288_, 1, v___x_6287_);
v___x_6289_ = l_Lean_Exception_toMessageData(v_exception_6279_);
v___x_6290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6290_, 0, v___x_6288_);
lean_ctor_set(v___x_6290_, 1, v___x_6289_);
v___x_6291_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2(v___x_6290_, v___y_6272_, v___y_6273_, v___y_6274_, v___y_6275_);
return v___x_6291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0___boxed(lean_object* v_f_6292_, lean_object* v___y_6293_, lean_object* v___y_6294_, lean_object* v___y_6295_, lean_object* v___y_6296_, lean_object* v___y_6297_){
_start:
{
lean_object* v_res_6298_; 
v_res_6298_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0(v_f_6292_, v___y_6293_, v___y_6294_, v___y_6295_, v___y_6296_);
lean_dec(v___y_6296_);
lean_dec_ref(v___y_6295_);
lean_dec(v___y_6294_);
lean_dec_ref(v___y_6293_);
return v_res_6298_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3(lean_object* v_as_6299_, size_t v_i_6300_, size_t v_stop_6301_, lean_object* v_b_6302_, lean_object* v___y_6303_, lean_object* v___y_6304_, lean_object* v___y_6305_, lean_object* v___y_6306_){
_start:
{
uint8_t v___x_6308_; 
v___x_6308_ = lean_usize_dec_eq(v_i_6300_, v_stop_6301_);
if (v___x_6308_ == 0)
{
lean_object* v___x_6309_; lean_object* v___x_6310_; 
v___x_6309_ = lean_array_uget_borrowed(v_as_6299_, v_i_6300_);
lean_inc(v___x_6309_);
v___x_6310_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0(v___x_6309_, v___y_6303_, v___y_6304_, v___y_6305_, v___y_6306_);
if (lean_obj_tag(v___x_6310_) == 0)
{
lean_object* v_a_6311_; size_t v___x_6312_; size_t v___x_6313_; 
v_a_6311_ = lean_ctor_get(v___x_6310_, 0);
lean_inc(v_a_6311_);
lean_dec_ref_known(v___x_6310_, 1);
v___x_6312_ = ((size_t)1ULL);
v___x_6313_ = lean_usize_add(v_i_6300_, v___x_6312_);
v_i_6300_ = v___x_6313_;
v_b_6302_ = v_a_6311_;
goto _start;
}
else
{
return v___x_6310_;
}
}
else
{
lean_object* v___x_6315_; 
v___x_6315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6315_, 0, v_b_6302_);
return v___x_6315_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3___boxed(lean_object* v_as_6316_, lean_object* v_i_6317_, lean_object* v_stop_6318_, lean_object* v_b_6319_, lean_object* v___y_6320_, lean_object* v___y_6321_, lean_object* v___y_6322_, lean_object* v___y_6323_, lean_object* v___y_6324_){
_start:
{
size_t v_i_boxed_6325_; size_t v_stop_boxed_6326_; lean_object* v_res_6327_; 
v_i_boxed_6325_ = lean_unbox_usize(v_i_6317_);
lean_dec(v_i_6317_);
v_stop_boxed_6326_ = lean_unbox_usize(v_stop_6318_);
lean_dec(v_stop_6318_);
v_res_6327_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3(v_as_6316_, v_i_boxed_6325_, v_stop_boxed_6326_, v_b_6319_, v___y_6320_, v___y_6321_, v___y_6322_, v___y_6323_);
lean_dec(v___y_6323_);
lean_dec_ref(v___y_6322_);
lean_dec(v___y_6321_);
lean_dec_ref(v___y_6320_);
lean_dec_ref(v_as_6316_);
return v_res_6327_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(lean_object* v_as_6328_, size_t v_i_6329_, size_t v_stop_6330_, lean_object* v_b_6331_){
_start:
{
uint8_t v___x_6332_; 
v___x_6332_ = lean_usize_dec_eq(v_i_6329_, v_stop_6330_);
if (v___x_6332_ == 0)
{
lean_object* v___x_6333_; lean_object* v___x_6334_; lean_object* v___x_6335_; size_t v___x_6336_; size_t v___x_6337_; 
v___x_6333_ = lean_array_uget_borrowed(v_as_6328_, v_i_6329_);
lean_inc(v___x_6333_);
v___x_6334_ = lean_task_get_own(v___x_6333_);
v___x_6335_ = l_Lean_Meta_LazyDiscrTree_InitResults_append___redArg(v_b_6331_, v___x_6334_);
v___x_6336_ = ((size_t)1ULL);
v___x_6337_ = lean_usize_add(v_i_6329_, v___x_6336_);
v_i_6329_ = v___x_6337_;
v_b_6331_ = v___x_6335_;
goto _start;
}
else
{
return v_b_6331_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_as_6339_, lean_object* v_i_6340_, lean_object* v_stop_6341_, lean_object* v_b_6342_){
_start:
{
size_t v_i_boxed_6343_; size_t v_stop_boxed_6344_; lean_object* v_res_6345_; 
v_i_boxed_6343_ = lean_unbox_usize(v_i_6340_);
lean_dec(v_i_6340_);
v_stop_boxed_6344_ = lean_unbox_usize(v_stop_6341_);
lean_dec(v_stop_6341_);
v_res_6345_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(v_as_6339_, v_i_boxed_6343_, v_stop_boxed_6344_, v_b_6342_);
lean_dec_ref(v_as_6339_);
return v_res_6345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(lean_object* v_z_6346_, lean_object* v_tasks_6347_){
_start:
{
lean_object* v___x_6348_; lean_object* v___x_6349_; uint8_t v___x_6350_; 
v___x_6348_ = lean_unsigned_to_nat(0u);
v___x_6349_ = lean_array_get_size(v_tasks_6347_);
v___x_6350_ = lean_nat_dec_lt(v___x_6348_, v___x_6349_);
if (v___x_6350_ == 0)
{
return v_z_6346_;
}
else
{
uint8_t v___x_6351_; 
v___x_6351_ = lean_nat_dec_le(v___x_6349_, v___x_6349_);
if (v___x_6351_ == 0)
{
if (v___x_6350_ == 0)
{
return v_z_6346_;
}
else
{
size_t v___x_6352_; size_t v___x_6353_; lean_object* v___x_6354_; 
v___x_6352_ = ((size_t)0ULL);
v___x_6353_ = lean_usize_of_nat(v___x_6349_);
v___x_6354_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(v_tasks_6347_, v___x_6352_, v___x_6353_, v_z_6346_);
return v___x_6354_;
}
}
else
{
size_t v___x_6355_; size_t v___x_6356_; lean_object* v___x_6357_; 
v___x_6355_ = ((size_t)0ULL);
v___x_6356_ = lean_usize_of_nat(v___x_6349_);
v___x_6357_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(v_tasks_6347_, v___x_6355_, v___x_6356_, v_z_6346_);
return v___x_6357_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg___boxed(lean_object* v_z_6358_, lean_object* v_tasks_6359_){
_start:
{
lean_object* v_res_6360_; 
v_res_6360_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(v_z_6358_, v_tasks_6359_);
lean_dec_ref(v_tasks_6359_);
return v_res_6360_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_6361_; lean_object* v___x_6362_; lean_object* v___x_6363_; 
v___x_6361_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
v___x_6362_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_6363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6363_, 0, v___x_6362_);
lean_ctor_set(v___x_6363_, 1, v___x_6361_);
return v___x_6363_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_6364_; lean_object* v___x_6365_; lean_object* v___x_6366_; 
v___x_6364_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
v___x_6365_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0);
v___x_6366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6366_, 0, v___x_6365_);
lean_ctor_set(v___x_6366_, 1, v___x_6364_);
return v___x_6366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(lean_object* v_cctx_6367_, lean_object* v_ngen_6368_, lean_object* v_env_6369_, lean_object* v_act_6370_, lean_object* v_constantsPerTask_6371_, lean_object* v___y_6372_, lean_object* v___y_6373_, lean_object* v___y_6374_, lean_object* v___y_6375_){
_start:
{
lean_object* v___x_6377_; lean_object* v_moduleData_6378_; lean_object* v_n_6379_; lean_object* v___x_6380_; lean_object* v___x_6381_; lean_object* v___x_6382_; lean_object* v_a_6383_; lean_object* v___x_6385_; uint8_t v_isShared_6386_; uint8_t v_isSharedCheck_6425_; 
v___x_6377_ = l_Lean_Environment_header(v_env_6369_);
v_moduleData_6378_ = lean_ctor_get(v___x_6377_, 6);
lean_inc_ref(v_moduleData_6378_);
lean_dec_ref(v___x_6377_);
v_n_6379_ = lean_array_get_size(v_moduleData_6378_);
lean_dec_ref(v_moduleData_6378_);
v___x_6380_ = lean_unsigned_to_nat(0u);
v___x_6381_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
v___x_6382_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(v_cctx_6367_, v_env_6369_, v_act_6370_, v_constantsPerTask_6371_, v_n_6379_, v_ngen_6368_, v___x_6381_, v___x_6380_, v___x_6380_, v___x_6380_);
v_a_6383_ = lean_ctor_get(v___x_6382_, 0);
v_isSharedCheck_6425_ = !lean_is_exclusive(v___x_6382_);
if (v_isSharedCheck_6425_ == 0)
{
v___x_6385_ = v___x_6382_;
v_isShared_6386_ = v_isSharedCheck_6425_;
goto v_resetjp_6384_;
}
else
{
lean_inc(v_a_6383_);
lean_dec(v___x_6382_);
v___x_6385_ = lean_box(0);
v_isShared_6386_ = v_isSharedCheck_6425_;
goto v_resetjp_6384_;
}
v_resetjp_6384_:
{
lean_object* v___x_6387_; lean_object* v_r_6388_; lean_object* v_tree_6395_; lean_object* v_errors_6396_; lean_object* v___x_6397_; uint8_t v___x_6398_; 
v___x_6387_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1);
v_r_6388_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(v___x_6387_, v_a_6383_);
lean_dec(v_a_6383_);
v_tree_6395_ = lean_ctor_get(v_r_6388_, 0);
lean_inc_ref(v_tree_6395_);
v_errors_6396_ = lean_ctor_get(v_r_6388_, 1);
lean_inc_ref(v_errors_6396_);
v___x_6397_ = lean_array_get_size(v_errors_6396_);
v___x_6398_ = lean_nat_dec_lt(v___x_6380_, v___x_6397_);
if (v___x_6398_ == 0)
{
lean_object* v___x_6399_; lean_object* v___x_6400_; 
lean_dec_ref(v_errors_6396_);
lean_dec_ref(v_r_6388_);
lean_del_object(v___x_6385_);
v___x_6399_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_tree_6395_);
v___x_6400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6400_, 0, v___x_6399_);
return v___x_6400_;
}
else
{
lean_object* v___x_6401_; uint8_t v___x_6402_; 
lean_dec_ref(v_tree_6395_);
v___x_6401_ = lean_box(0);
v___x_6402_ = lean_nat_dec_le(v___x_6397_, v___x_6397_);
if (v___x_6402_ == 0)
{
if (v___x_6398_ == 0)
{
lean_dec_ref(v_errors_6396_);
goto v___jp_6389_;
}
else
{
size_t v___x_6403_; size_t v___x_6404_; lean_object* v___x_6405_; 
v___x_6403_ = ((size_t)0ULL);
v___x_6404_ = lean_usize_of_nat(v___x_6397_);
v___x_6405_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3(v_errors_6396_, v___x_6403_, v___x_6404_, v___x_6401_, v___y_6372_, v___y_6373_, v___y_6374_, v___y_6375_);
lean_dec_ref(v_errors_6396_);
if (lean_obj_tag(v___x_6405_) == 0)
{
lean_dec_ref_known(v___x_6405_, 1);
goto v___jp_6389_;
}
else
{
lean_object* v_a_6406_; lean_object* v___x_6408_; uint8_t v_isShared_6409_; uint8_t v_isSharedCheck_6413_; 
lean_dec_ref(v_r_6388_);
lean_del_object(v___x_6385_);
v_a_6406_ = lean_ctor_get(v___x_6405_, 0);
v_isSharedCheck_6413_ = !lean_is_exclusive(v___x_6405_);
if (v_isSharedCheck_6413_ == 0)
{
v___x_6408_ = v___x_6405_;
v_isShared_6409_ = v_isSharedCheck_6413_;
goto v_resetjp_6407_;
}
else
{
lean_inc(v_a_6406_);
lean_dec(v___x_6405_);
v___x_6408_ = lean_box(0);
v_isShared_6409_ = v_isSharedCheck_6413_;
goto v_resetjp_6407_;
}
v_resetjp_6407_:
{
lean_object* v___x_6411_; 
if (v_isShared_6409_ == 0)
{
v___x_6411_ = v___x_6408_;
goto v_reusejp_6410_;
}
else
{
lean_object* v_reuseFailAlloc_6412_; 
v_reuseFailAlloc_6412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6412_, 0, v_a_6406_);
v___x_6411_ = v_reuseFailAlloc_6412_;
goto v_reusejp_6410_;
}
v_reusejp_6410_:
{
return v___x_6411_;
}
}
}
}
}
else
{
size_t v___x_6414_; size_t v___x_6415_; lean_object* v___x_6416_; 
v___x_6414_ = ((size_t)0ULL);
v___x_6415_ = lean_usize_of_nat(v___x_6397_);
v___x_6416_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3(v_errors_6396_, v___x_6414_, v___x_6415_, v___x_6401_, v___y_6372_, v___y_6373_, v___y_6374_, v___y_6375_);
lean_dec_ref(v_errors_6396_);
if (lean_obj_tag(v___x_6416_) == 0)
{
lean_dec_ref_known(v___x_6416_, 1);
goto v___jp_6389_;
}
else
{
lean_object* v_a_6417_; lean_object* v___x_6419_; uint8_t v_isShared_6420_; uint8_t v_isSharedCheck_6424_; 
lean_dec_ref(v_r_6388_);
lean_del_object(v___x_6385_);
v_a_6417_ = lean_ctor_get(v___x_6416_, 0);
v_isSharedCheck_6424_ = !lean_is_exclusive(v___x_6416_);
if (v_isSharedCheck_6424_ == 0)
{
v___x_6419_ = v___x_6416_;
v_isShared_6420_ = v_isSharedCheck_6424_;
goto v_resetjp_6418_;
}
else
{
lean_inc(v_a_6417_);
lean_dec(v___x_6416_);
v___x_6419_ = lean_box(0);
v_isShared_6420_ = v_isSharedCheck_6424_;
goto v_resetjp_6418_;
}
v_resetjp_6418_:
{
lean_object* v___x_6422_; 
if (v_isShared_6420_ == 0)
{
v___x_6422_ = v___x_6419_;
goto v_reusejp_6421_;
}
else
{
lean_object* v_reuseFailAlloc_6423_; 
v_reuseFailAlloc_6423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6423_, 0, v_a_6417_);
v___x_6422_ = v_reuseFailAlloc_6423_;
goto v_reusejp_6421_;
}
v_reusejp_6421_:
{
return v___x_6422_;
}
}
}
}
}
v___jp_6389_:
{
lean_object* v_tree_6390_; lean_object* v___x_6391_; lean_object* v___x_6393_; 
v_tree_6390_ = lean_ctor_get(v_r_6388_, 0);
lean_inc_ref(v_tree_6390_);
lean_dec_ref(v_r_6388_);
v___x_6391_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_tree_6390_);
if (v_isShared_6386_ == 0)
{
lean_ctor_set(v___x_6385_, 0, v___x_6391_);
v___x_6393_ = v___x_6385_;
goto v_reusejp_6392_;
}
else
{
lean_object* v_reuseFailAlloc_6394_; 
v_reuseFailAlloc_6394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6394_, 0, v___x_6391_);
v___x_6393_ = v_reuseFailAlloc_6394_;
goto v_reusejp_6392_;
}
v_reusejp_6392_:
{
return v___x_6393_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___boxed(lean_object* v_cctx_6426_, lean_object* v_ngen_6427_, lean_object* v_env_6428_, lean_object* v_act_6429_, lean_object* v_constantsPerTask_6430_, lean_object* v___y_6431_, lean_object* v___y_6432_, lean_object* v___y_6433_, lean_object* v___y_6434_, lean_object* v___y_6435_){
_start:
{
lean_object* v_res_6436_; 
v_res_6436_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(v_cctx_6426_, v_ngen_6427_, v_env_6428_, v_act_6429_, v_constantsPerTask_6430_, v___y_6431_, v___y_6432_, v___y_6433_, v___y_6434_);
lean_dec(v___y_6434_);
lean_dec_ref(v___y_6433_);
lean_dec(v___y_6432_);
lean_dec_ref(v___y_6431_);
lean_dec(v_constantsPerTask_6430_);
return v_res_6436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0(lean_object* v_a_6437_, lean_object* v___x_6438_, lean_object* v_addEntry_6439_, lean_object* v_constantsPerTask_6440_, lean_object* v_droppedEntriesRef_6441_, lean_object* v_droppedKeys_6442_, lean_object* v___y_6443_, lean_object* v___y_6444_, lean_object* v___y_6445_, lean_object* v___y_6446_){
_start:
{
lean_object* v___x_6448_; lean_object* v_env_6449_; lean_object* v___x_6450_; lean_object* v___x_6451_; 
v___x_6448_ = lean_st_ref_get(v___y_6446_);
v_env_6449_ = lean_ctor_get(v___x_6448_, 0);
lean_inc_ref(v_env_6449_);
lean_dec(v___x_6448_);
lean_inc_ref(v_a_6437_);
v___x_6450_ = l_Lean_Meta_LazyDiscrTree_createTreeCtx(v_a_6437_);
v___x_6451_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(v___x_6450_, v___x_6438_, v_env_6449_, v_addEntry_6439_, v_constantsPerTask_6440_, v___y_6443_, v___y_6444_, v___y_6445_, v___y_6446_);
if (lean_obj_tag(v___x_6451_) == 0)
{
if (lean_obj_tag(v_droppedEntriesRef_6441_) == 1)
{
lean_object* v_a_6452_; lean_object* v_val_6453_; lean_object* v___x_6455_; uint8_t v_isShared_6456_; uint8_t v_isSharedCheck_6486_; 
v_a_6452_ = lean_ctor_get(v___x_6451_, 0);
lean_inc(v_a_6452_);
lean_dec_ref_known(v___x_6451_, 1);
v_val_6453_ = lean_ctor_get(v_droppedEntriesRef_6441_, 0);
v_isSharedCheck_6486_ = !lean_is_exclusive(v_droppedEntriesRef_6441_);
if (v_isSharedCheck_6486_ == 0)
{
v___x_6455_ = v_droppedEntriesRef_6441_;
v_isShared_6456_ = v_isSharedCheck_6486_;
goto v_resetjp_6454_;
}
else
{
lean_inc(v_val_6453_);
lean_dec(v_droppedEntriesRef_6441_);
v___x_6455_ = lean_box(0);
v_isShared_6456_ = v_isSharedCheck_6486_;
goto v_resetjp_6454_;
}
v_resetjp_6454_:
{
lean_object* v___x_6457_; 
v___x_6457_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_a_6452_, v_droppedKeys_6442_, v___y_6443_, v___y_6444_, v___y_6445_, v___y_6446_);
lean_dec(v_droppedKeys_6442_);
if (lean_obj_tag(v___x_6457_) == 0)
{
lean_object* v_a_6458_; lean_object* v___x_6460_; uint8_t v_isShared_6461_; uint8_t v_isSharedCheck_6477_; 
v_a_6458_ = lean_ctor_get(v___x_6457_, 0);
v_isSharedCheck_6477_ = !lean_is_exclusive(v___x_6457_);
if (v_isSharedCheck_6477_ == 0)
{
v___x_6460_ = v___x_6457_;
v_isShared_6461_ = v_isSharedCheck_6477_;
goto v_resetjp_6459_;
}
else
{
lean_inc(v_a_6458_);
lean_dec(v___x_6457_);
v___x_6460_ = lean_box(0);
v_isShared_6461_ = v_isSharedCheck_6477_;
goto v_resetjp_6459_;
}
v_resetjp_6459_:
{
lean_object* v_fst_6462_; lean_object* v_snd_6463_; lean_object* v___x_6464_; lean_object* v___y_6466_; 
v_fst_6462_ = lean_ctor_get(v_a_6458_, 0);
lean_inc(v_fst_6462_);
v_snd_6463_ = lean_ctor_get(v_a_6458_, 1);
lean_inc(v_snd_6463_);
lean_dec(v_a_6458_);
v___x_6464_ = lean_st_ref_get(v_val_6453_);
if (lean_obj_tag(v___x_6464_) == 0)
{
lean_object* v___x_6475_; 
v___x_6475_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___y_6466_ = v___x_6475_;
goto v___jp_6465_;
}
else
{
lean_object* v_val_6476_; 
v_val_6476_ = lean_ctor_get(v___x_6464_, 0);
lean_inc(v_val_6476_);
lean_dec_ref_known(v___x_6464_, 1);
v___y_6466_ = v_val_6476_;
goto v___jp_6465_;
}
v___jp_6465_:
{
lean_object* v___x_6467_; lean_object* v___x_6469_; 
v___x_6467_ = l_Array_append___redArg(v___y_6466_, v_fst_6462_);
lean_dec(v_fst_6462_);
if (v_isShared_6456_ == 0)
{
lean_ctor_set(v___x_6455_, 0, v___x_6467_);
v___x_6469_ = v___x_6455_;
goto v_reusejp_6468_;
}
else
{
lean_object* v_reuseFailAlloc_6474_; 
v_reuseFailAlloc_6474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6474_, 0, v___x_6467_);
v___x_6469_ = v_reuseFailAlloc_6474_;
goto v_reusejp_6468_;
}
v_reusejp_6468_:
{
lean_object* v___x_6470_; lean_object* v___x_6472_; 
v___x_6470_ = lean_st_ref_set(v_val_6453_, v___x_6469_);
lean_dec(v_val_6453_);
if (v_isShared_6461_ == 0)
{
lean_ctor_set(v___x_6460_, 0, v_snd_6463_);
v___x_6472_ = v___x_6460_;
goto v_reusejp_6471_;
}
else
{
lean_object* v_reuseFailAlloc_6473_; 
v_reuseFailAlloc_6473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6473_, 0, v_snd_6463_);
v___x_6472_ = v_reuseFailAlloc_6473_;
goto v_reusejp_6471_;
}
v_reusejp_6471_:
{
return v___x_6472_;
}
}
}
}
}
else
{
lean_object* v_a_6478_; lean_object* v___x_6480_; uint8_t v_isShared_6481_; uint8_t v_isSharedCheck_6485_; 
lean_del_object(v___x_6455_);
lean_dec(v_val_6453_);
v_a_6478_ = lean_ctor_get(v___x_6457_, 0);
v_isSharedCheck_6485_ = !lean_is_exclusive(v___x_6457_);
if (v_isSharedCheck_6485_ == 0)
{
v___x_6480_ = v___x_6457_;
v_isShared_6481_ = v_isSharedCheck_6485_;
goto v_resetjp_6479_;
}
else
{
lean_inc(v_a_6478_);
lean_dec(v___x_6457_);
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
lean_object* v_a_6487_; lean_object* v___x_6488_; 
lean_dec(v_droppedEntriesRef_6441_);
v_a_6487_ = lean_ctor_get(v___x_6451_, 0);
lean_inc(v_a_6487_);
lean_dec_ref_known(v___x_6451_, 1);
v___x_6488_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_a_6487_, v_droppedKeys_6442_, v___y_6443_, v___y_6444_, v___y_6445_, v___y_6446_);
return v___x_6488_;
}
}
else
{
lean_dec(v_droppedKeys_6442_);
lean_dec(v_droppedEntriesRef_6441_);
return v___x_6451_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0___boxed(lean_object* v_a_6489_, lean_object* v___x_6490_, lean_object* v_addEntry_6491_, lean_object* v_constantsPerTask_6492_, lean_object* v_droppedEntriesRef_6493_, lean_object* v_droppedKeys_6494_, lean_object* v___y_6495_, lean_object* v___y_6496_, lean_object* v___y_6497_, lean_object* v___y_6498_, lean_object* v___y_6499_){
_start:
{
lean_object* v_res_6500_; 
v_res_6500_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0(v_a_6489_, v___x_6490_, v_addEntry_6491_, v_constantsPerTask_6492_, v_droppedEntriesRef_6493_, v_droppedKeys_6494_, v___y_6495_, v___y_6496_, v___y_6497_, v___y_6498_);
lean_dec(v___y_6498_);
lean_dec_ref(v___y_6497_);
lean_dec(v___y_6496_);
lean_dec_ref(v___y_6495_);
lean_dec(v_constantsPerTask_6492_);
lean_dec_ref(v_a_6489_);
return v_res_6500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(lean_object* v_ref_6502_, lean_object* v_addEntry_6503_, lean_object* v_droppedKeys_6504_, lean_object* v_constantsPerTask_6505_, lean_object* v_droppedEntriesRef_6506_, lean_object* v_ty_6507_, lean_object* v_a_6508_, lean_object* v_a_6509_, lean_object* v_a_6510_, lean_object* v_a_6511_){
_start:
{
lean_object* v_a_6514_; lean_object* v___x_6536_; lean_object* v_ngen_6537_; lean_object* v_namePrefix_6538_; lean_object* v_idx_6539_; lean_object* v___x_6541_; uint8_t v_isShared_6542_; uint8_t v_isSharedCheck_6584_; 
v___x_6536_ = lean_st_ref_get(v_a_6511_);
v_ngen_6537_ = lean_ctor_get(v___x_6536_, 2);
lean_inc_ref(v_ngen_6537_);
lean_dec(v___x_6536_);
v_namePrefix_6538_ = lean_ctor_get(v_ngen_6537_, 0);
v_idx_6539_ = lean_ctor_get(v_ngen_6537_, 1);
v_isSharedCheck_6584_ = !lean_is_exclusive(v_ngen_6537_);
if (v_isSharedCheck_6584_ == 0)
{
v___x_6541_ = v_ngen_6537_;
v_isShared_6542_ = v_isSharedCheck_6584_;
goto v_resetjp_6540_;
}
else
{
lean_inc(v_idx_6539_);
lean_inc(v_namePrefix_6538_);
lean_dec(v_ngen_6537_);
v___x_6541_ = lean_box(0);
v_isShared_6542_ = v_isSharedCheck_6584_;
goto v_resetjp_6540_;
}
v___jp_6513_:
{
lean_object* v___x_6515_; 
v___x_6515_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v_a_6514_, v_ty_6507_, v_a_6508_, v_a_6509_, v_a_6510_, v_a_6511_);
if (lean_obj_tag(v___x_6515_) == 0)
{
lean_object* v_a_6516_; lean_object* v___x_6518_; uint8_t v_isShared_6519_; uint8_t v_isSharedCheck_6527_; 
v_a_6516_ = lean_ctor_get(v___x_6515_, 0);
v_isSharedCheck_6527_ = !lean_is_exclusive(v___x_6515_);
if (v_isSharedCheck_6527_ == 0)
{
v___x_6518_ = v___x_6515_;
v_isShared_6519_ = v_isSharedCheck_6527_;
goto v_resetjp_6517_;
}
else
{
lean_inc(v_a_6516_);
lean_dec(v___x_6515_);
v___x_6518_ = lean_box(0);
v_isShared_6519_ = v_isSharedCheck_6527_;
goto v_resetjp_6517_;
}
v_resetjp_6517_:
{
lean_object* v_fst_6520_; lean_object* v_snd_6521_; lean_object* v___x_6522_; lean_object* v___x_6523_; lean_object* v___x_6525_; 
v_fst_6520_ = lean_ctor_get(v_a_6516_, 0);
lean_inc(v_fst_6520_);
v_snd_6521_ = lean_ctor_get(v_a_6516_, 1);
lean_inc(v_snd_6521_);
lean_dec(v_a_6516_);
v___x_6522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6522_, 0, v_snd_6521_);
v___x_6523_ = lean_st_ref_set(v_ref_6502_, v___x_6522_);
if (v_isShared_6519_ == 0)
{
lean_ctor_set(v___x_6518_, 0, v_fst_6520_);
v___x_6525_ = v___x_6518_;
goto v_reusejp_6524_;
}
else
{
lean_object* v_reuseFailAlloc_6526_; 
v_reuseFailAlloc_6526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6526_, 0, v_fst_6520_);
v___x_6525_ = v_reuseFailAlloc_6526_;
goto v_reusejp_6524_;
}
v_reusejp_6524_:
{
return v___x_6525_;
}
}
}
else
{
lean_object* v_a_6528_; lean_object* v___x_6530_; uint8_t v_isShared_6531_; uint8_t v_isSharedCheck_6535_; 
v_a_6528_ = lean_ctor_get(v___x_6515_, 0);
v_isSharedCheck_6535_ = !lean_is_exclusive(v___x_6515_);
if (v_isSharedCheck_6535_ == 0)
{
v___x_6530_ = v___x_6515_;
v_isShared_6531_ = v_isSharedCheck_6535_;
goto v_resetjp_6529_;
}
else
{
lean_inc(v_a_6528_);
lean_dec(v___x_6515_);
v___x_6530_ = lean_box(0);
v_isShared_6531_ = v_isSharedCheck_6535_;
goto v_resetjp_6529_;
}
v_resetjp_6529_:
{
lean_object* v___x_6533_; 
if (v_isShared_6531_ == 0)
{
v___x_6533_ = v___x_6530_;
goto v_reusejp_6532_;
}
else
{
lean_object* v_reuseFailAlloc_6534_; 
v_reuseFailAlloc_6534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6534_, 0, v_a_6528_);
v___x_6533_ = v_reuseFailAlloc_6534_;
goto v_reusejp_6532_;
}
v_reusejp_6532_:
{
return v___x_6533_;
}
}
}
}
v_resetjp_6540_:
{
lean_object* v___x_6543_; lean_object* v_env_6544_; lean_object* v_nextMacroScope_6545_; lean_object* v_auxDeclNGen_6546_; lean_object* v_traceState_6547_; lean_object* v_cache_6548_; lean_object* v_messages_6549_; lean_object* v_infoState_6550_; lean_object* v_snapshotTasks_6551_; lean_object* v___x_6553_; uint8_t v_isShared_6554_; uint8_t v_isSharedCheck_6582_; 
v___x_6543_ = lean_st_ref_take(v_a_6511_);
v_env_6544_ = lean_ctor_get(v___x_6543_, 0);
v_nextMacroScope_6545_ = lean_ctor_get(v___x_6543_, 1);
v_auxDeclNGen_6546_ = lean_ctor_get(v___x_6543_, 3);
v_traceState_6547_ = lean_ctor_get(v___x_6543_, 4);
v_cache_6548_ = lean_ctor_get(v___x_6543_, 5);
v_messages_6549_ = lean_ctor_get(v___x_6543_, 6);
v_infoState_6550_ = lean_ctor_get(v___x_6543_, 7);
v_snapshotTasks_6551_ = lean_ctor_get(v___x_6543_, 8);
v_isSharedCheck_6582_ = !lean_is_exclusive(v___x_6543_);
if (v_isSharedCheck_6582_ == 0)
{
lean_object* v_unused_6583_; 
v_unused_6583_ = lean_ctor_get(v___x_6543_, 2);
lean_dec(v_unused_6583_);
v___x_6553_ = v___x_6543_;
v_isShared_6554_ = v_isSharedCheck_6582_;
goto v_resetjp_6552_;
}
else
{
lean_inc(v_snapshotTasks_6551_);
lean_inc(v_infoState_6550_);
lean_inc(v_messages_6549_);
lean_inc(v_cache_6548_);
lean_inc(v_traceState_6547_);
lean_inc(v_auxDeclNGen_6546_);
lean_inc(v_nextMacroScope_6545_);
lean_inc(v_env_6544_);
lean_dec(v___x_6543_);
v___x_6553_ = lean_box(0);
v_isShared_6554_ = v_isSharedCheck_6582_;
goto v_resetjp_6552_;
}
v_resetjp_6552_:
{
lean_object* v___x_6555_; lean_object* v___x_6556_; lean_object* v___x_6557_; lean_object* v___x_6559_; 
lean_inc(v_idx_6539_);
lean_inc(v_namePrefix_6538_);
v___x_6555_ = l_Lean_Name_num___override(v_namePrefix_6538_, v_idx_6539_);
v___x_6556_ = lean_unsigned_to_nat(1u);
v___x_6557_ = lean_nat_add(v_idx_6539_, v___x_6556_);
lean_dec(v_idx_6539_);
if (v_isShared_6542_ == 0)
{
lean_ctor_set(v___x_6541_, 1, v___x_6557_);
v___x_6559_ = v___x_6541_;
goto v_reusejp_6558_;
}
else
{
lean_object* v_reuseFailAlloc_6581_; 
v_reuseFailAlloc_6581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6581_, 0, v_namePrefix_6538_);
lean_ctor_set(v_reuseFailAlloc_6581_, 1, v___x_6557_);
v___x_6559_ = v_reuseFailAlloc_6581_;
goto v_reusejp_6558_;
}
v_reusejp_6558_:
{
lean_object* v___x_6561_; 
if (v_isShared_6554_ == 0)
{
lean_ctor_set(v___x_6553_, 2, v___x_6559_);
v___x_6561_ = v___x_6553_;
goto v_reusejp_6560_;
}
else
{
lean_object* v_reuseFailAlloc_6580_; 
v_reuseFailAlloc_6580_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6580_, 0, v_env_6544_);
lean_ctor_set(v_reuseFailAlloc_6580_, 1, v_nextMacroScope_6545_);
lean_ctor_set(v_reuseFailAlloc_6580_, 2, v___x_6559_);
lean_ctor_set(v_reuseFailAlloc_6580_, 3, v_auxDeclNGen_6546_);
lean_ctor_set(v_reuseFailAlloc_6580_, 4, v_traceState_6547_);
lean_ctor_set(v_reuseFailAlloc_6580_, 5, v_cache_6548_);
lean_ctor_set(v_reuseFailAlloc_6580_, 6, v_messages_6549_);
lean_ctor_set(v_reuseFailAlloc_6580_, 7, v_infoState_6550_);
lean_ctor_set(v_reuseFailAlloc_6580_, 8, v_snapshotTasks_6551_);
v___x_6561_ = v_reuseFailAlloc_6580_;
goto v_reusejp_6560_;
}
v_reusejp_6560_:
{
lean_object* v___x_6562_; lean_object* v___x_6563_; 
v___x_6562_ = lean_st_ref_set(v_a_6511_, v___x_6561_);
v___x_6563_ = lean_st_ref_get(v_ref_6502_);
if (lean_obj_tag(v___x_6563_) == 0)
{
lean_object* v_options_6564_; lean_object* v___x_6565_; lean_object* v___f_6566_; lean_object* v___x_6567_; lean_object* v___x_6568_; lean_object* v___x_6569_; 
v_options_6564_ = lean_ctor_get(v_a_6510_, 2);
v___x_6565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6565_, 0, v___x_6555_);
lean_ctor_set(v___x_6565_, 1, v___x_6556_);
lean_inc_ref(v_a_6510_);
v___f_6566_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_6566_, 0, v_a_6510_);
lean_closure_set(v___f_6566_, 1, v___x_6565_);
lean_closure_set(v___f_6566_, 2, v_addEntry_6503_);
lean_closure_set(v___f_6566_, 3, v_constantsPerTask_6505_);
lean_closure_set(v___f_6566_, 4, v_droppedEntriesRef_6506_);
lean_closure_set(v___f_6566_, 5, v_droppedKeys_6504_);
v___x_6567_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___closed__0));
v___x_6568_ = lean_box(0);
v___x_6569_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v___x_6567_, v_options_6564_, v___f_6566_, v___x_6568_, v_a_6508_, v_a_6509_, v_a_6510_, v_a_6511_);
if (lean_obj_tag(v___x_6569_) == 0)
{
lean_object* v_a_6570_; 
v_a_6570_ = lean_ctor_get(v___x_6569_, 0);
lean_inc(v_a_6570_);
lean_dec_ref_known(v___x_6569_, 1);
v_a_6514_ = v_a_6570_;
goto v___jp_6513_;
}
else
{
lean_object* v_a_6571_; lean_object* v___x_6573_; uint8_t v_isShared_6574_; uint8_t v_isSharedCheck_6578_; 
lean_dec_ref(v_ty_6507_);
v_a_6571_ = lean_ctor_get(v___x_6569_, 0);
v_isSharedCheck_6578_ = !lean_is_exclusive(v___x_6569_);
if (v_isSharedCheck_6578_ == 0)
{
v___x_6573_ = v___x_6569_;
v_isShared_6574_ = v_isSharedCheck_6578_;
goto v_resetjp_6572_;
}
else
{
lean_inc(v_a_6571_);
lean_dec(v___x_6569_);
v___x_6573_ = lean_box(0);
v_isShared_6574_ = v_isSharedCheck_6578_;
goto v_resetjp_6572_;
}
v_resetjp_6572_:
{
lean_object* v___x_6576_; 
if (v_isShared_6574_ == 0)
{
v___x_6576_ = v___x_6573_;
goto v_reusejp_6575_;
}
else
{
lean_object* v_reuseFailAlloc_6577_; 
v_reuseFailAlloc_6577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6577_, 0, v_a_6571_);
v___x_6576_ = v_reuseFailAlloc_6577_;
goto v_reusejp_6575_;
}
v_reusejp_6575_:
{
return v___x_6576_;
}
}
}
}
else
{
lean_object* v_val_6579_; 
lean_dec(v___x_6555_);
lean_dec(v_droppedEntriesRef_6506_);
lean_dec(v_constantsPerTask_6505_);
lean_dec(v_droppedKeys_6504_);
lean_dec_ref(v_addEntry_6503_);
v_val_6579_ = lean_ctor_get(v___x_6563_, 0);
lean_inc(v_val_6579_);
lean_dec_ref_known(v___x_6563_, 1);
v_a_6514_ = v_val_6579_;
goto v___jp_6513_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___boxed(lean_object* v_ref_6585_, lean_object* v_addEntry_6586_, lean_object* v_droppedKeys_6587_, lean_object* v_constantsPerTask_6588_, lean_object* v_droppedEntriesRef_6589_, lean_object* v_ty_6590_, lean_object* v_a_6591_, lean_object* v_a_6592_, lean_object* v_a_6593_, lean_object* v_a_6594_, lean_object* v_a_6595_){
_start:
{
lean_object* v_res_6596_; 
v_res_6596_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(v_ref_6585_, v_addEntry_6586_, v_droppedKeys_6587_, v_constantsPerTask_6588_, v_droppedEntriesRef_6589_, v_ty_6590_, v_a_6591_, v_a_6592_, v_a_6593_, v_a_6594_);
lean_dec(v_a_6594_);
lean_dec_ref(v_a_6593_);
lean_dec(v_a_6592_);
lean_dec_ref(v_a_6591_);
lean_dec(v_ref_6585_);
return v_res_6596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches(lean_object* v_00_u03b1_6597_, lean_object* v_ref_6598_, lean_object* v_addEntry_6599_, lean_object* v_droppedKeys_6600_, lean_object* v_constantsPerTask_6601_, lean_object* v_droppedEntriesRef_6602_, lean_object* v_ty_6603_, lean_object* v_a_6604_, lean_object* v_a_6605_, lean_object* v_a_6606_, lean_object* v_a_6607_){
_start:
{
lean_object* v___x_6609_; 
v___x_6609_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(v_ref_6598_, v_addEntry_6599_, v_droppedKeys_6600_, v_constantsPerTask_6601_, v_droppedEntriesRef_6602_, v_ty_6603_, v_a_6604_, v_a_6605_, v_a_6606_, v_a_6607_);
return v___x_6609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___boxed(lean_object* v_00_u03b1_6610_, lean_object* v_ref_6611_, lean_object* v_addEntry_6612_, lean_object* v_droppedKeys_6613_, lean_object* v_constantsPerTask_6614_, lean_object* v_droppedEntriesRef_6615_, lean_object* v_ty_6616_, lean_object* v_a_6617_, lean_object* v_a_6618_, lean_object* v_a_6619_, lean_object* v_a_6620_, lean_object* v_a_6621_){
_start:
{
lean_object* v_res_6622_; 
v_res_6622_ = l_Lean_Meta_LazyDiscrTree_findImportMatches(v_00_u03b1_6610_, v_ref_6611_, v_addEntry_6612_, v_droppedKeys_6613_, v_constantsPerTask_6614_, v_droppedEntriesRef_6615_, v_ty_6616_, v_a_6617_, v_a_6618_, v_a_6619_, v_a_6620_);
lean_dec(v_a_6620_);
lean_dec_ref(v_a_6619_);
lean_dec(v_a_6618_);
lean_dec_ref(v_a_6617_);
lean_dec(v_ref_6611_);
return v_res_6622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0(lean_object* v_00_u03b1_6623_, lean_object* v_cctx_6624_, lean_object* v_ngen_6625_, lean_object* v_env_6626_, lean_object* v_act_6627_, lean_object* v_constantsPerTask_6628_, lean_object* v___y_6629_, lean_object* v___y_6630_, lean_object* v___y_6631_, lean_object* v___y_6632_){
_start:
{
lean_object* v___x_6634_; 
v___x_6634_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(v_cctx_6624_, v_ngen_6625_, v_env_6626_, v_act_6627_, v_constantsPerTask_6628_, v___y_6629_, v___y_6630_, v___y_6631_, v___y_6632_);
return v___x_6634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___boxed(lean_object* v_00_u03b1_6635_, lean_object* v_cctx_6636_, lean_object* v_ngen_6637_, lean_object* v_env_6638_, lean_object* v_act_6639_, lean_object* v_constantsPerTask_6640_, lean_object* v___y_6641_, lean_object* v___y_6642_, lean_object* v___y_6643_, lean_object* v___y_6644_, lean_object* v___y_6645_){
_start:
{
lean_object* v_res_6646_; 
v_res_6646_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0(v_00_u03b1_6635_, v_cctx_6636_, v_ngen_6637_, v_env_6638_, v_act_6639_, v_constantsPerTask_6640_, v___y_6641_, v___y_6642_, v___y_6643_, v___y_6644_);
lean_dec(v___y_6644_);
lean_dec_ref(v___y_6643_);
lean_dec(v___y_6642_);
lean_dec_ref(v___y_6641_);
lean_dec(v_constantsPerTask_6640_);
return v_res_6646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1(lean_object* v_00_u03b1_6647_, lean_object* v_cctx_6648_, lean_object* v_env_6649_, lean_object* v_act_6650_, lean_object* v_constantsPerTask_6651_, lean_object* v_n_6652_, lean_object* v_ngen_6653_, lean_object* v_tasks_6654_, lean_object* v_start_6655_, lean_object* v_cnt_6656_, lean_object* v_idx_6657_, lean_object* v___y_6658_, lean_object* v___y_6659_, lean_object* v___y_6660_, lean_object* v___y_6661_){
_start:
{
lean_object* v___x_6663_; 
v___x_6663_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(v_cctx_6648_, v_env_6649_, v_act_6650_, v_constantsPerTask_6651_, v_n_6652_, v_ngen_6653_, v_tasks_6654_, v_start_6655_, v_cnt_6656_, v_idx_6657_);
return v___x_6663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___boxed(lean_object* v_00_u03b1_6664_, lean_object* v_cctx_6665_, lean_object* v_env_6666_, lean_object* v_act_6667_, lean_object* v_constantsPerTask_6668_, lean_object* v_n_6669_, lean_object* v_ngen_6670_, lean_object* v_tasks_6671_, lean_object* v_start_6672_, lean_object* v_cnt_6673_, lean_object* v_idx_6674_, lean_object* v___y_6675_, lean_object* v___y_6676_, lean_object* v___y_6677_, lean_object* v___y_6678_, lean_object* v___y_6679_){
_start:
{
lean_object* v_res_6680_; 
v_res_6680_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1(v_00_u03b1_6664_, v_cctx_6665_, v_env_6666_, v_act_6667_, v_constantsPerTask_6668_, v_n_6669_, v_ngen_6670_, v_tasks_6671_, v_start_6672_, v_cnt_6673_, v_idx_6674_, v___y_6675_, v___y_6676_, v___y_6677_, v___y_6678_);
lean_dec(v___y_6678_);
lean_dec_ref(v___y_6677_);
lean_dec(v___y_6676_);
lean_dec_ref(v___y_6675_);
lean_dec(v_constantsPerTask_6668_);
return v_res_6680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2(lean_object* v_00_u03b1_6681_, lean_object* v_z_6682_, lean_object* v_tasks_6683_){
_start:
{
lean_object* v___x_6684_; 
v___x_6684_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(v_z_6682_, v_tasks_6683_);
return v___x_6684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___boxed(lean_object* v_00_u03b1_6685_, lean_object* v_z_6686_, lean_object* v_tasks_6687_){
_start:
{
lean_object* v_res_6688_; 
v_res_6688_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2(v_00_u03b1_6685_, v_z_6686_, v_tasks_6687_);
lean_dec_ref(v_tasks_6687_);
return v_res_6688_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5(lean_object* v_00_u03b1_6689_, lean_object* v_as_6690_, size_t v_i_6691_, size_t v_stop_6692_, lean_object* v_b_6693_){
_start:
{
lean_object* v___x_6694_; 
v___x_6694_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(v_as_6690_, v_i_6691_, v_stop_6692_, v_b_6693_);
return v___x_6694_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b1_6695_, lean_object* v_as_6696_, lean_object* v_i_6697_, lean_object* v_stop_6698_, lean_object* v_b_6699_){
_start:
{
size_t v_i_boxed_6700_; size_t v_stop_boxed_6701_; lean_object* v_res_6702_; 
v_i_boxed_6700_ = lean_unbox_usize(v_i_6697_);
lean_dec(v_i_6697_);
v_stop_boxed_6701_ = lean_unbox_usize(v_stop_6698_);
lean_dec(v_stop_6698_);
v_res_6702_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5(v_00_u03b1_6695_, v_as_6696_, v_i_boxed_6700_, v_stop_boxed_6701_, v_b_6699_);
lean_dec_ref(v_as_6696_);
return v_res_6702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(lean_object* v___y_6703_){
_start:
{
lean_object* v___x_6705_; lean_object* v_ngen_6706_; lean_object* v_namePrefix_6707_; lean_object* v_idx_6708_; lean_object* v___x_6710_; uint8_t v_isShared_6711_; uint8_t v_isSharedCheck_6738_; 
v___x_6705_ = lean_st_ref_get(v___y_6703_);
v_ngen_6706_ = lean_ctor_get(v___x_6705_, 2);
lean_inc_ref(v_ngen_6706_);
lean_dec(v___x_6705_);
v_namePrefix_6707_ = lean_ctor_get(v_ngen_6706_, 0);
v_idx_6708_ = lean_ctor_get(v_ngen_6706_, 1);
v_isSharedCheck_6738_ = !lean_is_exclusive(v_ngen_6706_);
if (v_isSharedCheck_6738_ == 0)
{
v___x_6710_ = v_ngen_6706_;
v_isShared_6711_ = v_isSharedCheck_6738_;
goto v_resetjp_6709_;
}
else
{
lean_inc(v_idx_6708_);
lean_inc(v_namePrefix_6707_);
lean_dec(v_ngen_6706_);
v___x_6710_ = lean_box(0);
v_isShared_6711_ = v_isSharedCheck_6738_;
goto v_resetjp_6709_;
}
v_resetjp_6709_:
{
lean_object* v___x_6712_; lean_object* v_env_6713_; lean_object* v_nextMacroScope_6714_; lean_object* v_auxDeclNGen_6715_; lean_object* v_traceState_6716_; lean_object* v_cache_6717_; lean_object* v_messages_6718_; lean_object* v_infoState_6719_; lean_object* v_snapshotTasks_6720_; lean_object* v___x_6722_; uint8_t v_isShared_6723_; uint8_t v_isSharedCheck_6736_; 
v___x_6712_ = lean_st_ref_take(v___y_6703_);
v_env_6713_ = lean_ctor_get(v___x_6712_, 0);
v_nextMacroScope_6714_ = lean_ctor_get(v___x_6712_, 1);
v_auxDeclNGen_6715_ = lean_ctor_get(v___x_6712_, 3);
v_traceState_6716_ = lean_ctor_get(v___x_6712_, 4);
v_cache_6717_ = lean_ctor_get(v___x_6712_, 5);
v_messages_6718_ = lean_ctor_get(v___x_6712_, 6);
v_infoState_6719_ = lean_ctor_get(v___x_6712_, 7);
v_snapshotTasks_6720_ = lean_ctor_get(v___x_6712_, 8);
v_isSharedCheck_6736_ = !lean_is_exclusive(v___x_6712_);
if (v_isSharedCheck_6736_ == 0)
{
lean_object* v_unused_6737_; 
v_unused_6737_ = lean_ctor_get(v___x_6712_, 2);
lean_dec(v_unused_6737_);
v___x_6722_ = v___x_6712_;
v_isShared_6723_ = v_isSharedCheck_6736_;
goto v_resetjp_6721_;
}
else
{
lean_inc(v_snapshotTasks_6720_);
lean_inc(v_infoState_6719_);
lean_inc(v_messages_6718_);
lean_inc(v_cache_6717_);
lean_inc(v_traceState_6716_);
lean_inc(v_auxDeclNGen_6715_);
lean_inc(v_nextMacroScope_6714_);
lean_inc(v_env_6713_);
lean_dec(v___x_6712_);
v___x_6722_ = lean_box(0);
v_isShared_6723_ = v_isSharedCheck_6736_;
goto v_resetjp_6721_;
}
v_resetjp_6721_:
{
lean_object* v___x_6724_; lean_object* v___x_6725_; lean_object* v___x_6726_; lean_object* v___x_6728_; 
lean_inc(v_idx_6708_);
lean_inc(v_namePrefix_6707_);
v___x_6724_ = l_Lean_Name_num___override(v_namePrefix_6707_, v_idx_6708_);
v___x_6725_ = lean_unsigned_to_nat(1u);
v___x_6726_ = lean_nat_add(v_idx_6708_, v___x_6725_);
lean_dec(v_idx_6708_);
if (v_isShared_6711_ == 0)
{
lean_ctor_set(v___x_6710_, 1, v___x_6726_);
v___x_6728_ = v___x_6710_;
goto v_reusejp_6727_;
}
else
{
lean_object* v_reuseFailAlloc_6735_; 
v_reuseFailAlloc_6735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6735_, 0, v_namePrefix_6707_);
lean_ctor_set(v_reuseFailAlloc_6735_, 1, v___x_6726_);
v___x_6728_ = v_reuseFailAlloc_6735_;
goto v_reusejp_6727_;
}
v_reusejp_6727_:
{
lean_object* v___x_6730_; 
if (v_isShared_6723_ == 0)
{
lean_ctor_set(v___x_6722_, 2, v___x_6728_);
v___x_6730_ = v___x_6722_;
goto v_reusejp_6729_;
}
else
{
lean_object* v_reuseFailAlloc_6734_; 
v_reuseFailAlloc_6734_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6734_, 0, v_env_6713_);
lean_ctor_set(v_reuseFailAlloc_6734_, 1, v_nextMacroScope_6714_);
lean_ctor_set(v_reuseFailAlloc_6734_, 2, v___x_6728_);
lean_ctor_set(v_reuseFailAlloc_6734_, 3, v_auxDeclNGen_6715_);
lean_ctor_set(v_reuseFailAlloc_6734_, 4, v_traceState_6716_);
lean_ctor_set(v_reuseFailAlloc_6734_, 5, v_cache_6717_);
lean_ctor_set(v_reuseFailAlloc_6734_, 6, v_messages_6718_);
lean_ctor_set(v_reuseFailAlloc_6734_, 7, v_infoState_6719_);
lean_ctor_set(v_reuseFailAlloc_6734_, 8, v_snapshotTasks_6720_);
v___x_6730_ = v_reuseFailAlloc_6734_;
goto v_reusejp_6729_;
}
v_reusejp_6729_:
{
lean_object* v___x_6731_; lean_object* v___x_6732_; lean_object* v___x_6733_; 
v___x_6731_ = lean_st_ref_set(v___y_6703_, v___x_6730_);
v___x_6732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6732_, 0, v___x_6724_);
lean_ctor_set(v___x_6732_, 1, v___x_6725_);
v___x_6733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6733_, 0, v___x_6732_);
return v___x_6733_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg___boxed(lean_object* v___y_6739_, lean_object* v___y_6740_){
_start:
{
lean_object* v_res_6741_; 
v_res_6741_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(v___y_6739_);
lean_dec(v___y_6739_);
return v_res_6741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1(lean_object* v___y_6742_, lean_object* v___y_6743_){
_start:
{
lean_object* v___x_6745_; 
v___x_6745_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(v___y_6743_);
return v___x_6745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___boxed(lean_object* v___y_6746_, lean_object* v___y_6747_, lean_object* v___y_6748_){
_start:
{
lean_object* v_res_6749_; 
v_res_6749_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1(v___y_6746_, v___y_6747_);
lean_dec(v___y_6747_);
lean_dec_ref(v___y_6746_);
return v_res_6749_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0(void){
_start:
{
lean_object* v___x_6750_; lean_object* v___x_6751_; lean_object* v___x_6752_; 
v___x_6750_ = lean_unsigned_to_nat(32u);
v___x_6751_ = lean_mk_empty_array_with_capacity(v___x_6750_);
v___x_6752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6752_, 0, v___x_6751_);
return v___x_6752_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1(void){
_start:
{
size_t v___x_6753_; lean_object* v___x_6754_; lean_object* v___x_6755_; lean_object* v___x_6756_; lean_object* v___x_6757_; lean_object* v___x_6758_; 
v___x_6753_ = ((size_t)5ULL);
v___x_6754_ = lean_unsigned_to_nat(0u);
v___x_6755_ = lean_unsigned_to_nat(32u);
v___x_6756_ = lean_mk_empty_array_with_capacity(v___x_6755_);
v___x_6757_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0);
v___x_6758_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_6758_, 0, v___x_6757_);
lean_ctor_set(v___x_6758_, 1, v___x_6756_);
lean_ctor_set(v___x_6758_, 2, v___x_6754_);
lean_ctor_set(v___x_6758_, 3, v___x_6754_);
lean_ctor_set_usize(v___x_6758_, 4, v___x_6753_);
return v___x_6758_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2(void){
_start:
{
lean_object* v___x_6759_; lean_object* v___x_6760_; lean_object* v___x_6761_; lean_object* v___x_6762_; 
v___x_6759_ = lean_box(1);
v___x_6760_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1);
v___x_6761_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_6762_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6762_, 0, v___x_6761_);
lean_ctor_set(v___x_6762_, 1, v___x_6760_);
lean_ctor_set(v___x_6762_, 2, v___x_6759_);
return v___x_6762_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_msgData_6763_, lean_object* v___y_6764_, lean_object* v___y_6765_){
_start:
{
lean_object* v___x_6767_; lean_object* v_env_6768_; lean_object* v_options_6769_; lean_object* v___x_6770_; lean_object* v___x_6771_; lean_object* v___x_6772_; lean_object* v___x_6773_; lean_object* v___x_6774_; 
v___x_6767_ = lean_st_ref_get(v___y_6765_);
v_env_6768_ = lean_ctor_get(v___x_6767_, 0);
lean_inc_ref(v_env_6768_);
lean_dec(v___x_6767_);
v_options_6769_ = lean_ctor_get(v___y_6764_, 2);
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
lean_ctor_set(v___x_6773_, 1, v_msgData_6763_);
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
lean_object* v___y_6788_; lean_object* v___y_6789_; lean_object* v___y_6790_; uint8_t v___y_6791_; uint8_t v___y_6792_; lean_object* v___y_6793_; lean_object* v___y_6794_; lean_object* v___y_6795_; lean_object* v___y_6796_; lean_object* v___y_6824_; lean_object* v___y_6825_; lean_object* v___y_6826_; uint8_t v___y_6827_; uint8_t v___y_6828_; uint8_t v___y_6829_; lean_object* v___y_6830_; lean_object* v___y_6831_; lean_object* v___y_6849_; lean_object* v___y_6850_; uint8_t v___y_6851_; uint8_t v___y_6852_; uint8_t v___y_6853_; lean_object* v___y_6854_; lean_object* v___y_6855_; lean_object* v___y_6856_; lean_object* v___y_6860_; lean_object* v___y_6861_; uint8_t v___y_6862_; lean_object* v___y_6863_; uint8_t v___y_6864_; lean_object* v___y_6865_; uint8_t v___y_6866_; uint8_t v___x_6871_; lean_object* v___y_6873_; lean_object* v___y_6874_; uint8_t v___y_6875_; lean_object* v___y_6876_; lean_object* v___y_6877_; uint8_t v___y_6878_; uint8_t v___y_6879_; uint8_t v___y_6881_; uint8_t v___x_6896_; 
v___x_6871_ = 2;
v___x_6896_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6782_, v___x_6871_);
if (v___x_6896_ == 0)
{
v___y_6881_ = v___x_6896_;
goto v___jp_6880_;
}
else
{
uint8_t v___x_6897_; 
lean_inc_ref(v_msgData_6781_);
v___x_6897_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_6781_);
v___y_6881_ = v___x_6897_;
goto v___jp_6880_;
}
v___jp_6787_:
{
lean_object* v___x_6797_; lean_object* v_currNamespace_6798_; lean_object* v_openDecls_6799_; lean_object* v_env_6800_; lean_object* v_nextMacroScope_6801_; lean_object* v_ngen_6802_; lean_object* v_auxDeclNGen_6803_; lean_object* v_traceState_6804_; lean_object* v_cache_6805_; lean_object* v_messages_6806_; lean_object* v_infoState_6807_; lean_object* v_snapshotTasks_6808_; lean_object* v___x_6810_; uint8_t v_isShared_6811_; uint8_t v_isSharedCheck_6822_; 
v___x_6797_ = lean_st_ref_take(v___y_6796_);
v_currNamespace_6798_ = lean_ctor_get(v___y_6795_, 6);
v_openDecls_6799_ = lean_ctor_get(v___y_6795_, 7);
v_env_6800_ = lean_ctor_get(v___x_6797_, 0);
v_nextMacroScope_6801_ = lean_ctor_get(v___x_6797_, 1);
v_ngen_6802_ = lean_ctor_get(v___x_6797_, 2);
v_auxDeclNGen_6803_ = lean_ctor_get(v___x_6797_, 3);
v_traceState_6804_ = lean_ctor_get(v___x_6797_, 4);
v_cache_6805_ = lean_ctor_get(v___x_6797_, 5);
v_messages_6806_ = lean_ctor_get(v___x_6797_, 6);
v_infoState_6807_ = lean_ctor_get(v___x_6797_, 7);
v_snapshotTasks_6808_ = lean_ctor_get(v___x_6797_, 8);
v_isSharedCheck_6822_ = !lean_is_exclusive(v___x_6797_);
if (v_isSharedCheck_6822_ == 0)
{
v___x_6810_ = v___x_6797_;
v_isShared_6811_ = v_isSharedCheck_6822_;
goto v_resetjp_6809_;
}
else
{
lean_inc(v_snapshotTasks_6808_);
lean_inc(v_infoState_6807_);
lean_inc(v_messages_6806_);
lean_inc(v_cache_6805_);
lean_inc(v_traceState_6804_);
lean_inc(v_auxDeclNGen_6803_);
lean_inc(v_ngen_6802_);
lean_inc(v_nextMacroScope_6801_);
lean_inc(v_env_6800_);
lean_dec(v___x_6797_);
v___x_6810_ = lean_box(0);
v_isShared_6811_ = v_isSharedCheck_6822_;
goto v_resetjp_6809_;
}
v_resetjp_6809_:
{
lean_object* v___x_6812_; lean_object* v___x_6813_; lean_object* v___x_6814_; lean_object* v___x_6815_; lean_object* v___x_6817_; 
lean_inc(v_openDecls_6799_);
lean_inc(v_currNamespace_6798_);
v___x_6812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6812_, 0, v_currNamespace_6798_);
lean_ctor_set(v___x_6812_, 1, v_openDecls_6799_);
v___x_6813_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6813_, 0, v___x_6812_);
lean_ctor_set(v___x_6813_, 1, v___y_6789_);
lean_inc_ref(v___y_6793_);
lean_inc_ref(v___y_6794_);
v___x_6814_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_6814_, 0, v___y_6794_);
lean_ctor_set(v___x_6814_, 1, v___y_6790_);
lean_ctor_set(v___x_6814_, 2, v___y_6788_);
lean_ctor_set(v___x_6814_, 3, v___y_6793_);
lean_ctor_set(v___x_6814_, 4, v___x_6813_);
lean_ctor_set_uint8(v___x_6814_, sizeof(void*)*5, v___y_6792_);
lean_ctor_set_uint8(v___x_6814_, sizeof(void*)*5 + 1, v___y_6791_);
lean_ctor_set_uint8(v___x_6814_, sizeof(void*)*5 + 2, v_isSilent_6783_);
v___x_6815_ = l_Lean_MessageLog_add(v___x_6814_, v_messages_6806_);
if (v_isShared_6811_ == 0)
{
lean_ctor_set(v___x_6810_, 6, v___x_6815_);
v___x_6817_ = v___x_6810_;
goto v_reusejp_6816_;
}
else
{
lean_object* v_reuseFailAlloc_6821_; 
v_reuseFailAlloc_6821_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6821_, 0, v_env_6800_);
lean_ctor_set(v_reuseFailAlloc_6821_, 1, v_nextMacroScope_6801_);
lean_ctor_set(v_reuseFailAlloc_6821_, 2, v_ngen_6802_);
lean_ctor_set(v_reuseFailAlloc_6821_, 3, v_auxDeclNGen_6803_);
lean_ctor_set(v_reuseFailAlloc_6821_, 4, v_traceState_6804_);
lean_ctor_set(v_reuseFailAlloc_6821_, 5, v_cache_6805_);
lean_ctor_set(v_reuseFailAlloc_6821_, 6, v___x_6815_);
lean_ctor_set(v_reuseFailAlloc_6821_, 7, v_infoState_6807_);
lean_ctor_set(v_reuseFailAlloc_6821_, 8, v_snapshotTasks_6808_);
v___x_6817_ = v_reuseFailAlloc_6821_;
goto v_reusejp_6816_;
}
v_reusejp_6816_:
{
lean_object* v___x_6818_; lean_object* v___x_6819_; lean_object* v___x_6820_; 
v___x_6818_ = lean_st_ref_set(v___y_6796_, v___x_6817_);
v___x_6819_ = lean_box(0);
v___x_6820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6820_, 0, v___x_6819_);
return v___x_6820_;
}
}
}
v___jp_6823_:
{
lean_object* v___x_6832_; lean_object* v___x_6833_; lean_object* v_a_6834_; lean_object* v___x_6836_; uint8_t v_isShared_6837_; uint8_t v_isSharedCheck_6847_; 
v___x_6832_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_6781_);
v___x_6833_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5(v___x_6832_, v___y_6784_, v___y_6785_);
v_a_6834_ = lean_ctor_get(v___x_6833_, 0);
v_isSharedCheck_6847_ = !lean_is_exclusive(v___x_6833_);
if (v_isSharedCheck_6847_ == 0)
{
v___x_6836_ = v___x_6833_;
v_isShared_6837_ = v_isSharedCheck_6847_;
goto v_resetjp_6835_;
}
else
{
lean_inc(v_a_6834_);
lean_dec(v___x_6833_);
v___x_6836_ = lean_box(0);
v_isShared_6837_ = v_isSharedCheck_6847_;
goto v_resetjp_6835_;
}
v_resetjp_6835_:
{
lean_object* v___x_6838_; lean_object* v___x_6839_; lean_object* v___x_6840_; lean_object* v___x_6841_; 
lean_inc_ref_n(v___y_6826_, 2);
v___x_6838_ = l_Lean_FileMap_toPosition(v___y_6826_, v___y_6825_);
lean_dec(v___y_6825_);
v___x_6839_ = l_Lean_FileMap_toPosition(v___y_6826_, v___y_6831_);
lean_dec(v___y_6831_);
v___x_6840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6840_, 0, v___x_6839_);
v___x_6841_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___closed__0));
if (v___y_6827_ == 0)
{
lean_del_object(v___x_6836_);
lean_dec_ref(v___y_6824_);
v___y_6788_ = v___x_6840_;
v___y_6789_ = v_a_6834_;
v___y_6790_ = v___x_6838_;
v___y_6791_ = v___y_6828_;
v___y_6792_ = v___y_6829_;
v___y_6793_ = v___x_6841_;
v___y_6794_ = v___y_6830_;
v___y_6795_ = v___y_6784_;
v___y_6796_ = v___y_6785_;
goto v___jp_6787_;
}
else
{
uint8_t v___x_6842_; 
lean_inc(v_a_6834_);
v___x_6842_ = l_Lean_MessageData_hasTag(v___y_6824_, v_a_6834_);
if (v___x_6842_ == 0)
{
lean_object* v___x_6843_; lean_object* v___x_6845_; 
lean_dec_ref_known(v___x_6840_, 1);
lean_dec_ref(v___x_6838_);
lean_dec(v_a_6834_);
v___x_6843_ = lean_box(0);
if (v_isShared_6837_ == 0)
{
lean_ctor_set(v___x_6836_, 0, v___x_6843_);
v___x_6845_ = v___x_6836_;
goto v_reusejp_6844_;
}
else
{
lean_object* v_reuseFailAlloc_6846_; 
v_reuseFailAlloc_6846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6846_, 0, v___x_6843_);
v___x_6845_ = v_reuseFailAlloc_6846_;
goto v_reusejp_6844_;
}
v_reusejp_6844_:
{
return v___x_6845_;
}
}
else
{
lean_del_object(v___x_6836_);
v___y_6788_ = v___x_6840_;
v___y_6789_ = v_a_6834_;
v___y_6790_ = v___x_6838_;
v___y_6791_ = v___y_6828_;
v___y_6792_ = v___y_6829_;
v___y_6793_ = v___x_6841_;
v___y_6794_ = v___y_6830_;
v___y_6795_ = v___y_6784_;
v___y_6796_ = v___y_6785_;
goto v___jp_6787_;
}
}
}
}
v___jp_6848_:
{
lean_object* v___x_6857_; 
v___x_6857_ = l_Lean_Syntax_getTailPos_x3f(v___y_6854_, v___y_6853_);
lean_dec(v___y_6854_);
if (lean_obj_tag(v___x_6857_) == 0)
{
lean_inc(v___y_6856_);
v___y_6824_ = v___y_6849_;
v___y_6825_ = v___y_6856_;
v___y_6826_ = v___y_6850_;
v___y_6827_ = v___y_6851_;
v___y_6828_ = v___y_6852_;
v___y_6829_ = v___y_6853_;
v___y_6830_ = v___y_6855_;
v___y_6831_ = v___y_6856_;
goto v___jp_6823_;
}
else
{
lean_object* v_val_6858_; 
v_val_6858_ = lean_ctor_get(v___x_6857_, 0);
lean_inc(v_val_6858_);
lean_dec_ref_known(v___x_6857_, 1);
v___y_6824_ = v___y_6849_;
v___y_6825_ = v___y_6856_;
v___y_6826_ = v___y_6850_;
v___y_6827_ = v___y_6851_;
v___y_6828_ = v___y_6852_;
v___y_6829_ = v___y_6853_;
v___y_6830_ = v___y_6855_;
v___y_6831_ = v_val_6858_;
goto v___jp_6823_;
}
}
v___jp_6859_:
{
lean_object* v_ref_6867_; lean_object* v___x_6868_; 
v_ref_6867_ = l_Lean_replaceRef(v_ref_6780_, v___y_6863_);
v___x_6868_ = l_Lean_Syntax_getPos_x3f(v_ref_6867_, v___y_6864_);
if (lean_obj_tag(v___x_6868_) == 0)
{
lean_object* v___x_6869_; 
v___x_6869_ = lean_unsigned_to_nat(0u);
v___y_6849_ = v___y_6860_;
v___y_6850_ = v___y_6861_;
v___y_6851_ = v___y_6862_;
v___y_6852_ = v___y_6866_;
v___y_6853_ = v___y_6864_;
v___y_6854_ = v_ref_6867_;
v___y_6855_ = v___y_6865_;
v___y_6856_ = v___x_6869_;
goto v___jp_6848_;
}
else
{
lean_object* v_val_6870_; 
v_val_6870_ = lean_ctor_get(v___x_6868_, 0);
lean_inc(v_val_6870_);
lean_dec_ref_known(v___x_6868_, 1);
v___y_6849_ = v___y_6860_;
v___y_6850_ = v___y_6861_;
v___y_6851_ = v___y_6862_;
v___y_6852_ = v___y_6866_;
v___y_6853_ = v___y_6864_;
v___y_6854_ = v_ref_6867_;
v___y_6855_ = v___y_6865_;
v___y_6856_ = v_val_6870_;
goto v___jp_6848_;
}
}
v___jp_6872_:
{
if (v___y_6879_ == 0)
{
v___y_6860_ = v___y_6874_;
v___y_6861_ = v___y_6873_;
v___y_6862_ = v___y_6875_;
v___y_6863_ = v___y_6876_;
v___y_6864_ = v___y_6878_;
v___y_6865_ = v___y_6877_;
v___y_6866_ = v_severity_6782_;
goto v___jp_6859_;
}
else
{
v___y_6860_ = v___y_6874_;
v___y_6861_ = v___y_6873_;
v___y_6862_ = v___y_6875_;
v___y_6863_ = v___y_6876_;
v___y_6864_ = v___y_6878_;
v___y_6865_ = v___y_6877_;
v___y_6866_ = v___x_6871_;
goto v___jp_6859_;
}
}
v___jp_6880_:
{
if (v___y_6881_ == 0)
{
lean_object* v_fileName_6882_; lean_object* v_fileMap_6883_; lean_object* v_options_6884_; lean_object* v_ref_6885_; uint8_t v_suppressElabErrors_6886_; lean_object* v___x_6887_; lean_object* v___x_6888_; lean_object* v___f_6889_; uint8_t v___x_6890_; uint8_t v___x_6891_; 
v_fileName_6882_ = lean_ctor_get(v___y_6784_, 0);
v_fileMap_6883_ = lean_ctor_get(v___y_6784_, 1);
v_options_6884_ = lean_ctor_get(v___y_6784_, 2);
v_ref_6885_ = lean_ctor_get(v___y_6784_, 5);
v_suppressElabErrors_6886_ = lean_ctor_get_uint8(v___y_6784_, sizeof(void*)*14 + 1);
v___x_6887_ = lean_box(v___y_6881_);
v___x_6888_ = lean_box(v_suppressElabErrors_6886_);
v___f_6889_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_6889_, 0, v___x_6887_);
lean_closure_set(v___f_6889_, 1, v___x_6888_);
v___x_6890_ = 1;
v___x_6891_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6782_, v___x_6890_);
if (v___x_6891_ == 0)
{
v___y_6873_ = v_fileMap_6883_;
v___y_6874_ = v___f_6889_;
v___y_6875_ = v_suppressElabErrors_6886_;
v___y_6876_ = v_ref_6885_;
v___y_6877_ = v_fileName_6882_;
v___y_6878_ = v___y_6881_;
v___y_6879_ = v___x_6891_;
goto v___jp_6872_;
}
else
{
lean_object* v___x_6892_; uint8_t v___x_6893_; 
v___x_6892_ = l_Lean_warningAsError;
v___x_6893_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(v_options_6884_, v___x_6892_);
v___y_6873_ = v_fileMap_6883_;
v___y_6874_ = v___f_6889_;
v___y_6875_ = v_suppressElabErrors_6886_;
v___y_6876_ = v_ref_6885_;
v___y_6877_ = v_fileName_6882_;
v___y_6878_ = v___y_6881_;
v___y_6879_ = v___x_6893_;
goto v___jp_6872_;
}
}
else
{
lean_object* v___x_6894_; lean_object* v___x_6895_; 
lean_dec_ref(v_msgData_6781_);
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
v_ref_6914_ = lean_ctor_get(v___y_6911_, 5);
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
v___x_7072_ = lean_st_ref_set(v_val_7058_, v___x_7071_);
lean_dec(v_val_7058_);
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
lean_object* v_options_7122_; lean_object* v___f_7123_; lean_object* v___x_7124_; lean_object* v___x_7125_; lean_object* v___x_7126_; 
v_options_7122_ = lean_ctor_get(v_a_7119_, 2);
v___f_7123_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_7123_, 0, v_entriesForConst_7114_);
lean_closure_set(v___f_7123_, 1, v_droppedEntriesRef_7116_);
lean_closure_set(v___f_7123_, 2, v_droppedKeys_7115_);
v___x_7124_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___closed__0));
v___x_7125_ = lean_box(0);
v___x_7126_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v___x_7124_, v_options_7122_, v___f_7123_, v___x_7125_, v_a_7117_, v_a_7118_, v_a_7119_, v_a_7120_);
return v___x_7126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___boxed(lean_object* v_entriesForConst_7127_, lean_object* v_droppedKeys_7128_, lean_object* v_droppedEntriesRef_7129_, lean_object* v_a_7130_, lean_object* v_a_7131_, lean_object* v_a_7132_, lean_object* v_a_7133_, lean_object* v_a_7134_){
_start:
{
lean_object* v_res_7135_; 
v_res_7135_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v_entriesForConst_7127_, v_droppedKeys_7128_, v_droppedEntriesRef_7129_, v_a_7130_, v_a_7131_, v_a_7132_, v_a_7133_);
lean_dec(v_a_7133_);
lean_dec_ref(v_a_7132_);
lean_dec(v_a_7131_);
lean_dec_ref(v_a_7130_);
return v_res_7135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef(lean_object* v_00_u03b1_7136_, lean_object* v_entriesForConst_7137_, lean_object* v_droppedKeys_7138_, lean_object* v_droppedEntriesRef_7139_, lean_object* v_a_7140_, lean_object* v_a_7141_, lean_object* v_a_7142_, lean_object* v_a_7143_){
_start:
{
lean_object* v___x_7145_; 
v___x_7145_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v_entriesForConst_7137_, v_droppedKeys_7138_, v_droppedEntriesRef_7139_, v_a_7140_, v_a_7141_, v_a_7142_, v_a_7143_);
return v___x_7145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___boxed(lean_object* v_00_u03b1_7146_, lean_object* v_entriesForConst_7147_, lean_object* v_droppedKeys_7148_, lean_object* v_droppedEntriesRef_7149_, lean_object* v_a_7150_, lean_object* v_a_7151_, lean_object* v_a_7152_, lean_object* v_a_7153_, lean_object* v_a_7154_){
_start:
{
lean_object* v_res_7155_; 
v_res_7155_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef(v_00_u03b1_7146_, v_entriesForConst_7147_, v_droppedKeys_7148_, v_droppedEntriesRef_7149_, v_a_7150_, v_a_7151_, v_a_7152_, v_a_7153_);
lean_dec(v_a_7153_);
lean_dec_ref(v_a_7152_);
lean_dec(v_a_7151_);
lean_dec_ref(v_a_7150_);
return v_res_7155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0(lean_object* v_moduleRef_7156_, lean_object* v_ty_7157_, lean_object* v___y_7158_, lean_object* v___y_7159_, lean_object* v___y_7160_, lean_object* v___y_7161_){
_start:
{
lean_object* v___x_7163_; lean_object* v___x_7164_; 
v___x_7163_ = lean_st_ref_get(v_moduleRef_7156_);
v___x_7164_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v___x_7163_, v_ty_7157_, v___y_7158_, v___y_7159_, v___y_7160_, v___y_7161_);
if (lean_obj_tag(v___x_7164_) == 0)
{
lean_object* v_a_7165_; lean_object* v___x_7167_; uint8_t v_isShared_7168_; uint8_t v_isSharedCheck_7175_; 
v_a_7165_ = lean_ctor_get(v___x_7164_, 0);
v_isSharedCheck_7175_ = !lean_is_exclusive(v___x_7164_);
if (v_isSharedCheck_7175_ == 0)
{
v___x_7167_ = v___x_7164_;
v_isShared_7168_ = v_isSharedCheck_7175_;
goto v_resetjp_7166_;
}
else
{
lean_inc(v_a_7165_);
lean_dec(v___x_7164_);
v___x_7167_ = lean_box(0);
v_isShared_7168_ = v_isSharedCheck_7175_;
goto v_resetjp_7166_;
}
v_resetjp_7166_:
{
lean_object* v_fst_7169_; lean_object* v_snd_7170_; lean_object* v___x_7171_; lean_object* v___x_7173_; 
v_fst_7169_ = lean_ctor_get(v_a_7165_, 0);
lean_inc(v_fst_7169_);
v_snd_7170_ = lean_ctor_get(v_a_7165_, 1);
lean_inc(v_snd_7170_);
lean_dec(v_a_7165_);
v___x_7171_ = lean_st_ref_set(v_moduleRef_7156_, v_snd_7170_);
if (v_isShared_7168_ == 0)
{
lean_ctor_set(v___x_7167_, 0, v_fst_7169_);
v___x_7173_ = v___x_7167_;
goto v_reusejp_7172_;
}
else
{
lean_object* v_reuseFailAlloc_7174_; 
v_reuseFailAlloc_7174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7174_, 0, v_fst_7169_);
v___x_7173_ = v_reuseFailAlloc_7174_;
goto v_reusejp_7172_;
}
v_reusejp_7172_:
{
return v___x_7173_;
}
}
}
else
{
lean_object* v_a_7176_; lean_object* v___x_7178_; uint8_t v_isShared_7179_; uint8_t v_isSharedCheck_7183_; 
v_a_7176_ = lean_ctor_get(v___x_7164_, 0);
v_isSharedCheck_7183_ = !lean_is_exclusive(v___x_7164_);
if (v_isSharedCheck_7183_ == 0)
{
v___x_7178_ = v___x_7164_;
v_isShared_7179_ = v_isSharedCheck_7183_;
goto v_resetjp_7177_;
}
else
{
lean_inc(v_a_7176_);
lean_dec(v___x_7164_);
v___x_7178_ = lean_box(0);
v_isShared_7179_ = v_isSharedCheck_7183_;
goto v_resetjp_7177_;
}
v_resetjp_7177_:
{
lean_object* v___x_7181_; 
if (v_isShared_7179_ == 0)
{
v___x_7181_ = v___x_7178_;
goto v_reusejp_7180_;
}
else
{
lean_object* v_reuseFailAlloc_7182_; 
v_reuseFailAlloc_7182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7182_, 0, v_a_7176_);
v___x_7181_ = v_reuseFailAlloc_7182_;
goto v_reusejp_7180_;
}
v_reusejp_7180_:
{
return v___x_7181_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0___boxed(lean_object* v_moduleRef_7184_, lean_object* v_ty_7185_, lean_object* v___y_7186_, lean_object* v___y_7187_, lean_object* v___y_7188_, lean_object* v___y_7189_, lean_object* v___y_7190_){
_start:
{
lean_object* v_res_7191_; 
v_res_7191_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0(v_moduleRef_7184_, v_ty_7185_, v___y_7186_, v___y_7187_, v___y_7188_, v___y_7189_);
lean_dec(v___y_7189_);
lean_dec_ref(v___y_7188_);
lean_dec(v___y_7187_);
lean_dec_ref(v___y_7186_);
lean_dec(v_moduleRef_7184_);
return v_res_7191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(lean_object* v_moduleRef_7193_, lean_object* v_ty_7194_, lean_object* v_a_7195_, lean_object* v_a_7196_, lean_object* v_a_7197_, lean_object* v_a_7198_){
_start:
{
lean_object* v_options_7200_; lean_object* v___f_7201_; lean_object* v___x_7202_; lean_object* v___x_7203_; lean_object* v___x_7204_; 
v_options_7200_ = lean_ctor_get(v_a_7197_, 2);
v___f_7201_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_7201_, 0, v_moduleRef_7193_);
lean_closure_set(v___f_7201_, 1, v_ty_7194_);
v___x_7202_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___closed__0));
v___x_7203_ = lean_box(0);
v___x_7204_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v___x_7202_, v_options_7200_, v___f_7201_, v___x_7203_, v_a_7195_, v_a_7196_, v_a_7197_, v_a_7198_);
return v___x_7204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___boxed(lean_object* v_moduleRef_7205_, lean_object* v_ty_7206_, lean_object* v_a_7207_, lean_object* v_a_7208_, lean_object* v_a_7209_, lean_object* v_a_7210_, lean_object* v_a_7211_){
_start:
{
lean_object* v_res_7212_; 
v_res_7212_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(v_moduleRef_7205_, v_ty_7206_, v_a_7207_, v_a_7208_, v_a_7209_, v_a_7210_);
lean_dec(v_a_7210_);
lean_dec_ref(v_a_7209_);
lean_dec(v_a_7208_);
lean_dec_ref(v_a_7207_);
return v_res_7212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches(lean_object* v_00_u03b1_7213_, lean_object* v_moduleRef_7214_, lean_object* v_ty_7215_, lean_object* v_a_7216_, lean_object* v_a_7217_, lean_object* v_a_7218_, lean_object* v_a_7219_){
_start:
{
lean_object* v___x_7221_; 
v___x_7221_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(v_moduleRef_7214_, v_ty_7215_, v_a_7216_, v_a_7217_, v_a_7218_, v_a_7219_);
return v___x_7221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___boxed(lean_object* v_00_u03b1_7222_, lean_object* v_moduleRef_7223_, lean_object* v_ty_7224_, lean_object* v_a_7225_, lean_object* v_a_7226_, lean_object* v_a_7227_, lean_object* v_a_7228_, lean_object* v_a_7229_){
_start:
{
lean_object* v_res_7230_; 
v_res_7230_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches(v_00_u03b1_7222_, v_moduleRef_7223_, v_ty_7224_, v_a_7225_, v_a_7226_, v_a_7227_, v_a_7228_);
lean_dec(v_a_7228_);
lean_dec_ref(v_a_7227_);
lean_dec(v_a_7226_);
lean_dec_ref(v_a_7225_);
return v_res_7230_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(lean_object* v_adjustResult_7231_, lean_object* v_j_7232_, size_t v_sz_7233_, size_t v_i_7234_, lean_object* v_bs_7235_){
_start:
{
uint8_t v___x_7236_; 
v___x_7236_ = lean_usize_dec_lt(v_i_7234_, v_sz_7233_);
if (v___x_7236_ == 0)
{
lean_dec(v_j_7232_);
lean_dec(v_adjustResult_7231_);
return v_bs_7235_;
}
else
{
lean_object* v_v_7237_; lean_object* v___x_7238_; lean_object* v_bs_x27_7239_; lean_object* v___x_7240_; size_t v___x_7241_; size_t v___x_7242_; lean_object* v___x_7243_; 
v_v_7237_ = lean_array_uget(v_bs_7235_, v_i_7234_);
v___x_7238_ = lean_unsigned_to_nat(0u);
v_bs_x27_7239_ = lean_array_uset(v_bs_7235_, v_i_7234_, v___x_7238_);
lean_inc(v_adjustResult_7231_);
lean_inc(v_j_7232_);
v___x_7240_ = lean_apply_2(v_adjustResult_7231_, v_j_7232_, v_v_7237_);
v___x_7241_ = ((size_t)1ULL);
v___x_7242_ = lean_usize_add(v_i_7234_, v___x_7241_);
v___x_7243_ = lean_array_uset(v_bs_x27_7239_, v_i_7234_, v___x_7240_);
v_i_7234_ = v___x_7242_;
v_bs_7235_ = v___x_7243_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg___boxed(lean_object* v_adjustResult_7245_, lean_object* v_j_7246_, lean_object* v_sz_7247_, lean_object* v_i_7248_, lean_object* v_bs_7249_){
_start:
{
size_t v_sz_boxed_7250_; size_t v_i_boxed_7251_; lean_object* v_res_7252_; 
v_sz_boxed_7250_ = lean_unbox_usize(v_sz_7247_);
lean_dec(v_sz_7247_);
v_i_boxed_7251_ = lean_unbox_usize(v_i_7248_);
lean_dec(v_i_7248_);
v_res_7252_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(v_adjustResult_7245_, v_j_7246_, v_sz_boxed_7250_, v_i_boxed_7251_, v_bs_7249_);
return v_res_7252_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(lean_object* v_adjustResult_7253_, lean_object* v_j_7254_, lean_object* v_as_7255_, size_t v_i_7256_, size_t v_stop_7257_, lean_object* v_b_7258_){
_start:
{
uint8_t v___x_7259_; 
v___x_7259_ = lean_usize_dec_eq(v_i_7256_, v_stop_7257_);
if (v___x_7259_ == 0)
{
lean_object* v___x_7260_; size_t v_sz_7261_; size_t v___x_7262_; lean_object* v___x_7263_; lean_object* v___x_7264_; size_t v___x_7265_; size_t v___x_7266_; 
v___x_7260_ = lean_array_uget_borrowed(v_as_7255_, v_i_7256_);
v_sz_7261_ = lean_array_size(v___x_7260_);
v___x_7262_ = ((size_t)0ULL);
lean_inc(v___x_7260_);
lean_inc(v_j_7254_);
lean_inc(v_adjustResult_7253_);
v___x_7263_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(v_adjustResult_7253_, v_j_7254_, v_sz_7261_, v___x_7262_, v___x_7260_);
v___x_7264_ = l_Array_append___redArg(v_b_7258_, v___x_7263_);
lean_dec_ref(v___x_7263_);
v___x_7265_ = ((size_t)1ULL);
v___x_7266_ = lean_usize_add(v_i_7256_, v___x_7265_);
v_i_7256_ = v___x_7266_;
v_b_7258_ = v___x_7264_;
goto _start;
}
else
{
lean_dec(v_j_7254_);
lean_dec(v_adjustResult_7253_);
return v_b_7258_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg___boxed(lean_object* v_adjustResult_7268_, lean_object* v_j_7269_, lean_object* v_as_7270_, lean_object* v_i_7271_, lean_object* v_stop_7272_, lean_object* v_b_7273_){
_start:
{
size_t v_i_boxed_7274_; size_t v_stop_boxed_7275_; lean_object* v_res_7276_; 
v_i_boxed_7274_ = lean_unbox_usize(v_i_7271_);
lean_dec(v_i_7271_);
v_stop_boxed_7275_ = lean_unbox_usize(v_stop_7272_);
lean_dec(v_stop_7272_);
v_res_7276_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7268_, v_j_7269_, v_as_7270_, v_i_boxed_7274_, v_stop_boxed_7275_, v_b_7273_);
lean_dec_ref(v_as_7270_);
return v_res_7276_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(lean_object* v_n_7277_, lean_object* v_aa_7278_, lean_object* v_adjustResult_7279_, lean_object* v_n_7280_, lean_object* v_j_7281_, lean_object* v_a_7282_){
_start:
{
lean_object* v_zero_7283_; uint8_t v_isZero_7284_; 
v_zero_7283_ = lean_unsigned_to_nat(0u);
v_isZero_7284_ = lean_nat_dec_eq(v_j_7281_, v_zero_7283_);
if (v_isZero_7284_ == 1)
{
lean_dec(v_j_7281_);
lean_dec(v_adjustResult_7279_);
return v_a_7282_;
}
else
{
lean_object* v_one_7285_; lean_object* v_n_7286_; lean_object* v___x_7287_; lean_object* v___x_7288_; lean_object* v_j_7289_; lean_object* v_b_7290_; lean_object* v___x_7291_; uint8_t v___x_7292_; 
v_one_7285_ = lean_unsigned_to_nat(1u);
v_n_7286_ = lean_nat_sub(v_j_7281_, v_one_7285_);
v___x_7287_ = lean_nat_sub(v_n_7280_, v_j_7281_);
lean_dec(v_j_7281_);
v___x_7288_ = lean_nat_sub(v_n_7277_, v_one_7285_);
v_j_7289_ = lean_nat_sub(v___x_7288_, v___x_7287_);
lean_dec(v___x_7287_);
lean_dec(v___x_7288_);
v_b_7290_ = lean_array_fget_borrowed(v_aa_7278_, v_j_7289_);
v___x_7291_ = lean_array_get_size(v_b_7290_);
v___x_7292_ = lean_nat_dec_lt(v_zero_7283_, v___x_7291_);
if (v___x_7292_ == 0)
{
lean_dec(v_j_7289_);
v_j_7281_ = v_n_7286_;
goto _start;
}
else
{
uint8_t v___x_7294_; 
v___x_7294_ = lean_nat_dec_le(v___x_7291_, v___x_7291_);
if (v___x_7294_ == 0)
{
if (v___x_7292_ == 0)
{
lean_dec(v_j_7289_);
v_j_7281_ = v_n_7286_;
goto _start;
}
else
{
size_t v___x_7296_; size_t v___x_7297_; lean_object* v___x_7298_; 
v___x_7296_ = ((size_t)0ULL);
v___x_7297_ = lean_usize_of_nat(v___x_7291_);
lean_inc(v_adjustResult_7279_);
v___x_7298_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7279_, v_j_7289_, v_b_7290_, v___x_7296_, v___x_7297_, v_a_7282_);
v_j_7281_ = v_n_7286_;
v_a_7282_ = v___x_7298_;
goto _start;
}
}
else
{
size_t v___x_7300_; size_t v___x_7301_; lean_object* v___x_7302_; 
v___x_7300_ = ((size_t)0ULL);
v___x_7301_ = lean_usize_of_nat(v___x_7291_);
lean_inc(v_adjustResult_7279_);
v___x_7302_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7279_, v_j_7289_, v_b_7290_, v___x_7300_, v___x_7301_, v_a_7282_);
v_j_7281_ = v_n_7286_;
v_a_7282_ = v___x_7302_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_n_7304_, lean_object* v_aa_7305_, lean_object* v_adjustResult_7306_, lean_object* v_n_7307_, lean_object* v_j_7308_, lean_object* v_a_7309_){
_start:
{
lean_object* v_res_7310_; 
v_res_7310_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7304_, v_aa_7305_, v_adjustResult_7306_, v_n_7307_, v_j_7308_, v_a_7309_);
lean_dec(v_n_7307_);
lean_dec_ref(v_aa_7305_);
lean_dec(v_n_7304_);
return v_res_7310_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(lean_object* v_n_7311_, lean_object* v_adjustResult_7312_, lean_object* v_aa_7313_, lean_object* v_n_7314_, lean_object* v_j_7315_, lean_object* v_a_7316_){
_start:
{
lean_object* v_zero_7317_; uint8_t v_isZero_7318_; 
v_zero_7317_ = lean_unsigned_to_nat(0u);
v_isZero_7318_ = lean_nat_dec_eq(v_j_7315_, v_zero_7317_);
if (v_isZero_7318_ == 1)
{
lean_dec(v_adjustResult_7312_);
return v_a_7316_;
}
else
{
lean_object* v_one_7319_; lean_object* v_n_7320_; lean_object* v___x_7321_; lean_object* v___x_7322_; lean_object* v_j_7323_; lean_object* v_b_7324_; lean_object* v___x_7325_; uint8_t v___x_7326_; 
v_one_7319_ = lean_unsigned_to_nat(1u);
v_n_7320_ = lean_nat_sub(v_j_7315_, v_one_7319_);
v___x_7321_ = lean_nat_sub(v_n_7314_, v_j_7315_);
v___x_7322_ = lean_nat_sub(v_n_7311_, v_one_7319_);
v_j_7323_ = lean_nat_sub(v___x_7322_, v___x_7321_);
lean_dec(v___x_7321_);
lean_dec(v___x_7322_);
v_b_7324_ = lean_array_fget_borrowed(v_aa_7313_, v_j_7323_);
v___x_7325_ = lean_array_get_size(v_b_7324_);
v___x_7326_ = lean_nat_dec_lt(v_zero_7317_, v___x_7325_);
if (v___x_7326_ == 0)
{
lean_object* v___x_7327_; 
lean_dec(v_j_7323_);
v___x_7327_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7311_, v_aa_7313_, v_adjustResult_7312_, v_n_7314_, v_n_7320_, v_a_7316_);
return v___x_7327_;
}
else
{
uint8_t v___x_7328_; 
v___x_7328_ = lean_nat_dec_le(v___x_7325_, v___x_7325_);
if (v___x_7328_ == 0)
{
if (v___x_7326_ == 0)
{
lean_object* v___x_7329_; 
lean_dec(v_j_7323_);
v___x_7329_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7311_, v_aa_7313_, v_adjustResult_7312_, v_n_7314_, v_n_7320_, v_a_7316_);
return v___x_7329_;
}
else
{
size_t v___x_7330_; size_t v___x_7331_; lean_object* v___x_7332_; lean_object* v___x_7333_; 
v___x_7330_ = ((size_t)0ULL);
v___x_7331_ = lean_usize_of_nat(v___x_7325_);
lean_inc(v_adjustResult_7312_);
v___x_7332_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7312_, v_j_7323_, v_b_7324_, v___x_7330_, v___x_7331_, v_a_7316_);
v___x_7333_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7311_, v_aa_7313_, v_adjustResult_7312_, v_n_7314_, v_n_7320_, v___x_7332_);
return v___x_7333_;
}
}
else
{
size_t v___x_7334_; size_t v___x_7335_; lean_object* v___x_7336_; lean_object* v___x_7337_; 
v___x_7334_ = ((size_t)0ULL);
v___x_7335_ = lean_usize_of_nat(v___x_7325_);
lean_inc(v_adjustResult_7312_);
v___x_7336_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7312_, v_j_7323_, v_b_7324_, v___x_7334_, v___x_7335_, v_a_7316_);
v___x_7337_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7311_, v_aa_7313_, v_adjustResult_7312_, v_n_7314_, v_n_7320_, v___x_7336_);
return v___x_7337_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg___boxed(lean_object* v_n_7338_, lean_object* v_adjustResult_7339_, lean_object* v_aa_7340_, lean_object* v_n_7341_, lean_object* v_j_7342_, lean_object* v_a_7343_){
_start:
{
lean_object* v_res_7344_; 
v_res_7344_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(v_n_7338_, v_adjustResult_7339_, v_aa_7340_, v_n_7341_, v_j_7342_, v_a_7343_);
lean_dec(v_j_7342_);
lean_dec(v_n_7341_);
lean_dec_ref(v_aa_7340_);
lean_dec(v_n_7338_);
return v_res_7344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(lean_object* v_adjustResult_7345_, lean_object* v_mr_7346_, lean_object* v_a_7347_){
_start:
{
lean_object* v_n_7348_; lean_object* v___x_7349_; 
v_n_7348_ = lean_array_get_size(v_mr_7346_);
v___x_7349_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(v_n_7348_, v_adjustResult_7345_, v_mr_7346_, v_n_7348_, v_n_7348_, v_a_7347_);
return v___x_7349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg___boxed(lean_object* v_adjustResult_7350_, lean_object* v_mr_7351_, lean_object* v_a_7352_){
_start:
{
lean_object* v_res_7353_; 
v_res_7353_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7350_, v_mr_7351_, v_a_7352_);
lean_dec_ref(v_mr_7351_);
return v_res_7353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(lean_object* v_moduleTreeRef_7354_, lean_object* v_ref_7355_, lean_object* v_addEntry_7356_, lean_object* v_droppedKeys_7357_, lean_object* v_constantsPerTask_7358_, lean_object* v_droppedEntriesRef_7359_, lean_object* v_adjustResult_7360_, lean_object* v_ty_7361_, lean_object* v_a_7362_, lean_object* v_a_7363_, lean_object* v_a_7364_, lean_object* v_a_7365_){
_start:
{
lean_object* v___x_7367_; 
lean_inc_ref(v_ty_7361_);
v___x_7367_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(v_moduleTreeRef_7354_, v_ty_7361_, v_a_7362_, v_a_7363_, v_a_7364_, v_a_7365_);
if (lean_obj_tag(v___x_7367_) == 0)
{
lean_object* v_a_7368_; lean_object* v___x_7369_; 
v_a_7368_ = lean_ctor_get(v___x_7367_, 0);
lean_inc(v_a_7368_);
lean_dec_ref_known(v___x_7367_, 1);
v___x_7369_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(v_ref_7355_, v_addEntry_7356_, v_droppedKeys_7357_, v_constantsPerTask_7358_, v_droppedEntriesRef_7359_, v_ty_7361_, v_a_7362_, v_a_7363_, v_a_7364_, v_a_7365_);
if (lean_obj_tag(v___x_7369_) == 0)
{
lean_object* v_a_7370_; lean_object* v___x_7372_; uint8_t v_isShared_7373_; uint8_t v_isSharedCheck_7383_; 
v_a_7370_ = lean_ctor_get(v___x_7369_, 0);
v_isSharedCheck_7383_ = !lean_is_exclusive(v___x_7369_);
if (v_isSharedCheck_7383_ == 0)
{
v___x_7372_ = v___x_7369_;
v_isShared_7373_ = v_isSharedCheck_7383_;
goto v_resetjp_7371_;
}
else
{
lean_inc(v_a_7370_);
lean_dec(v___x_7369_);
v___x_7372_ = lean_box(0);
v_isShared_7373_ = v_isSharedCheck_7383_;
goto v_resetjp_7371_;
}
v_resetjp_7371_:
{
lean_object* v___x_7374_; lean_object* v___x_7375_; lean_object* v___x_7376_; lean_object* v___x_7377_; lean_object* v___x_7378_; lean_object* v___x_7379_; lean_object* v___x_7381_; 
v___x_7374_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_a_7368_);
v___x_7375_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_a_7370_);
v___x_7376_ = lean_nat_add(v___x_7374_, v___x_7375_);
lean_dec(v___x_7375_);
lean_dec(v___x_7374_);
v___x_7377_ = lean_mk_empty_array_with_capacity(v___x_7376_);
lean_dec(v___x_7376_);
lean_inc(v_adjustResult_7360_);
v___x_7378_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7360_, v_a_7368_, v___x_7377_);
lean_dec(v_a_7368_);
v___x_7379_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7360_, v_a_7370_, v___x_7378_);
lean_dec(v_a_7370_);
if (v_isShared_7373_ == 0)
{
lean_ctor_set(v___x_7372_, 0, v___x_7379_);
v___x_7381_ = v___x_7372_;
goto v_reusejp_7380_;
}
else
{
lean_object* v_reuseFailAlloc_7382_; 
v_reuseFailAlloc_7382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7382_, 0, v___x_7379_);
v___x_7381_ = v_reuseFailAlloc_7382_;
goto v_reusejp_7380_;
}
v_reusejp_7380_:
{
return v___x_7381_;
}
}
}
else
{
lean_object* v_a_7384_; lean_object* v___x_7386_; uint8_t v_isShared_7387_; uint8_t v_isSharedCheck_7391_; 
lean_dec(v_a_7368_);
lean_dec(v_adjustResult_7360_);
v_a_7384_ = lean_ctor_get(v___x_7369_, 0);
v_isSharedCheck_7391_ = !lean_is_exclusive(v___x_7369_);
if (v_isSharedCheck_7391_ == 0)
{
v___x_7386_ = v___x_7369_;
v_isShared_7387_ = v_isSharedCheck_7391_;
goto v_resetjp_7385_;
}
else
{
lean_inc(v_a_7384_);
lean_dec(v___x_7369_);
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
else
{
lean_object* v_a_7392_; lean_object* v___x_7394_; uint8_t v_isShared_7395_; uint8_t v_isSharedCheck_7399_; 
lean_dec_ref(v_ty_7361_);
lean_dec(v_adjustResult_7360_);
lean_dec(v_droppedEntriesRef_7359_);
lean_dec(v_constantsPerTask_7358_);
lean_dec(v_droppedKeys_7357_);
lean_dec_ref(v_addEntry_7356_);
v_a_7392_ = lean_ctor_get(v___x_7367_, 0);
v_isSharedCheck_7399_ = !lean_is_exclusive(v___x_7367_);
if (v_isSharedCheck_7399_ == 0)
{
v___x_7394_ = v___x_7367_;
v_isShared_7395_ = v_isSharedCheck_7399_;
goto v_resetjp_7393_;
}
else
{
lean_inc(v_a_7392_);
lean_dec(v___x_7367_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg___boxed(lean_object* v_moduleTreeRef_7400_, lean_object* v_ref_7401_, lean_object* v_addEntry_7402_, lean_object* v_droppedKeys_7403_, lean_object* v_constantsPerTask_7404_, lean_object* v_droppedEntriesRef_7405_, lean_object* v_adjustResult_7406_, lean_object* v_ty_7407_, lean_object* v_a_7408_, lean_object* v_a_7409_, lean_object* v_a_7410_, lean_object* v_a_7411_, lean_object* v_a_7412_){
_start:
{
lean_object* v_res_7413_; 
v_res_7413_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_moduleTreeRef_7400_, v_ref_7401_, v_addEntry_7402_, v_droppedKeys_7403_, v_constantsPerTask_7404_, v_droppedEntriesRef_7405_, v_adjustResult_7406_, v_ty_7407_, v_a_7408_, v_a_7409_, v_a_7410_, v_a_7411_);
lean_dec(v_a_7411_);
lean_dec_ref(v_a_7410_);
lean_dec(v_a_7409_);
lean_dec_ref(v_a_7408_);
lean_dec(v_ref_7401_);
return v_res_7413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt(lean_object* v_00_u03b1_7414_, lean_object* v_00_u03b2_7415_, lean_object* v_moduleTreeRef_7416_, lean_object* v_ref_7417_, lean_object* v_addEntry_7418_, lean_object* v_droppedKeys_7419_, lean_object* v_constantsPerTask_7420_, lean_object* v_droppedEntriesRef_7421_, lean_object* v_adjustResult_7422_, lean_object* v_ty_7423_, lean_object* v_a_7424_, lean_object* v_a_7425_, lean_object* v_a_7426_, lean_object* v_a_7427_){
_start:
{
lean_object* v___x_7429_; 
v___x_7429_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_moduleTreeRef_7416_, v_ref_7417_, v_addEntry_7418_, v_droppedKeys_7419_, v_constantsPerTask_7420_, v_droppedEntriesRef_7421_, v_adjustResult_7422_, v_ty_7423_, v_a_7424_, v_a_7425_, v_a_7426_, v_a_7427_);
return v___x_7429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___boxed(lean_object* v_00_u03b1_7430_, lean_object* v_00_u03b2_7431_, lean_object* v_moduleTreeRef_7432_, lean_object* v_ref_7433_, lean_object* v_addEntry_7434_, lean_object* v_droppedKeys_7435_, lean_object* v_constantsPerTask_7436_, lean_object* v_droppedEntriesRef_7437_, lean_object* v_adjustResult_7438_, lean_object* v_ty_7439_, lean_object* v_a_7440_, lean_object* v_a_7441_, lean_object* v_a_7442_, lean_object* v_a_7443_, lean_object* v_a_7444_){
_start:
{
lean_object* v_res_7445_; 
v_res_7445_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt(v_00_u03b1_7430_, v_00_u03b2_7431_, v_moduleTreeRef_7432_, v_ref_7433_, v_addEntry_7434_, v_droppedKeys_7435_, v_constantsPerTask_7436_, v_droppedEntriesRef_7437_, v_adjustResult_7438_, v_ty_7439_, v_a_7440_, v_a_7441_, v_a_7442_, v_a_7443_);
lean_dec(v_a_7443_);
lean_dec_ref(v_a_7442_);
lean_dec(v_a_7441_);
lean_dec_ref(v_a_7440_);
lean_dec(v_ref_7433_);
return v_res_7445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0(lean_object* v_00_u03b1_7446_, lean_object* v_00_u03b2_7447_, lean_object* v_adjustResult_7448_, lean_object* v_mr_7449_, lean_object* v_a_7450_){
_start:
{
lean_object* v___x_7451_; 
v___x_7451_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7448_, v_mr_7449_, v_a_7450_);
return v___x_7451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___boxed(lean_object* v_00_u03b1_7452_, lean_object* v_00_u03b2_7453_, lean_object* v_adjustResult_7454_, lean_object* v_mr_7455_, lean_object* v_a_7456_){
_start:
{
lean_object* v_res_7457_; 
v_res_7457_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0(v_00_u03b1_7452_, v_00_u03b2_7453_, v_adjustResult_7454_, v_mr_7455_, v_a_7456_);
lean_dec_ref(v_mr_7455_);
return v_res_7457_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0(lean_object* v_00_u03b1_7458_, lean_object* v_00_u03b2_7459_, lean_object* v_adjustResult_7460_, lean_object* v_j_7461_, size_t v_sz_7462_, size_t v_i_7463_, lean_object* v_bs_7464_){
_start:
{
lean_object* v___x_7465_; 
v___x_7465_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(v_adjustResult_7460_, v_j_7461_, v_sz_7462_, v_i_7463_, v_bs_7464_);
return v___x_7465_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___boxed(lean_object* v_00_u03b1_7466_, lean_object* v_00_u03b2_7467_, lean_object* v_adjustResult_7468_, lean_object* v_j_7469_, lean_object* v_sz_7470_, lean_object* v_i_7471_, lean_object* v_bs_7472_){
_start:
{
size_t v_sz_boxed_7473_; size_t v_i_boxed_7474_; lean_object* v_res_7475_; 
v_sz_boxed_7473_ = lean_unbox_usize(v_sz_7470_);
lean_dec(v_sz_7470_);
v_i_boxed_7474_ = lean_unbox_usize(v_i_7471_);
lean_dec(v_i_7471_);
v_res_7475_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0(v_00_u03b1_7466_, v_00_u03b2_7467_, v_adjustResult_7468_, v_j_7469_, v_sz_boxed_7473_, v_i_boxed_7474_, v_bs_7472_);
return v_res_7475_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1(lean_object* v_00_u03b1_7476_, lean_object* v_00_u03b2_7477_, lean_object* v_adjustResult_7478_, lean_object* v_j_7479_, lean_object* v_as_7480_, size_t v_i_7481_, size_t v_stop_7482_, lean_object* v_b_7483_){
_start:
{
lean_object* v___x_7484_; 
v___x_7484_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7478_, v_j_7479_, v_as_7480_, v_i_7481_, v_stop_7482_, v_b_7483_);
return v___x_7484_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___boxed(lean_object* v_00_u03b1_7485_, lean_object* v_00_u03b2_7486_, lean_object* v_adjustResult_7487_, lean_object* v_j_7488_, lean_object* v_as_7489_, lean_object* v_i_7490_, lean_object* v_stop_7491_, lean_object* v_b_7492_){
_start:
{
size_t v_i_boxed_7493_; size_t v_stop_boxed_7494_; lean_object* v_res_7495_; 
v_i_boxed_7493_ = lean_unbox_usize(v_i_7490_);
lean_dec(v_i_7490_);
v_stop_boxed_7494_ = lean_unbox_usize(v_stop_7491_);
lean_dec(v_stop_7491_);
v_res_7495_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1(v_00_u03b1_7485_, v_00_u03b2_7486_, v_adjustResult_7487_, v_j_7488_, v_as_7489_, v_i_boxed_7493_, v_stop_boxed_7494_, v_b_7492_);
lean_dec_ref(v_as_7489_);
return v_res_7495_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2(lean_object* v_00_u03b2_7496_, lean_object* v_n_7497_, lean_object* v_00_u03b1_7498_, lean_object* v_adjustResult_7499_, lean_object* v_aa_7500_, lean_object* v_n_7501_, lean_object* v_j_7502_, lean_object* v_a_7503_, lean_object* v_a_7504_){
_start:
{
lean_object* v___x_7505_; 
v___x_7505_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(v_n_7497_, v_adjustResult_7499_, v_aa_7500_, v_n_7501_, v_j_7502_, v_a_7504_);
return v___x_7505_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___boxed(lean_object* v_00_u03b2_7506_, lean_object* v_n_7507_, lean_object* v_00_u03b1_7508_, lean_object* v_adjustResult_7509_, lean_object* v_aa_7510_, lean_object* v_n_7511_, lean_object* v_j_7512_, lean_object* v_a_7513_, lean_object* v_a_7514_){
_start:
{
lean_object* v_res_7515_; 
v_res_7515_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2(v_00_u03b2_7506_, v_n_7507_, v_00_u03b1_7508_, v_adjustResult_7509_, v_aa_7510_, v_n_7511_, v_j_7512_, v_a_7513_, v_a_7514_);
lean_dec(v_j_7512_);
lean_dec(v_n_7511_);
lean_dec_ref(v_aa_7510_);
lean_dec(v_n_7507_);
return v_res_7515_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_7516_, lean_object* v_n_7517_, lean_object* v_00_u03b1_7518_, lean_object* v_aa_7519_, lean_object* v_adjustResult_7520_, lean_object* v_n_7521_, lean_object* v_j_7522_, lean_object* v_a_7523_, lean_object* v_a_7524_){
_start:
{
lean_object* v___x_7525_; 
v___x_7525_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7517_, v_aa_7519_, v_adjustResult_7520_, v_n_7521_, v_j_7522_, v_a_7524_);
return v___x_7525_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b2_7526_, lean_object* v_n_7527_, lean_object* v_00_u03b1_7528_, lean_object* v_aa_7529_, lean_object* v_adjustResult_7530_, lean_object* v_n_7531_, lean_object* v_j_7532_, lean_object* v_a_7533_, lean_object* v_a_7534_){
_start:
{
lean_object* v_res_7535_; 
v_res_7535_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3(v_00_u03b2_7526_, v_n_7527_, v_00_u03b1_7528_, v_aa_7529_, v_adjustResult_7530_, v_n_7531_, v_j_7532_, v_a_7533_, v_a_7534_);
lean_dec(v_n_7531_);
lean_dec_ref(v_aa_7529_);
lean_dec(v_n_7527_);
return v_res_7535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg___lam__0(lean_object* v_x_7536_, lean_object* v_v_7537_){
_start:
{
lean_inc(v_v_7537_);
return v_v_7537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg___lam__0___boxed(lean_object* v_x_7538_, lean_object* v_v_7539_){
_start:
{
lean_object* v_res_7540_; 
v_res_7540_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg___lam__0(v_x_7538_, v_v_7539_);
lean_dec(v_v_7539_);
lean_dec(v_x_7538_);
return v_res_7540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg(lean_object* v_ref_7542_, lean_object* v_addEntry_7543_, lean_object* v_droppedKeys_7544_, lean_object* v_constantsPerTask_7545_, lean_object* v_droppedEntriesRef_7546_, lean_object* v_ty_7547_, lean_object* v_a_7548_, lean_object* v_a_7549_, lean_object* v_a_7550_, lean_object* v_a_7551_){
_start:
{
lean_object* v___x_7553_; 
lean_inc(v_droppedEntriesRef_7546_);
lean_inc(v_droppedKeys_7544_);
lean_inc_ref(v_addEntry_7543_);
v___x_7553_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v_addEntry_7543_, v_droppedKeys_7544_, v_droppedEntriesRef_7546_, v_a_7548_, v_a_7549_, v_a_7550_, v_a_7551_);
if (lean_obj_tag(v___x_7553_) == 0)
{
lean_object* v_a_7554_; lean_object* v___f_7555_; lean_object* v___x_7556_; 
v_a_7554_ = lean_ctor_get(v___x_7553_, 0);
lean_inc(v_a_7554_);
lean_dec_ref_known(v___x_7553_, 1);
v___f_7555_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_findMatches___redArg___closed__0));
v___x_7556_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_a_7554_, v_ref_7542_, v_addEntry_7543_, v_droppedKeys_7544_, v_constantsPerTask_7545_, v_droppedEntriesRef_7546_, v___f_7555_, v_ty_7547_, v_a_7548_, v_a_7549_, v_a_7550_, v_a_7551_);
return v___x_7556_;
}
else
{
lean_object* v_a_7557_; lean_object* v___x_7559_; uint8_t v_isShared_7560_; uint8_t v_isSharedCheck_7564_; 
lean_dec_ref(v_ty_7547_);
lean_dec(v_droppedEntriesRef_7546_);
lean_dec(v_constantsPerTask_7545_);
lean_dec(v_droppedKeys_7544_);
lean_dec_ref(v_addEntry_7543_);
v_a_7557_ = lean_ctor_get(v___x_7553_, 0);
v_isSharedCheck_7564_ = !lean_is_exclusive(v___x_7553_);
if (v_isSharedCheck_7564_ == 0)
{
v___x_7559_ = v___x_7553_;
v_isShared_7560_ = v_isSharedCheck_7564_;
goto v_resetjp_7558_;
}
else
{
lean_inc(v_a_7557_);
lean_dec(v___x_7553_);
v___x_7559_ = lean_box(0);
v_isShared_7560_ = v_isSharedCheck_7564_;
goto v_resetjp_7558_;
}
v_resetjp_7558_:
{
lean_object* v___x_7562_; 
if (v_isShared_7560_ == 0)
{
v___x_7562_ = v___x_7559_;
goto v_reusejp_7561_;
}
else
{
lean_object* v_reuseFailAlloc_7563_; 
v_reuseFailAlloc_7563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7563_, 0, v_a_7557_);
v___x_7562_ = v_reuseFailAlloc_7563_;
goto v_reusejp_7561_;
}
v_reusejp_7561_:
{
return v___x_7562_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg___boxed(lean_object* v_ref_7565_, lean_object* v_addEntry_7566_, lean_object* v_droppedKeys_7567_, lean_object* v_constantsPerTask_7568_, lean_object* v_droppedEntriesRef_7569_, lean_object* v_ty_7570_, lean_object* v_a_7571_, lean_object* v_a_7572_, lean_object* v_a_7573_, lean_object* v_a_7574_, lean_object* v_a_7575_){
_start:
{
lean_object* v_res_7576_; 
v_res_7576_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg(v_ref_7565_, v_addEntry_7566_, v_droppedKeys_7567_, v_constantsPerTask_7568_, v_droppedEntriesRef_7569_, v_ty_7570_, v_a_7571_, v_a_7572_, v_a_7573_, v_a_7574_);
lean_dec(v_a_7574_);
lean_dec_ref(v_a_7573_);
lean_dec(v_a_7572_);
lean_dec_ref(v_a_7571_);
lean_dec(v_ref_7565_);
return v_res_7576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches(lean_object* v_00_u03b1_7577_, lean_object* v_ref_7578_, lean_object* v_addEntry_7579_, lean_object* v_droppedKeys_7580_, lean_object* v_constantsPerTask_7581_, lean_object* v_droppedEntriesRef_7582_, lean_object* v_ty_7583_, lean_object* v_a_7584_, lean_object* v_a_7585_, lean_object* v_a_7586_, lean_object* v_a_7587_){
_start:
{
lean_object* v___x_7589_; 
v___x_7589_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg(v_ref_7578_, v_addEntry_7579_, v_droppedKeys_7580_, v_constantsPerTask_7581_, v_droppedEntriesRef_7582_, v_ty_7583_, v_a_7584_, v_a_7585_, v_a_7586_, v_a_7587_);
return v___x_7589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___boxed(lean_object* v_00_u03b1_7590_, lean_object* v_ref_7591_, lean_object* v_addEntry_7592_, lean_object* v_droppedKeys_7593_, lean_object* v_constantsPerTask_7594_, lean_object* v_droppedEntriesRef_7595_, lean_object* v_ty_7596_, lean_object* v_a_7597_, lean_object* v_a_7598_, lean_object* v_a_7599_, lean_object* v_a_7600_, lean_object* v_a_7601_){
_start:
{
lean_object* v_res_7602_; 
v_res_7602_ = l_Lean_Meta_LazyDiscrTree_findMatches(v_00_u03b1_7590_, v_ref_7591_, v_addEntry_7592_, v_droppedKeys_7593_, v_constantsPerTask_7594_, v_droppedEntriesRef_7595_, v_ty_7596_, v_a_7597_, v_a_7598_, v_a_7599_, v_a_7600_);
lean_dec(v_a_7600_);
lean_dec_ref(v_a_7599_);
lean_dec(v_a_7598_);
lean_dec_ref(v_a_7597_);
lean_dec(v_ref_7591_);
return v_res_7602_;
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
