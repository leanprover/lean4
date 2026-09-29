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
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
uint16_t l_Lean_OptionFlags_ofOptions(lean_object*);
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
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint16_t lean_uint16_land(uint16_t, uint16_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7_spec__9___boxed(lean_object*, lean_object*);
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
lean_object* v___y_780_; uint16_t v___y_790_; uint8_t v___y_791_; lean_object* v___y_792_; uint8_t v___y_793_; lean_object* v___y_794_; lean_object* v___y_795_; lean_object* v_toCold_800_; lean_object* v_currRecDepth_801_; lean_object* v_ref_802_; uint16_t v_optionFlags_803_; uint8_t v_suppressElabErrors_804_; uint8_t v_isRecordingDeps_805_; lean_object* v_maxRecDepth_806_; lean_object* v_cancelTk_x3f_807_; 
v_toCold_800_ = lean_ctor_get(v___y_776_, 0);
v_currRecDepth_801_ = lean_ctor_get(v___y_776_, 1);
v_ref_802_ = lean_ctor_get(v___y_776_, 2);
v_optionFlags_803_ = lean_ctor_get_uint16(v___y_776_, sizeof(void*)*3);
v_suppressElabErrors_804_ = lean_ctor_get_uint8(v___y_776_, sizeof(void*)*3 + 2);
v_isRecordingDeps_805_ = lean_ctor_get_uint8(v___y_776_, sizeof(void*)*3 + 3);
v_maxRecDepth_806_ = lean_ctor_get(v_toCold_800_, 3);
v_cancelTk_x3f_807_ = lean_ctor_get(v_toCold_800_, 10);
if (lean_obj_tag(v_cancelTk_x3f_807_) == 1)
{
lean_object* v_val_813_; uint8_t v___x_814_; 
v_val_813_ = lean_ctor_get(v_cancelTk_x3f_807_, 0);
v___x_814_ = l_IO_CancelToken_isSet(v_val_813_);
if (v___x_814_ == 0)
{
goto v___jp_808_;
}
else
{
lean_object* v___x_815_; lean_object* v_a_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_823_; 
lean_dec_ref(v_x_774_);
v___x_815_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg();
v_a_816_ = lean_ctor_get(v___x_815_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_823_ == 0)
{
v___x_818_ = v___x_815_;
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_a_816_);
lean_dec(v___x_815_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_821_; 
if (v_isShared_819_ == 0)
{
v___x_821_ = v___x_818_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_a_816_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
}
else
{
goto v___jp_808_;
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
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_796_ = lean_unsigned_to_nat(1u);
v___x_797_ = lean_nat_add(v___y_792_, v___x_796_);
lean_inc_ref(v___y_794_);
v___x_798_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_798_, 0, v___y_794_);
lean_ctor_set(v___x_798_, 1, v___x_797_);
lean_ctor_set(v___x_798_, 2, v___y_795_);
lean_ctor_set_uint16(v___x_798_, sizeof(void*)*3, v___y_790_);
lean_ctor_set_uint8(v___x_798_, sizeof(void*)*3 + 2, v___y_791_);
lean_ctor_set_uint8(v___x_798_, sizeof(void*)*3 + 3, v___y_793_);
lean_inc(v___y_777_);
lean_inc(v___y_775_);
v___x_799_ = lean_apply_4(v_x_774_, v___y_775_, v___x_798_, v___y_777_, lean_box(0));
v___y_780_ = v___x_799_;
goto v___jp_779_;
}
v___jp_808_:
{
lean_object* v___x_809_; uint8_t v___x_810_; 
v___x_809_ = lean_unsigned_to_nat(0u);
v___x_810_ = lean_nat_dec_eq(v_maxRecDepth_806_, v___x_809_);
if (v___x_810_ == 0)
{
uint8_t v___x_811_; 
v___x_811_ = lean_nat_dec_eq(v_currRecDepth_801_, v_maxRecDepth_806_);
if (v___x_811_ == 0)
{
lean_inc(v_ref_802_);
v___y_790_ = v_optionFlags_803_;
v___y_791_ = v_suppressElabErrors_804_;
v___y_792_ = v_currRecDepth_801_;
v___y_793_ = v_isRecordingDeps_805_;
v___y_794_ = v_toCold_800_;
v___y_795_ = v_ref_802_;
goto v___jp_789_;
}
else
{
lean_object* v___x_812_; 
lean_dec_ref(v_x_774_);
lean_inc(v_ref_802_);
v___x_812_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_802_);
v___y_780_ = v___x_812_;
goto v___jp_779_;
}
}
else
{
lean_inc(v_ref_802_);
v___y_790_ = v_optionFlags_803_;
v___y_791_ = v_suppressElabErrors_804_;
v___y_792_ = v_currRecDepth_801_;
v___y_793_ = v_isRecordingDeps_805_;
v___y_794_ = v_toCold_800_;
v___y_795_ = v_ref_802_;
goto v___jp_789_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg(v_x_824_, v___y_825_, v___y_826_, v___y_827_);
lean_dec(v___y_827_);
lean_dec_ref(v___y_826_);
lean_dec(v___y_825_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_a_830_, lean_object* v_x_831_){
_start:
{
if (lean_obj_tag(v_x_831_) == 0)
{
lean_object* v___x_832_; 
v___x_832_ = lean_box(0);
return v___x_832_;
}
else
{
lean_object* v_key_833_; lean_object* v_value_834_; lean_object* v_tail_835_; uint8_t v___x_836_; 
v_key_833_ = lean_ctor_get(v_x_831_, 0);
v_value_834_ = lean_ctor_get(v_x_831_, 1);
v_tail_835_ = lean_ctor_get(v_x_831_, 2);
v___x_836_ = l_Lean_ExprStructEq_beq(v_key_833_, v_a_830_);
if (v___x_836_ == 0)
{
v_x_831_ = v_tail_835_;
goto _start;
}
else
{
lean_object* v___x_838_; 
lean_inc(v_value_834_);
v___x_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_838_, 0, v_value_834_);
return v___x_838_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_a_839_, lean_object* v_x_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg(v_a_839_, v_x_840_);
lean_dec(v_x_840_);
lean_dec_ref(v_a_839_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg(lean_object* v_m_842_, lean_object* v_a_843_){
_start:
{
lean_object* v_buckets_844_; lean_object* v___x_845_; uint64_t v___x_846_; uint64_t v___x_847_; uint64_t v___x_848_; uint64_t v_fold_849_; uint64_t v___x_850_; uint64_t v___x_851_; uint64_t v___x_852_; size_t v___x_853_; size_t v___x_854_; size_t v___x_855_; size_t v___x_856_; size_t v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
v_buckets_844_ = lean_ctor_get(v_m_842_, 1);
v___x_845_ = lean_array_get_size(v_buckets_844_);
v___x_846_ = l_Lean_ExprStructEq_hash(v_a_843_);
v___x_847_ = 32ULL;
v___x_848_ = lean_uint64_shift_right(v___x_846_, v___x_847_);
v_fold_849_ = lean_uint64_xor(v___x_846_, v___x_848_);
v___x_850_ = 16ULL;
v___x_851_ = lean_uint64_shift_right(v_fold_849_, v___x_850_);
v___x_852_ = lean_uint64_xor(v_fold_849_, v___x_851_);
v___x_853_ = lean_uint64_to_usize(v___x_852_);
v___x_854_ = lean_usize_of_nat(v___x_845_);
v___x_855_ = ((size_t)1ULL);
v___x_856_ = lean_usize_sub(v___x_854_, v___x_855_);
v___x_857_ = lean_usize_land(v___x_853_, v___x_856_);
v___x_858_ = lean_array_uget_borrowed(v_buckets_844_, v___x_857_);
v___x_859_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg(v_a_843_, v___x_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_m_860_, lean_object* v_a_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg(v_m_860_, v_a_861_);
lean_dec_ref(v_a_861_);
lean_dec_ref(v_m_860_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12___redArg(lean_object* v_a_863_, lean_object* v_b_864_, lean_object* v_x_865_){
_start:
{
if (lean_obj_tag(v_x_865_) == 0)
{
lean_dec(v_b_864_);
lean_dec_ref(v_a_863_);
return v_x_865_;
}
else
{
lean_object* v_key_866_; lean_object* v_value_867_; lean_object* v_tail_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_880_; 
v_key_866_ = lean_ctor_get(v_x_865_, 0);
v_value_867_ = lean_ctor_get(v_x_865_, 1);
v_tail_868_ = lean_ctor_get(v_x_865_, 2);
v_isSharedCheck_880_ = !lean_is_exclusive(v_x_865_);
if (v_isSharedCheck_880_ == 0)
{
v___x_870_ = v_x_865_;
v_isShared_871_ = v_isSharedCheck_880_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_tail_868_);
lean_inc(v_value_867_);
lean_inc(v_key_866_);
lean_dec(v_x_865_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_880_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
uint8_t v___x_872_; 
v___x_872_ = l_Lean_ExprStructEq_beq(v_key_866_, v_a_863_);
if (v___x_872_ == 0)
{
lean_object* v___x_873_; lean_object* v___x_875_; 
v___x_873_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12___redArg(v_a_863_, v_b_864_, v_tail_868_);
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 2, v___x_873_);
v___x_875_ = v___x_870_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_key_866_);
lean_ctor_set(v_reuseFailAlloc_876_, 1, v_value_867_);
lean_ctor_set(v_reuseFailAlloc_876_, 2, v___x_873_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
else
{
lean_object* v___x_878_; 
lean_dec(v_value_867_);
lean_dec(v_key_866_);
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 1, v_b_864_);
lean_ctor_set(v___x_870_, 0, v_a_863_);
v___x_878_ = v___x_870_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_a_863_);
lean_ctor_set(v_reuseFailAlloc_879_, 1, v_b_864_);
lean_ctor_set(v_reuseFailAlloc_879_, 2, v_tail_868_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(lean_object* v_x_881_, lean_object* v_x_882_){
_start:
{
if (lean_obj_tag(v_x_882_) == 0)
{
return v_x_881_;
}
else
{
lean_object* v_key_883_; lean_object* v_value_884_; lean_object* v_tail_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_908_; 
v_key_883_ = lean_ctor_get(v_x_882_, 0);
v_value_884_ = lean_ctor_get(v_x_882_, 1);
v_tail_885_ = lean_ctor_get(v_x_882_, 2);
v_isSharedCheck_908_ = !lean_is_exclusive(v_x_882_);
if (v_isSharedCheck_908_ == 0)
{
v___x_887_ = v_x_882_;
v_isShared_888_ = v_isSharedCheck_908_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_tail_885_);
lean_inc(v_value_884_);
lean_inc(v_key_883_);
lean_dec(v_x_882_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_908_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_889_; uint64_t v___x_890_; uint64_t v___x_891_; uint64_t v___x_892_; uint64_t v_fold_893_; uint64_t v___x_894_; uint64_t v___x_895_; uint64_t v___x_896_; size_t v___x_897_; size_t v___x_898_; size_t v___x_899_; size_t v___x_900_; size_t v___x_901_; lean_object* v___x_902_; lean_object* v___x_904_; 
v___x_889_ = lean_array_get_size(v_x_881_);
v___x_890_ = l_Lean_ExprStructEq_hash(v_key_883_);
v___x_891_ = 32ULL;
v___x_892_ = lean_uint64_shift_right(v___x_890_, v___x_891_);
v_fold_893_ = lean_uint64_xor(v___x_890_, v___x_892_);
v___x_894_ = 16ULL;
v___x_895_ = lean_uint64_shift_right(v_fold_893_, v___x_894_);
v___x_896_ = lean_uint64_xor(v_fold_893_, v___x_895_);
v___x_897_ = lean_uint64_to_usize(v___x_896_);
v___x_898_ = lean_usize_of_nat(v___x_889_);
v___x_899_ = ((size_t)1ULL);
v___x_900_ = lean_usize_sub(v___x_898_, v___x_899_);
v___x_901_ = lean_usize_land(v___x_897_, v___x_900_);
v___x_902_ = lean_array_uget_borrowed(v_x_881_, v___x_901_);
lean_inc(v___x_902_);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 2, v___x_902_);
v___x_904_ = v___x_887_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_key_883_);
lean_ctor_set(v_reuseFailAlloc_907_, 1, v_value_884_);
lean_ctor_set(v_reuseFailAlloc_907_, 2, v___x_902_);
v___x_904_ = v_reuseFailAlloc_907_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
lean_object* v___x_905_; 
v___x_905_ = lean_array_uset(v_x_881_, v___x_901_, v___x_904_);
v_x_881_ = v___x_905_;
v_x_882_ = v_tail_885_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(lean_object* v_i_909_, lean_object* v_source_910_, lean_object* v_target_911_){
_start:
{
lean_object* v___x_912_; uint8_t v___x_913_; 
v___x_912_ = lean_array_get_size(v_source_910_);
v___x_913_ = lean_nat_dec_lt(v_i_909_, v___x_912_);
if (v___x_913_ == 0)
{
lean_dec_ref(v_source_910_);
lean_dec(v_i_909_);
return v_target_911_;
}
else
{
lean_object* v_es_914_; lean_object* v___x_915_; lean_object* v_source_916_; lean_object* v_target_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v_es_914_ = lean_array_fget(v_source_910_, v_i_909_);
v___x_915_ = lean_box(0);
v_source_916_ = lean_array_fset(v_source_910_, v_i_909_, v___x_915_);
v_target_917_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_target_911_, v_es_914_);
v___x_918_ = lean_unsigned_to_nat(1u);
v___x_919_ = lean_nat_add(v_i_909_, v___x_918_);
lean_dec(v_i_909_);
v_i_909_ = v___x_919_;
v_source_910_ = v_source_916_;
v_target_911_ = v_target_917_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11___redArg(lean_object* v_data_921_){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v_nbuckets_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_922_ = lean_array_get_size(v_data_921_);
v___x_923_ = lean_unsigned_to_nat(2u);
v_nbuckets_924_ = lean_nat_mul(v___x_922_, v___x_923_);
v___x_925_ = lean_unsigned_to_nat(0u);
v___x_926_ = lean_box(0);
v___x_927_ = lean_mk_array(v_nbuckets_924_, v___x_926_);
v___x_928_ = lean_array_propagate_mark(v_data_921_, v___x_927_);
v___x_929_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v___x_925_, v_data_921_, v___x_928_);
return v___x_929_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(lean_object* v_a_930_, lean_object* v_x_931_){
_start:
{
if (lean_obj_tag(v_x_931_) == 0)
{
uint8_t v___x_932_; 
v___x_932_ = 0;
return v___x_932_;
}
else
{
lean_object* v_key_933_; lean_object* v_tail_934_; uint8_t v___x_935_; 
v_key_933_ = lean_ctor_get(v_x_931_, 0);
v_tail_934_ = lean_ctor_get(v_x_931_, 2);
v___x_935_ = l_Lean_ExprStructEq_beq(v_key_933_, v_a_930_);
if (v___x_935_ == 0)
{
v_x_931_ = v_tail_934_;
goto _start;
}
else
{
return v___x_935_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg___boxed(lean_object* v_a_937_, lean_object* v_x_938_){
_start:
{
uint8_t v_res_939_; lean_object* v_r_940_; 
v_res_939_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(v_a_937_, v_x_938_);
lean_dec(v_x_938_);
lean_dec_ref(v_a_937_);
v_r_940_ = lean_box(v_res_939_);
return v_r_940_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6___redArg(lean_object* v_m_941_, lean_object* v_a_942_, lean_object* v_b_943_){
_start:
{
lean_object* v_size_944_; lean_object* v_buckets_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_988_; 
v_size_944_ = lean_ctor_get(v_m_941_, 0);
v_buckets_945_ = lean_ctor_get(v_m_941_, 1);
v_isSharedCheck_988_ = !lean_is_exclusive(v_m_941_);
if (v_isSharedCheck_988_ == 0)
{
v___x_947_ = v_m_941_;
v_isShared_948_ = v_isSharedCheck_988_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_buckets_945_);
lean_inc(v_size_944_);
lean_dec(v_m_941_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_988_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_949_; uint64_t v___x_950_; uint64_t v___x_951_; uint64_t v___x_952_; uint64_t v_fold_953_; uint64_t v___x_954_; uint64_t v___x_955_; uint64_t v___x_956_; size_t v___x_957_; size_t v___x_958_; size_t v___x_959_; size_t v___x_960_; size_t v___x_961_; lean_object* v_bkt_962_; uint8_t v___x_963_; 
v___x_949_ = lean_array_get_size(v_buckets_945_);
v___x_950_ = l_Lean_ExprStructEq_hash(v_a_942_);
v___x_951_ = 32ULL;
v___x_952_ = lean_uint64_shift_right(v___x_950_, v___x_951_);
v_fold_953_ = lean_uint64_xor(v___x_950_, v___x_952_);
v___x_954_ = 16ULL;
v___x_955_ = lean_uint64_shift_right(v_fold_953_, v___x_954_);
v___x_956_ = lean_uint64_xor(v_fold_953_, v___x_955_);
v___x_957_ = lean_uint64_to_usize(v___x_956_);
v___x_958_ = lean_usize_of_nat(v___x_949_);
v___x_959_ = ((size_t)1ULL);
v___x_960_ = lean_usize_sub(v___x_958_, v___x_959_);
v___x_961_ = lean_usize_land(v___x_957_, v___x_960_);
v_bkt_962_ = lean_array_uget_borrowed(v_buckets_945_, v___x_961_);
v___x_963_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(v_a_942_, v_bkt_962_);
if (v___x_963_ == 0)
{
lean_object* v___x_964_; lean_object* v_size_x27_965_; lean_object* v___x_966_; lean_object* v_buckets_x27_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; uint8_t v___x_973_; 
v___x_964_ = lean_unsigned_to_nat(1u);
v_size_x27_965_ = lean_nat_add(v_size_944_, v___x_964_);
lean_dec(v_size_944_);
lean_inc(v_bkt_962_);
v___x_966_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_966_, 0, v_a_942_);
lean_ctor_set(v___x_966_, 1, v_b_943_);
lean_ctor_set(v___x_966_, 2, v_bkt_962_);
v_buckets_x27_967_ = lean_array_uset(v_buckets_945_, v___x_961_, v___x_966_);
v___x_968_ = lean_unsigned_to_nat(4u);
v___x_969_ = lean_nat_mul(v_size_x27_965_, v___x_968_);
v___x_970_ = lean_unsigned_to_nat(3u);
v___x_971_ = lean_nat_div(v___x_969_, v___x_970_);
lean_dec(v___x_969_);
v___x_972_ = lean_array_get_size(v_buckets_x27_967_);
v___x_973_ = lean_nat_dec_le(v___x_971_, v___x_972_);
lean_dec(v___x_971_);
if (v___x_973_ == 0)
{
lean_object* v_val_974_; lean_object* v___x_976_; 
v_val_974_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11___redArg(v_buckets_x27_967_);
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 1, v_val_974_);
lean_ctor_set(v___x_947_, 0, v_size_x27_965_);
v___x_976_ = v___x_947_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_size_x27_965_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v_val_974_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
else
{
lean_object* v___x_979_; 
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 1, v_buckets_x27_967_);
lean_ctor_set(v___x_947_, 0, v_size_x27_965_);
v___x_979_ = v___x_947_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_size_x27_965_);
lean_ctor_set(v_reuseFailAlloc_980_, 1, v_buckets_x27_967_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
else
{
lean_object* v___x_981_; lean_object* v_buckets_x27_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_986_; 
lean_inc(v_bkt_962_);
v___x_981_ = lean_box(0);
v_buckets_x27_982_ = lean_array_uset(v_buckets_945_, v___x_961_, v___x_981_);
v___x_983_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12___redArg(v_a_942_, v_b_943_, v_bkt_962_);
v___x_984_ = lean_array_uset(v_buckets_x27_982_, v___x_961_, v___x_983_);
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 1, v___x_984_);
v___x_986_ = v___x_947_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_size_944_);
lean_ctor_set(v_reuseFailAlloc_987_, 1, v___x_984_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2(lean_object* v_a_989_, lean_object* v_e_990_, lean_object* v_a_991_){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_993_ = lean_st_ref_take(v_a_989_);
v___x_994_ = lean_box(0);
v___x_995_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6___redArg(v___x_993_, v_e_990_, v_a_991_);
v___x_996_ = lean_st_ref_put(v_a_989_, v___x_995_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2___boxed(lean_object* v_a_997_, lean_object* v_e_998_, lean_object* v_a_999_, lean_object* v___y_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2(v_a_997_, v_e_998_, v_a_999_);
lean_dec(v_a_997_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_1002_, lean_object* v_x_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1007_ = lean_apply_1(v_x_1003_, lean_box(0));
v___x_1008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1009_, lean_object* v_x_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(v_00_u03b1_1009_, v_x_1010_, v___y_1011_, v___y_1012_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
return v_res_1014_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0(void){
_start:
{
lean_object* v___x_1016_; lean_object* v_dummy_1017_; 
v___x_1016_ = lean_box(0);
v_dummy_1017_ = l_Lean_Expr_sort___override(v___x_1016_);
return v_dummy_1017_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1(lean_object* v_pre_1018_, lean_object* v_post_1019_, size_t v_sz_1020_, size_t v_i_1021_, lean_object* v_bs_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_){
_start:
{
uint8_t v___x_1027_; 
v___x_1027_ = lean_usize_dec_lt(v_i_1021_, v_sz_1020_);
if (v___x_1027_ == 0)
{
lean_object* v___x_1028_; 
lean_dec_ref(v_post_1019_);
lean_dec_ref(v_pre_1018_);
v___x_1028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1028_, 0, v_bs_1022_);
return v___x_1028_;
}
else
{
lean_object* v_v_1029_; lean_object* v___x_1030_; lean_object* v_bs_x27_1031_; lean_object* v___x_1032_; 
v_v_1029_ = lean_array_uget(v_bs_1022_, v_i_1021_);
v___x_1030_ = lean_unsigned_to_nat(0u);
v_bs_x27_1031_ = lean_array_uset(v_bs_1022_, v_i_1021_, v___x_1030_);
lean_inc_ref(v_post_1019_);
lean_inc_ref(v_pre_1018_);
v___x_1032_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1018_, v_post_1019_, v_v_1029_, v___y_1023_, v___y_1024_, v___y_1025_);
if (lean_obj_tag(v___x_1032_) == 0)
{
lean_object* v_a_1033_; size_t v___x_1034_; size_t v___x_1035_; lean_object* v___x_1036_; 
v_a_1033_ = lean_ctor_get(v___x_1032_, 0);
lean_inc(v_a_1033_);
lean_dec_ref_known(v___x_1032_, 1);
v___x_1034_ = ((size_t)1ULL);
v___x_1035_ = lean_usize_add(v_i_1021_, v___x_1034_);
v___x_1036_ = lean_array_uset(v_bs_x27_1031_, v_i_1021_, v_a_1033_);
v_i_1021_ = v___x_1035_;
v_bs_1022_ = v___x_1036_;
goto _start;
}
else
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1045_; 
lean_dec_ref(v_bs_x27_1031_);
lean_dec_ref(v_post_1019_);
lean_dec_ref(v_pre_1018_);
v_a_1038_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1040_ = v___x_1032_;
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_1032_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1043_; 
if (v_isShared_1041_ == 0)
{
v___x_1043_ = v___x_1040_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_a_1038_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4(lean_object* v_pre_1046_, lean_object* v_post_1047_, lean_object* v_x_1048_, lean_object* v_x_1049_, lean_object* v_x_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_){
_start:
{
if (lean_obj_tag(v_x_1048_) == 5)
{
lean_object* v_fn_1055_; lean_object* v_arg_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v_fn_1055_ = lean_ctor_get(v_x_1048_, 0);
lean_inc_ref(v_fn_1055_);
v_arg_1056_ = lean_ctor_get(v_x_1048_, 1);
lean_inc_ref(v_arg_1056_);
lean_dec_ref_known(v_x_1048_, 2);
v___x_1057_ = lean_array_set(v_x_1049_, v_x_1050_, v_arg_1056_);
v___x_1058_ = lean_unsigned_to_nat(1u);
v___x_1059_ = lean_nat_sub(v_x_1050_, v___x_1058_);
lean_dec(v_x_1050_);
v_x_1048_ = v_fn_1055_;
v_x_1049_ = v___x_1057_;
v_x_1050_ = v___x_1059_;
goto _start;
}
else
{
lean_object* v___x_1061_; 
lean_dec(v_x_1050_);
lean_inc_ref(v_post_1047_);
lean_inc_ref(v_pre_1046_);
v___x_1061_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1046_, v_post_1047_, v_x_1048_, v___y_1051_, v___y_1052_, v___y_1053_);
if (lean_obj_tag(v___x_1061_) == 0)
{
lean_object* v_a_1062_; size_t v_sz_1063_; size_t v___x_1064_; lean_object* v___x_1065_; 
v_a_1062_ = lean_ctor_get(v___x_1061_, 0);
lean_inc(v_a_1062_);
lean_dec_ref_known(v___x_1061_, 1);
v_sz_1063_ = lean_array_size(v_x_1049_);
v___x_1064_ = ((size_t)0ULL);
lean_inc_ref(v_post_1047_);
lean_inc_ref(v_pre_1046_);
v___x_1065_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1(v_pre_1046_, v_post_1047_, v_sz_1063_, v___x_1064_, v_x_1049_, v___y_1051_, v___y_1052_, v___y_1053_);
if (lean_obj_tag(v___x_1065_) == 0)
{
lean_object* v_a_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
v_a_1066_ = lean_ctor_get(v___x_1065_, 0);
lean_inc(v_a_1066_);
lean_dec_ref_known(v___x_1065_, 1);
v___x_1067_ = l_Lean_mkAppN(v_a_1062_, v_a_1066_);
lean_dec(v_a_1066_);
v___x_1068_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1046_, v_post_1047_, v___x_1067_, v___y_1051_, v___y_1052_, v___y_1053_);
return v___x_1068_;
}
else
{
lean_object* v_a_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1076_; 
lean_dec(v_a_1062_);
lean_dec_ref(v_post_1047_);
lean_dec_ref(v_pre_1046_);
v_a_1069_ = lean_ctor_get(v___x_1065_, 0);
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_1065_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1071_ = v___x_1065_;
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_a_1069_);
lean_dec(v___x_1065_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1074_; 
if (v_isShared_1072_ == 0)
{
v___x_1074_ = v___x_1071_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_a_1069_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
}
}
else
{
lean_dec_ref(v_x_1049_);
lean_dec_ref(v_post_1047_);
lean_dec_ref(v_pre_1046_);
return v___x_1061_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1(lean_object* v___x_1077_, lean_object* v_pre_1078_, lean_object* v_e_1079_, lean_object* v_post_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
lean_object* v___x_1085_; 
v___x_1085_ = l_Lean_Core_checkSystem(v___x_1077_, v___y_1082_, v___y_1083_);
if (lean_obj_tag(v___x_1085_) == 0)
{
lean_object* v___x_1086_; 
lean_dec_ref_known(v___x_1085_, 1);
lean_inc_ref(v_pre_1078_);
lean_inc(v___y_1083_);
lean_inc_ref(v___y_1082_);
lean_inc_ref(v_e_1079_);
v___x_1086_ = lean_apply_4(v_pre_1078_, v_e_1079_, v___y_1082_, v___y_1083_, lean_box(0));
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1202_; 
v_a_1087_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1089_ = v___x_1086_;
v_isShared_1090_ = v_isSharedCheck_1202_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1086_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1202_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___y_1092_; 
switch(lean_obj_tag(v_a_1087_))
{
case 0:
{
lean_object* v_e_1192_; lean_object* v___x_1194_; 
lean_dec_ref(v_post_1080_);
lean_dec_ref(v_e_1079_);
lean_dec_ref(v_pre_1078_);
v_e_1192_ = lean_ctor_get(v_a_1087_, 0);
lean_inc_ref(v_e_1192_);
lean_dec_ref_known(v_a_1087_, 1);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 0, v_e_1192_);
v___x_1194_ = v___x_1089_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_e_1192_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
case 1:
{
lean_object* v_e_1196_; lean_object* v___x_1197_; 
lean_del_object(v___x_1089_);
lean_dec_ref(v_e_1079_);
v_e_1196_ = lean_ctor_get(v_a_1087_, 0);
lean_inc_ref(v_e_1196_);
lean_dec_ref_known(v_a_1087_, 1);
lean_inc_ref(v_post_1080_);
lean_inc_ref(v_pre_1078_);
v___x_1197_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1078_, v_post_1080_, v_e_1196_, v___y_1081_, v___y_1082_, v___y_1083_);
if (lean_obj_tag(v___x_1197_) == 0)
{
lean_object* v_a_1198_; lean_object* v___x_1199_; 
v_a_1198_ = lean_ctor_get(v___x_1197_, 0);
lean_inc(v_a_1198_);
lean_dec_ref_known(v___x_1197_, 1);
v___x_1199_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1078_, v_post_1080_, v_a_1198_, v___y_1081_, v___y_1082_, v___y_1083_);
return v___x_1199_;
}
else
{
lean_dec_ref(v_post_1080_);
lean_dec_ref(v_pre_1078_);
return v___x_1197_;
}
}
default: 
{
lean_object* v_e_x3f_1200_; 
lean_del_object(v___x_1089_);
v_e_x3f_1200_ = lean_ctor_get(v_a_1087_, 0);
lean_inc(v_e_x3f_1200_);
lean_dec_ref_known(v_a_1087_, 1);
if (lean_obj_tag(v_e_x3f_1200_) == 0)
{
v___y_1092_ = v_e_1079_;
goto v___jp_1091_;
}
else
{
lean_object* v_val_1201_; 
lean_dec_ref(v_e_1079_);
v_val_1201_ = lean_ctor_get(v_e_x3f_1200_, 0);
lean_inc(v_val_1201_);
lean_dec_ref_known(v_e_x3f_1200_, 1);
v___y_1092_ = v_val_1201_;
goto v___jp_1091_;
}
}
}
v___jp_1091_:
{
switch(lean_obj_tag(v___y_1092_))
{
case 7:
{
lean_object* v_binderName_1093_; lean_object* v_binderType_1094_; lean_object* v_body_1095_; uint8_t v_binderInfo_1096_; lean_object* v___x_1097_; 
v_binderName_1093_ = lean_ctor_get(v___y_1092_, 0);
v_binderType_1094_ = lean_ctor_get(v___y_1092_, 1);
v_body_1095_ = lean_ctor_get(v___y_1092_, 2);
v_binderInfo_1096_ = lean_ctor_get_uint8(v___y_1092_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1094_);
lean_inc_ref(v_post_1080_);
lean_inc_ref(v_pre_1078_);
v___x_1097_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1078_, v_post_1080_, v_binderType_1094_, v___y_1081_, v___y_1082_, v___y_1083_);
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_object* v_a_1098_; lean_object* v___x_1099_; 
v_a_1098_ = lean_ctor_get(v___x_1097_, 0);
lean_inc(v_a_1098_);
lean_dec_ref_known(v___x_1097_, 1);
lean_inc_ref(v_body_1095_);
lean_inc_ref(v_post_1080_);
lean_inc_ref(v_pre_1078_);
v___x_1099_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1078_, v_post_1080_, v_body_1095_, v___y_1081_, v___y_1082_, v___y_1083_);
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_object* v_a_1100_; size_t v___x_1101_; size_t v___x_1102_; uint8_t v___x_1103_; 
v_a_1100_ = lean_ctor_get(v___x_1099_, 0);
lean_inc(v_a_1100_);
lean_dec_ref_known(v___x_1099_, 1);
v___x_1101_ = lean_ptr_addr(v_binderType_1094_);
v___x_1102_ = lean_ptr_addr(v_a_1098_);
v___x_1103_ = lean_usize_dec_eq(v___x_1101_, v___x_1102_);
if (v___x_1103_ == 0)
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
lean_inc(v_binderName_1093_);
lean_dec_ref_known(v___y_1092_, 3);
v___x_1104_ = l_Lean_Expr_forallE___override(v_binderName_1093_, v_a_1098_, v_a_1100_, v_binderInfo_1096_);
v___x_1105_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1078_, v_post_1080_, v___x_1104_, v___y_1081_, v___y_1082_, v___y_1083_);
return v___x_1105_;
}
else
{
size_t v___x_1106_; size_t v___x_1107_; uint8_t v___x_1108_; 
v___x_1106_ = lean_ptr_addr(v_body_1095_);
v___x_1107_ = lean_ptr_addr(v_a_1100_);
v___x_1108_ = lean_usize_dec_eq(v___x_1106_, v___x_1107_);
if (v___x_1108_ == 0)
{
lean_object* v___x_1109_; lean_object* v___x_1110_; 
lean_inc(v_binderName_1093_);
lean_dec_ref_known(v___y_1092_, 3);
v___x_1109_ = l_Lean_Expr_forallE___override(v_binderName_1093_, v_a_1098_, v_a_1100_, v_binderInfo_1096_);
v___x_1110_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1078_, v_post_1080_, v___x_1109_, v___y_1081_, v___y_1082_, v___y_1083_);
return v___x_1110_;
}
else
{
uint8_t v___x_1111_; 
v___x_1111_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1096_, v_binderInfo_1096_);
if (v___x_1111_ == 0)
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
lean_inc(v_binderName_1093_);
lean_dec_ref_known(v___y_1092_, 3);
v___x_1112_ = l_Lean_Expr_forallE___override(v_binderName_1093_, v_a_1098_, v_a_1100_, v_binderInfo_1096_);
v___x_1113_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1078_, v_post_1080_, v___x_1112_, v___y_1081_, v___y_1082_, v___y_1083_);
return v___x_1113_;
}
else
{
lean_object* v___x_1114_; 
lean_dec(v_a_1100_);
lean_dec(v_a_1098_);
v___x_1114_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1078_, v_post_1080_, v___y_1092_, v___y_1081_, v___y_1082_, v___y_1083_);
return v___x_1114_;
}
}
}
}
else
{
lean_dec(v_a_1098_);
lean_dec_ref_known(v___y_1092_, 3);
lean_dec_ref(v_post_1080_);
lean_dec_ref(v_pre_1078_);
return v___x_1099_;
}
}
else
{
lean_dec_ref_known(v___y_1092_, 3);
lean_dec_ref(v_post_1080_);
lean_dec_ref(v_pre_1078_);
return v___x_1097_;
}
}
case 6:
{
lean_object* v_binderName_1115_; lean_object* v_binderType_1116_; lean_object* v_body_1117_; uint8_t v_binderInfo_1118_; lean_object* v___x_1119_; 
v_binderName_1115_ = lean_ctor_get(v___y_1092_, 0);
v_binderType_1116_ = lean_ctor_get(v___y_1092_, 1);
v_body_1117_ = lean_ctor_get(v___y_1092_, 2);
v_binderInfo_1118_ = lean_ctor_get_uint8(v___y_1092_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1116_);
lean_inc_ref(v_post_1080_);
lean_inc_ref(v_pre_1078_);
v___x_1119_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1078_, v_post_1080_, v_binderType_1116_, v___y_1081_, v___y_1082_, v___y_1083_);
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v_a_1120_; lean_object* v___x_1121_; 
v_a_1120_ = lean_ctor_get(v___x_1119_, 0);
lean_inc(v_a_1120_);
lean_dec_ref_known(v___x_1119_, 1);
lean_inc_ref(v_body_1117_);
lean_inc_ref(v_post_1080_);
lean_inc_ref(v_pre_1078_);
v___x_1121_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1078_, v_post_1080_, v_body_1117_, v___y_1081_, v___y_1082_, v___y_1083_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v_a_1122_; size_t v___x_1123_; size_t v___x_1124_; uint8_t v___x_1125_; 
v_a_1122_ = lean_ctor_get(v___x_1121_, 0);
lean_inc(v_a_1122_);
lean_dec_ref_known(v___x_1121_, 1);
v___x_1123_ = lean_ptr_addr(v_binderType_1116_);
v___x_1124_ = lean_ptr_addr(v_a_1120_);
v___x_1125_ = lean_usize_dec_eq(v___x_1123_, v___x_1124_);
if (v___x_1125_ == 0)
{
lean_object* v___x_1126_; lean_object* v___x_1127_; 
lean_inc(v_binderName_1115_);
lean_dec_ref_known(v___y_1092_, 3);
v___x_1126_ = l_Lean_Expr_lam___override(v_binderName_1115_, v_a_1120_, v_a_1122_, v_binderInfo_1118_);
v___x_1127_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1078_, v_post_1080_, v___x_1126_, v___y_1081_, v___y_1082_, v___y_1083_);
return v___x_1127_;
}
else
{
size_t v___x_1128_; size_t v___x_1129_; uint8_t v___x_1130_; 
v___x_1128_ = lean_ptr_addr(v_body_1117_);
v___x_1129_ = lean_ptr_addr(v_a_1122_);
v___x_1130_ = lean_usize_dec_eq(v___x_1128_, v___x_1129_);
if (v___x_1130_ == 0)
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
lean_inc(v_binderName_1115_);
lean_dec_ref_known(v___y_1092_, 3);
v___x_1131_ = l_Lean_Expr_lam___override(v_binderName_1115_, v_a_1120_, v_a_1122_, v_binderInfo_1118_);
v___x_1132_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1078_, v_post_1080_, v___x_1131_, v___y_1081_, v___y_1082_, v___y_1083_);
return v___x_1132_;
}
else
{
uint8_t v___x_1133_; 
v___x_1133_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1118_, v_binderInfo_1118_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
lean_inc(v_binderName_1115_);
lean_dec_ref_known(v___y_1092_, 3);
v___x_1134_ = l_Lean_Expr_lam___override(v_binderName_1115_, v_a_1120_, v_a_1122_, v_binderInfo_1118_);
v___x_1135_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1078_, v_post_1080_, v___x_1134_, v___y_1081_, v___y_1082_, v___y_1083_);
return v___x_1135_;
}
else
{
lean_object* v___x_1136_; 
lean_dec(v_a_1122_);
lean_dec(v_a_1120_);
v___x_1136_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1078_, v_post_1080_, v___y_1092_, v___y_1081_, v___y_1082_, v___y_1083_);
return v___x_1136_;
}
}
}
}
else
{
lean_dec(v_a_1120_);
lean_dec_ref_known(v___y_1092_, 3);
lean_dec_ref(v_post_1080_);
lean_dec_ref(v_pre_1078_);
return v___x_1121_;
}
}
else
{
lean_dec_ref_known(v___y_1092_, 3);
lean_dec_ref(v_post_1080_);
lean_dec_ref(v_pre_1078_);
return v___x_1119_;
}
}
case 8:
{
lean_object* v_declName_1137_; lean_object* v_type_1138_; lean_object* v_value_1139_; lean_object* v_body_1140_; uint8_t v_nondep_1141_; lean_object* v___x_1142_; 
v_declName_1137_ = lean_ctor_get(v___y_1092_, 0);
v_type_1138_ = lean_ctor_get(v___y_1092_, 1);
v_value_1139_ = lean_ctor_get(v___y_1092_, 2);
v_body_1140_ = lean_ctor_get(v___y_1092_, 3);
v_nondep_1141_ = lean_ctor_get_uint8(v___y_1092_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_1138_);
lean_inc_ref(v_post_1080_);
lean_inc_ref(v_pre_1078_);
v___x_1142_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1078_, v_post_1080_, v_type_1138_, v___y_1081_, v___y_1082_, v___y_1083_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_object* v_a_1143_; lean_object* v___x_1144_; 
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
lean_inc(v_a_1143_);
lean_dec_ref_known(v___x_1142_, 1);
lean_inc_ref(v_value_1139_);
lean_inc_ref(v_post_1080_);
lean_inc_ref(v_pre_1078_);
v___x_1144_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1078_, v_post_1080_, v_value_1139_, v___y_1081_, v___y_1082_, v___y_1083_);
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_object* v_a_1145_; lean_object* v___x_1146_; 
v_a_1145_ = lean_ctor_get(v___x_1144_, 0);
lean_inc(v_a_1145_);
lean_dec_ref_known(v___x_1144_, 1);
lean_inc_ref(v_body_1140_);
lean_inc_ref(v_post_1080_);
lean_inc_ref(v_pre_1078_);
v___x_1146_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1078_, v_post_1080_, v_body_1140_, v___y_1081_, v___y_1082_, v___y_1083_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v_a_1147_; size_t v___x_1148_; size_t v___x_1149_; uint8_t v___x_1150_; 
v_a_1147_ = lean_ctor_get(v___x_1146_, 0);
lean_inc(v_a_1147_);
lean_dec_ref_known(v___x_1146_, 1);
v___x_1148_ = lean_ptr_addr(v_type_1138_);
v___x_1149_ = lean_ptr_addr(v_a_1143_);
v___x_1150_ = lean_usize_dec_eq(v___x_1148_, v___x_1149_);
if (v___x_1150_ == 0)
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
lean_inc(v_declName_1137_);
lean_dec_ref_known(v___y_1092_, 4);
v___x_1151_ = l_Lean_Expr_letE___override(v_declName_1137_, v_a_1143_, v_a_1145_, v_a_1147_, v_nondep_1141_);
v___x_1152_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1078_, v_post_1080_, v___x_1151_, v___y_1081_, v___y_1082_, v___y_1083_);
return v___x_1152_;
}
else
{
size_t v___x_1153_; size_t v___x_1154_; uint8_t v___x_1155_; 
v___x_1153_ = lean_ptr_addr(v_value_1139_);
v___x_1154_ = lean_ptr_addr(v_a_1145_);
v___x_1155_ = lean_usize_dec_eq(v___x_1153_, v___x_1154_);
if (v___x_1155_ == 0)
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
lean_inc(v_declName_1137_);
lean_dec_ref_known(v___y_1092_, 4);
v___x_1156_ = l_Lean_Expr_letE___override(v_declName_1137_, v_a_1143_, v_a_1145_, v_a_1147_, v_nondep_1141_);
v___x_1157_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1078_, v_post_1080_, v___x_1156_, v___y_1081_, v___y_1082_, v___y_1083_);
return v___x_1157_;
}
else
{
size_t v___x_1158_; size_t v___x_1159_; uint8_t v___x_1160_; 
v___x_1158_ = lean_ptr_addr(v_body_1140_);
v___x_1159_ = lean_ptr_addr(v_a_1147_);
v___x_1160_ = lean_usize_dec_eq(v___x_1158_, v___x_1159_);
if (v___x_1160_ == 0)
{
lean_object* v___x_1161_; lean_object* v___x_1162_; 
lean_inc(v_declName_1137_);
lean_dec_ref_known(v___y_1092_, 4);
v___x_1161_ = l_Lean_Expr_letE___override(v_declName_1137_, v_a_1143_, v_a_1145_, v_a_1147_, v_nondep_1141_);
v___x_1162_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1078_, v_post_1080_, v___x_1161_, v___y_1081_, v___y_1082_, v___y_1083_);
return v___x_1162_;
}
else
{
lean_object* v___x_1163_; 
lean_dec(v_a_1147_);
lean_dec(v_a_1145_);
lean_dec(v_a_1143_);
v___x_1163_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1078_, v_post_1080_, v___y_1092_, v___y_1081_, v___y_1082_, v___y_1083_);
return v___x_1163_;
}
}
}
}
else
{
lean_dec(v_a_1145_);
lean_dec(v_a_1143_);
lean_dec_ref_known(v___y_1092_, 4);
lean_dec_ref(v_post_1080_);
lean_dec_ref(v_pre_1078_);
return v___x_1146_;
}
}
else
{
lean_dec(v_a_1143_);
lean_dec_ref_known(v___y_1092_, 4);
lean_dec_ref(v_post_1080_);
lean_dec_ref(v_pre_1078_);
return v___x_1144_;
}
}
else
{
lean_dec_ref_known(v___y_1092_, 4);
lean_dec_ref(v_post_1080_);
lean_dec_ref(v_pre_1078_);
return v___x_1142_;
}
}
case 5:
{
lean_object* v_dummy_1164_; lean_object* v_nargs_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; 
v_dummy_1164_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0);
v_nargs_1165_ = l_Lean_Expr_getAppNumArgs(v___y_1092_);
lean_inc(v_nargs_1165_);
v___x_1166_ = lean_mk_array(v_nargs_1165_, v_dummy_1164_);
v___x_1167_ = lean_unsigned_to_nat(1u);
v___x_1168_ = lean_nat_sub(v_nargs_1165_, v___x_1167_);
lean_dec(v_nargs_1165_);
v___x_1169_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4(v_pre_1078_, v_post_1080_, v___y_1092_, v___x_1166_, v___x_1168_, v___y_1081_, v___y_1082_, v___y_1083_);
return v___x_1169_;
}
case 10:
{
lean_object* v_data_1170_; lean_object* v_expr_1171_; lean_object* v___x_1172_; 
v_data_1170_ = lean_ctor_get(v___y_1092_, 0);
v_expr_1171_ = lean_ctor_get(v___y_1092_, 1);
lean_inc_ref(v_expr_1171_);
lean_inc_ref(v_post_1080_);
lean_inc_ref(v_pre_1078_);
v___x_1172_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1078_, v_post_1080_, v_expr_1171_, v___y_1081_, v___y_1082_, v___y_1083_);
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_object* v_a_1173_; size_t v___x_1174_; size_t v___x_1175_; uint8_t v___x_1176_; 
v_a_1173_ = lean_ctor_get(v___x_1172_, 0);
lean_inc(v_a_1173_);
lean_dec_ref_known(v___x_1172_, 1);
v___x_1174_ = lean_ptr_addr(v_expr_1171_);
v___x_1175_ = lean_ptr_addr(v_a_1173_);
v___x_1176_ = lean_usize_dec_eq(v___x_1174_, v___x_1175_);
if (v___x_1176_ == 0)
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
lean_inc(v_data_1170_);
lean_dec_ref_known(v___y_1092_, 2);
v___x_1177_ = l_Lean_Expr_mdata___override(v_data_1170_, v_a_1173_);
v___x_1178_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1078_, v_post_1080_, v___x_1177_, v___y_1081_, v___y_1082_, v___y_1083_);
return v___x_1178_;
}
else
{
lean_object* v___x_1179_; 
lean_dec(v_a_1173_);
v___x_1179_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1078_, v_post_1080_, v___y_1092_, v___y_1081_, v___y_1082_, v___y_1083_);
return v___x_1179_;
}
}
else
{
lean_dec_ref_known(v___y_1092_, 2);
lean_dec_ref(v_post_1080_);
lean_dec_ref(v_pre_1078_);
return v___x_1172_;
}
}
case 11:
{
lean_object* v_typeName_1180_; lean_object* v_idx_1181_; lean_object* v_struct_1182_; lean_object* v___x_1183_; 
v_typeName_1180_ = lean_ctor_get(v___y_1092_, 0);
v_idx_1181_ = lean_ctor_get(v___y_1092_, 1);
v_struct_1182_ = lean_ctor_get(v___y_1092_, 2);
lean_inc_ref(v_struct_1182_);
lean_inc_ref(v_post_1080_);
lean_inc_ref(v_pre_1078_);
v___x_1183_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1078_, v_post_1080_, v_struct_1182_, v___y_1081_, v___y_1082_, v___y_1083_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v_a_1184_; size_t v___x_1185_; size_t v___x_1186_; uint8_t v___x_1187_; 
v_a_1184_ = lean_ctor_get(v___x_1183_, 0);
lean_inc(v_a_1184_);
lean_dec_ref_known(v___x_1183_, 1);
v___x_1185_ = lean_ptr_addr(v_struct_1182_);
v___x_1186_ = lean_ptr_addr(v_a_1184_);
v___x_1187_ = lean_usize_dec_eq(v___x_1185_, v___x_1186_);
if (v___x_1187_ == 0)
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
lean_inc(v_idx_1181_);
lean_inc(v_typeName_1180_);
lean_dec_ref_known(v___y_1092_, 3);
v___x_1188_ = l_Lean_Expr_proj___override(v_typeName_1180_, v_idx_1181_, v_a_1184_);
v___x_1189_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1078_, v_post_1080_, v___x_1188_, v___y_1081_, v___y_1082_, v___y_1083_);
return v___x_1189_;
}
else
{
lean_object* v___x_1190_; 
lean_dec(v_a_1184_);
v___x_1190_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1078_, v_post_1080_, v___y_1092_, v___y_1081_, v___y_1082_, v___y_1083_);
return v___x_1190_;
}
}
else
{
lean_dec_ref_known(v___y_1092_, 3);
lean_dec_ref(v_post_1080_);
lean_dec_ref(v_pre_1078_);
return v___x_1183_;
}
}
default: 
{
lean_object* v___x_1191_; 
v___x_1191_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1078_, v_post_1080_, v___y_1092_, v___y_1081_, v___y_1082_, v___y_1083_);
return v___x_1191_;
}
}
}
}
}
else
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1210_; 
lean_dec_ref(v_post_1080_);
lean_dec_ref(v_e_1079_);
lean_dec_ref(v_pre_1078_);
v_a_1203_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1205_ = v___x_1086_;
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_1086_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1208_; 
if (v_isShared_1206_ == 0)
{
v___x_1208_ = v___x_1205_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_a_1203_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
}
else
{
lean_object* v_a_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1218_; 
lean_dec_ref(v_post_1080_);
lean_dec_ref(v_e_1079_);
lean_dec_ref(v_pre_1078_);
v_a_1211_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1213_ = v___x_1085_;
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_a_1211_);
lean_dec(v___x_1085_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1216_; 
if (v_isShared_1214_ == 0)
{
v___x_1216_ = v___x_1213_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_a_1211_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___boxed(lean_object* v___x_1219_, lean_object* v_pre_1220_, lean_object* v_e_1221_, lean_object* v_post_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1(v___x_1219_, v_pre_1220_, v_e_1221_, v_post_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec(v___y_1223_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(lean_object* v_pre_1228_, lean_object* v_post_1229_, lean_object* v_e_1230_, lean_object* v_a_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; 
lean_inc(v_a_1231_);
v___x_1235_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1235_, 0, lean_box(0));
lean_closure_set(v___x_1235_, 1, lean_box(0));
lean_closure_set(v___x_1235_, 2, v_a_1231_);
v___x_1236_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(lean_box(0), v___x_1235_, v___y_1232_, v___y_1233_);
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_object* v_a_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1268_; 
v_a_1237_ = lean_ctor_get(v___x_1236_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1239_ = v___x_1236_;
v_isShared_1240_ = v_isSharedCheck_1268_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_a_1237_);
lean_dec(v___x_1236_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1268_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1241_; 
v___x_1241_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg(v_a_1237_, v_e_1230_);
lean_dec(v_a_1237_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v___x_1242_; lean_object* v___f_1243_; lean_object* v___x_1244_; 
lean_del_object(v___x_1239_);
v___x_1242_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___closed__0));
lean_inc_ref(v_e_1230_);
v___f_1243_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___boxed), 8, 4);
lean_closure_set(v___f_1243_, 0, v___x_1242_);
lean_closure_set(v___f_1243_, 1, v_pre_1228_);
lean_closure_set(v___f_1243_, 2, v_e_1230_);
lean_closure_set(v___f_1243_, 3, v_post_1229_);
v___x_1244_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg(v___f_1243_, v_a_1231_, v___y_1232_, v___y_1233_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_object* v_a_1245_; lean_object* v___f_1246_; lean_object* v___x_1247_; 
v_a_1245_ = lean_ctor_get(v___x_1244_, 0);
lean_inc_n(v_a_1245_, 2);
lean_dec_ref_known(v___x_1244_, 1);
lean_inc(v_a_1231_);
v___f_1246_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1246_, 0, v_a_1231_);
lean_closure_set(v___f_1246_, 1, v_e_1230_);
lean_closure_set(v___f_1246_, 2, v_a_1245_);
v___x_1247_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(lean_box(0), v___f_1246_, v___y_1232_, v___y_1233_);
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1254_; 
v_isSharedCheck_1254_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1254_ == 0)
{
lean_object* v_unused_1255_; 
v_unused_1255_ = lean_ctor_get(v___x_1247_, 0);
lean_dec(v_unused_1255_);
v___x_1249_ = v___x_1247_;
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
else
{
lean_dec(v___x_1247_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1252_; 
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 0, v_a_1245_);
v___x_1252_ = v___x_1249_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_a_1245_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
return v___x_1252_;
}
}
}
else
{
lean_object* v_a_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1263_; 
lean_dec(v_a_1245_);
v_a_1256_ = lean_ctor_get(v___x_1247_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1258_ = v___x_1247_;
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_a_1256_);
lean_dec(v___x_1247_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1261_; 
if (v_isShared_1259_ == 0)
{
v___x_1261_ = v___x_1258_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_a_1256_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
}
}
else
{
lean_dec_ref(v_e_1230_);
return v___x_1244_;
}
}
else
{
lean_object* v_val_1264_; lean_object* v___x_1266_; 
lean_dec_ref(v_e_1230_);
lean_dec_ref(v_post_1229_);
lean_dec_ref(v_pre_1228_);
v_val_1264_ = lean_ctor_get(v___x_1241_, 0);
lean_inc(v_val_1264_);
lean_dec_ref_known(v___x_1241_, 1);
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 0, v_val_1264_);
v___x_1266_ = v___x_1239_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_val_1264_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
}
else
{
lean_object* v_a_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1276_; 
lean_dec_ref(v_e_1230_);
lean_dec_ref(v_post_1229_);
lean_dec_ref(v_pre_1228_);
v_a_1269_ = lean_ctor_get(v___x_1236_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1271_ = v___x_1236_;
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_a_1269_);
lean_dec(v___x_1236_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1274_; 
if (v_isShared_1272_ == 0)
{
v___x_1274_ = v___x_1271_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_a_1269_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(lean_object* v_pre_1277_, lean_object* v_post_1278_, lean_object* v_e_1279_, lean_object* v_a_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_){
_start:
{
lean_object* v___x_1284_; 
lean_inc_ref(v_post_1278_);
lean_inc(v___y_1282_);
lean_inc_ref(v___y_1281_);
lean_inc_ref(v_e_1279_);
v___x_1284_ = lean_apply_4(v_post_1278_, v_e_1279_, v___y_1281_, v___y_1282_, lean_box(0));
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1303_; 
v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1287_ = v___x_1284_;
v_isShared_1288_ = v_isSharedCheck_1303_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1284_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1303_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
switch(lean_obj_tag(v_a_1285_))
{
case 0:
{
lean_object* v_e_1289_; lean_object* v___x_1291_; 
lean_dec_ref(v_e_1279_);
lean_dec_ref(v_post_1278_);
lean_dec_ref(v_pre_1277_);
v_e_1289_ = lean_ctor_get(v_a_1285_, 0);
lean_inc_ref(v_e_1289_);
lean_dec_ref_known(v_a_1285_, 1);
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 0, v_e_1289_);
v___x_1291_ = v___x_1287_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_e_1289_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
case 1:
{
lean_object* v_e_1293_; lean_object* v___x_1294_; 
lean_del_object(v___x_1287_);
lean_dec_ref(v_e_1279_);
v_e_1293_ = lean_ctor_get(v_a_1285_, 0);
lean_inc_ref(v_e_1293_);
lean_dec_ref_known(v_a_1285_, 1);
v___x_1294_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1277_, v_post_1278_, v_e_1293_, v_a_1280_, v___y_1281_, v___y_1282_);
return v___x_1294_;
}
default: 
{
lean_object* v_e_x3f_1295_; 
lean_dec_ref(v_post_1278_);
lean_dec_ref(v_pre_1277_);
v_e_x3f_1295_ = lean_ctor_get(v_a_1285_, 0);
lean_inc(v_e_x3f_1295_);
lean_dec_ref_known(v_a_1285_, 1);
if (lean_obj_tag(v_e_x3f_1295_) == 0)
{
lean_object* v___x_1297_; 
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 0, v_e_1279_);
v___x_1297_ = v___x_1287_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_e_1279_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
else
{
lean_object* v_val_1299_; lean_object* v___x_1301_; 
lean_dec_ref(v_e_1279_);
v_val_1299_ = lean_ctor_get(v_e_x3f_1295_, 0);
lean_inc(v_val_1299_);
lean_dec_ref_known(v_e_x3f_1295_, 1);
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 0, v_val_1299_);
v___x_1301_ = v___x_1287_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_val_1299_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
}
}
else
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1311_; 
lean_dec_ref(v_e_1279_);
lean_dec_ref(v_post_1278_);
lean_dec_ref(v_pre_1277_);
v_a_1304_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1306_ = v___x_1284_;
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1284_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1307_ == 0)
{
v___x_1309_ = v___x_1306_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1304_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_1312_, lean_object* v_post_1313_, lean_object* v_e_1314_, lean_object* v_a_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_){
_start:
{
lean_object* v_res_1319_; 
v_res_1319_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1312_, v_post_1313_, v_e_1314_, v_a_1315_, v___y_1316_, v___y_1317_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
lean_dec(v_a_1315_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_1320_, lean_object* v_post_1321_, lean_object* v_sz_1322_, lean_object* v_i_1323_, lean_object* v_bs_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_){
_start:
{
size_t v_sz_boxed_1329_; size_t v_i_boxed_1330_; lean_object* v_res_1331_; 
v_sz_boxed_1329_ = lean_unbox_usize(v_sz_1322_);
lean_dec(v_sz_1322_);
v_i_boxed_1330_ = lean_unbox_usize(v_i_1323_);
lean_dec(v_i_1323_);
v_res_1331_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1(v_pre_1320_, v_post_1321_, v_sz_boxed_1329_, v_i_boxed_1330_, v_bs_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
lean_dec(v___y_1325_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_1332_, lean_object* v_post_1333_, lean_object* v_x_1334_, lean_object* v_x_1335_, lean_object* v_x_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4(v_pre_1332_, v_post_1333_, v_x_1334_, v_x_1335_, v_x_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec(v___y_1337_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___boxed(lean_object* v_pre_1342_, lean_object* v_post_1343_, lean_object* v_e_1344_, lean_object* v_a_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
lean_object* v_res_1349_; 
v_res_1349_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1342_, v_post_1343_, v_e_1344_, v_a_1345_, v___y_1346_, v___y_1347_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec(v_a_1345_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(lean_object* v_00_u03b1_1350_, lean_object* v_x_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_){
_start:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1355_ = lean_apply_1(v_x_1351_, lean_box(0));
v___x_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1355_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1357_, lean_object* v_x_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_){
_start:
{
lean_object* v_res_1362_; 
v_res_1362_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(v_00_u03b1_1357_, v_x_1358_, v___y_1359_, v___y_1360_);
lean_dec(v___y_1360_);
lean_dec_ref(v___y_1359_);
return v_res_1362_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1363_ = lean_box(0);
v___x_1364_ = lean_unsigned_to_nat(16u);
v___x_1365_ = lean_mk_array(v___x_1364_, v___x_1363_);
return v___x_1365_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1366_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0, &l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0);
v___x_1367_ = lean_unsigned_to_nat(0u);
v___x_1368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1367_);
lean_ctor_set(v___x_1368_, 1, v___x_1366_);
return v___x_1368_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1369_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1, &l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1_once, _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1);
v___x_1370_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1370_, 0, lean_box(0));
lean_closure_set(v___x_1370_, 1, lean_box(0));
lean_closure_set(v___x_1370_, 2, v___x_1369_);
return v___x_1370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0(lean_object* v_input_1371_, lean_object* v_pre_1372_, lean_object* v_post_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_){
_start:
{
lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v_a_1379_; lean_object* v___x_1380_; 
v___x_1377_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2);
v___x_1378_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(lean_box(0), v___x_1377_, v___y_1374_, v___y_1375_);
v_a_1379_ = lean_ctor_get(v___x_1378_, 0);
lean_inc(v_a_1379_);
lean_dec_ref(v___x_1378_);
v___x_1380_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1372_, v_post_1373_, v_input_1371_, v_a_1379_, v___y_1374_, v___y_1375_);
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_object* v_a_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1390_; 
v_a_1381_ = lean_ctor_get(v___x_1380_, 0);
lean_inc(v_a_1381_);
lean_dec_ref_known(v___x_1380_, 1);
v___x_1382_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1382_, 0, lean_box(0));
lean_closure_set(v___x_1382_, 1, lean_box(0));
lean_closure_set(v___x_1382_, 2, v_a_1379_);
v___x_1383_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(lean_box(0), v___x_1382_, v___y_1374_, v___y_1375_);
v_isSharedCheck_1390_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1390_ == 0)
{
lean_object* v_unused_1391_; 
v_unused_1391_ = lean_ctor_get(v___x_1383_, 0);
lean_dec(v_unused_1391_);
v___x_1385_ = v___x_1383_;
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
else
{
lean_dec(v___x_1383_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1388_; 
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 0, v_a_1381_);
v___x_1388_ = v___x_1385_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_a_1381_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
}
else
{
lean_dec(v_a_1379_);
return v___x_1380_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___boxed(lean_object* v_input_1392_, lean_object* v_pre_1393_, lean_object* v_post_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
lean_object* v_res_1398_; 
v_res_1398_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0(v_input_1392_, v_pre_1393_, v_post_1394_, v___y_1395_, v___y_1396_);
lean_dec(v___y_1396_);
lean_dec_ref(v___y_1395_);
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(lean_object* v_e_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_){
_start:
{
lean_object* v___f_1405_; lean_object* v___f_1406_; lean_object* v___x_1407_; 
v___f_1405_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___closed__0));
v___f_1406_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___closed__1));
v___x_1407_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0(v_e_1401_, v___f_1405_, v___f_1406_, v_a_1402_, v_a_1403_);
return v___x_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___boxed(lean_object* v_e_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(v_e_1408_, v_a_1409_, v_a_1410_);
lean_dec(v_a_1410_);
lean_dec_ref(v_a_1409_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1413_, lean_object* v_m_1414_, lean_object* v_a_1415_){
_start:
{
lean_object* v___x_1416_; 
v___x_1416_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg(v_m_1414_, v_a_1415_);
return v___x_1416_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1417_, lean_object* v_m_1418_, lean_object* v_a_1419_){
_start:
{
lean_object* v_res_1420_; 
v_res_1420_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3(v_00_u03b2_1417_, v_m_1418_, v_a_1419_);
lean_dec_ref(v_a_1419_);
lean_dec_ref(v_m_1418_);
return v_res_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_1421_, lean_object* v_ref_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
lean_object* v___x_1426_; 
v___x_1426_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1422_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1427_, lean_object* v_ref_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_1427_, v_ref_1428_, v___y_1429_, v___y_1430_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8(lean_object* v_00_u03b1_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
lean_object* v___x_1437_; 
v___x_1437_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg();
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8(v_00_u03b1_1438_, v___y_1439_, v___y_1440_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_1443_, lean_object* v_x_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
lean_object* v___x_1449_; 
v___x_1449_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg(v_x_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_1450_, lean_object* v_x_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
lean_object* v_res_1456_; 
v_res_1456_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5(v_00_u03b1_1450_, v_x_1451_, v___y_1452_, v___y_1453_, v___y_1454_);
lean_dec(v___y_1454_);
lean_dec_ref(v___y_1453_);
lean_dec(v___y_1452_);
return v_res_1456_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_1457_, lean_object* v_m_1458_, lean_object* v_a_1459_, lean_object* v_b_1460_){
_start:
{
lean_object* v___x_1461_; 
v___x_1461_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6___redArg(v_m_1458_, v_a_1459_, v_b_1460_);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_1462_, lean_object* v_a_1463_, lean_object* v_x_1464_){
_start:
{
lean_object* v___x_1465_; 
v___x_1465_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1463_, v_x_1464_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1466_, lean_object* v_a_1467_, lean_object* v_x_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_1466_, v_a_1467_, v_x_1468_);
lean_dec(v_x_1468_);
lean_dec_ref(v_a_1467_);
return v_res_1469_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_1470_, lean_object* v_a_1471_, lean_object* v_x_1472_){
_start:
{
uint8_t v___x_1473_; 
v___x_1473_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1471_, v_x_1472_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___boxed(lean_object* v_00_u03b2_1474_, lean_object* v_a_1475_, lean_object* v_x_1476_){
_start:
{
uint8_t v_res_1477_; lean_object* v_r_1478_; 
v_res_1477_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10(v_00_u03b2_1474_, v_a_1475_, v_x_1476_);
lean_dec(v_x_1476_);
lean_dec_ref(v_a_1475_);
v_r_1478_ = lean_box(v_res_1477_);
return v_r_1478_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_1479_, lean_object* v_data_1480_){
_start:
{
lean_object* v___x_1481_; 
v___x_1481_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11___redArg(v_data_1480_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12(lean_object* v_00_u03b2_1482_, lean_object* v_a_1483_, lean_object* v_b_1484_, lean_object* v_x_1485_){
_start:
{
lean_object* v___x_1486_; 
v___x_1486_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1483_, v_b_1484_, v_x_1485_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12(lean_object* v_00_u03b2_1487_, lean_object* v_i_1488_, lean_object* v_source_1489_, lean_object* v_target_1490_){
_start:
{
lean_object* v___x_1491_; 
v___x_1491_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v_i_1488_, v_source_1489_, v_target_1490_);
return v___x_1491_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_1492_, lean_object* v_x_1493_, lean_object* v_x_1494_){
_start:
{
lean_object* v___x_1495_; 
v___x_1495_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_x_1493_, v_x_1494_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(lean_object* v_declName_1496_, lean_object* v___y_1497_){
_start:
{
lean_object* v___x_1499_; lean_object* v_env_1500_; uint8_t v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1499_ = lean_st_ref_get(v___y_1497_);
v_env_1500_ = lean_ctor_get(v___x_1499_, 0);
lean_inc_ref(v_env_1500_);
lean_dec(v___x_1499_);
v___x_1501_ = l_Lean_isRecCore(v_env_1500_, v_declName_1496_);
v___x_1502_ = lean_box(v___x_1501_);
v___x_1503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1503_, 0, v___x_1502_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg___boxed(lean_object* v_declName_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_){
_start:
{
lean_object* v_res_1507_; 
v_res_1507_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(v_declName_1504_, v___y_1505_);
lean_dec(v___y_1505_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2(lean_object* v_declName_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_){
_start:
{
lean_object* v___x_1514_; 
v___x_1514_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(v_declName_1508_, v___y_1512_);
return v___x_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___boxed(lean_object* v_declName_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2(v_declName_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(lean_object* v_declName_1522_, lean_object* v___y_1523_){
_start:
{
lean_object* v___x_1525_; lean_object* v_env_1526_; uint8_t v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1525_ = lean_st_ref_get(v___y_1523_);
v_env_1526_ = lean_ctor_get(v___x_1525_, 0);
lean_inc_ref(v_env_1526_);
lean_dec(v___x_1525_);
v___x_1527_ = l_Lean_getReducibilityStatusCore(v_env_1526_, v_declName_1522_);
v___x_1528_ = lean_box(v___x_1527_);
v___x_1529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1528_);
return v___x_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg___boxed(lean_object* v_declName_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(v_declName_1530_, v___y_1531_);
lean_dec(v___y_1531_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0(lean_object* v_declName_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
lean_object* v___x_1540_; lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1556_; 
v___x_1540_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(v_declName_1534_, v___y_1538_);
v_a_1541_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1543_ = v___x_1540_;
v_isShared_1544_ = v_isSharedCheck_1556_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_dec(v___x_1540_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1556_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
uint8_t v___x_1545_; 
v___x_1545_ = lean_unbox(v_a_1541_);
lean_dec(v_a_1541_);
if (v___x_1545_ == 0)
{
uint8_t v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1549_; 
v___x_1546_ = 1;
v___x_1547_ = lean_box(v___x_1546_);
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 0, v___x_1547_);
v___x_1549_ = v___x_1543_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v___x_1547_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
}
}
else
{
uint8_t v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1554_; 
v___x_1551_ = 0;
v___x_1552_ = lean_box(v___x_1551_);
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 0, v___x_1552_);
v___x_1554_ = v___x_1543_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v___x_1552_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0___boxed(lean_object* v_declName_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_){
_start:
{
lean_object* v_res_1563_; 
v_res_1563_ = l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0(v_declName_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(lean_object* v_a_1564_, lean_object* v_b_1565_){
_start:
{
lean_object* v_array_1567_; lean_object* v_start_1568_; lean_object* v_stop_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1586_; 
v_array_1567_ = lean_ctor_get(v_a_1564_, 0);
v_start_1568_ = lean_ctor_get(v_a_1564_, 1);
v_stop_1569_ = lean_ctor_get(v_a_1564_, 2);
v_isSharedCheck_1586_ = !lean_is_exclusive(v_a_1564_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1571_ = v_a_1564_;
v_isShared_1572_ = v_isSharedCheck_1586_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_stop_1569_);
lean_inc(v_start_1568_);
lean_inc(v_array_1567_);
lean_dec(v_a_1564_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1586_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
uint8_t v___x_1573_; 
v___x_1573_ = lean_nat_dec_lt(v_start_1568_, v_stop_1569_);
if (v___x_1573_ == 0)
{
lean_object* v___x_1574_; 
lean_del_object(v___x_1571_);
lean_dec(v_stop_1569_);
lean_dec(v_start_1568_);
lean_dec_ref(v_array_1567_);
v___x_1574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1574_, 0, v_b_1565_);
return v___x_1574_;
}
else
{
lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1579_; 
v___x_1575_ = lean_box(0);
v___x_1576_ = lean_unsigned_to_nat(1u);
v___x_1577_ = lean_nat_add(v_start_1568_, v___x_1576_);
lean_inc_ref(v_array_1567_);
if (v_isShared_1572_ == 0)
{
lean_ctor_set(v___x_1571_, 1, v___x_1577_);
v___x_1579_ = v___x_1571_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_array_1567_);
lean_ctor_set(v_reuseFailAlloc_1585_, 1, v___x_1577_);
lean_ctor_set(v_reuseFailAlloc_1585_, 2, v_stop_1569_);
v___x_1579_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
lean_object* v___x_1580_; uint8_t v___x_1581_; 
v___x_1580_ = lean_array_fget(v_array_1567_, v_start_1568_);
lean_dec(v_start_1568_);
lean_dec_ref(v_array_1567_);
v___x_1581_ = l_Lean_Expr_hasExprMVar(v___x_1580_);
lean_dec(v___x_1580_);
if (v___x_1581_ == 0)
{
v_a_1564_ = v___x_1579_;
v_b_1565_ = v___x_1575_;
goto _start;
}
else
{
lean_object* v___x_1583_; 
v___x_1583_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_dec_ref_known(v___x_1583_, 1);
v_a_1564_ = v___x_1579_;
v_b_1565_ = v___x_1575_;
goto _start;
}
else
{
lean_dec_ref(v___x_1579_);
return v___x_1583_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg___boxed(lean_object* v_a_1587_, lean_object* v_b_1588_, lean_object* v___y_1589_){
_start:
{
lean_object* v_res_1590_; 
v_res_1590_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(v_a_1587_, v_b_1588_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(lean_object* v_e_1599_, uint8_t v_isMatch_1600_, uint8_t v_root_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_){
_start:
{
lean_object* v___y_1608_; lean_object* v_b_1609_; lean_object* v___x_1620_; 
v___x_1620_ = l_Lean_Meta_DiscrTree_reduceDT(v_e_1599_, v_root_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v_a_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1783_; 
v_a_1621_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1623_ = v___x_1620_;
v_isShared_1624_ = v_isSharedCheck_1783_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_a_1621_);
lean_dec(v___x_1620_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1783_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___y_1626_; lean_object* v___y_1636_; lean_object* v___y_1637_; lean_object* v___y_1638_; lean_object* v___y_1639_; 
if (v_root_1601_ == 0)
{
lean_object* v___x_1771_; 
lean_inc(v_a_1621_);
v___x_1771_ = l_Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f(v_a_1621_);
if (lean_obj_tag(v___x_1771_) == 1)
{
lean_object* v_val_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1782_; 
lean_del_object(v___x_1623_);
lean_dec(v_a_1621_);
v_val_1772_ = lean_ctor_get(v___x_1771_, 0);
v_isSharedCheck_1782_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1774_ = v___x_1771_;
v_isShared_1775_ = v_isSharedCheck_1782_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_val_1772_);
lean_dec(v___x_1771_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1782_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1777_; 
if (v_isShared_1775_ == 0)
{
lean_ctor_set_tag(v___x_1774_, 2);
v___x_1777_ = v___x_1774_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v_val_1772_);
v___x_1777_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; 
v___x_1778_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
v___x_1779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1779_, 0, v___x_1777_);
lean_ctor_set(v___x_1779_, 1, v___x_1778_);
v___x_1780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1780_, 0, v___x_1779_);
return v___x_1780_;
}
}
}
else
{
lean_dec(v___x_1771_);
v___y_1636_ = v_a_1602_;
v___y_1637_ = v_a_1603_;
v___y_1638_ = v_a_1604_;
v___y_1639_ = v_a_1605_;
goto v___jp_1635_;
}
}
else
{
v___y_1636_ = v_a_1602_;
v___y_1637_ = v_a_1603_;
v___y_1638_ = v_a_1604_;
v___y_1639_ = v_a_1605_;
goto v___jp_1635_;
}
v___jp_1625_:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1633_; 
v___x_1627_ = l_Lean_Expr_getAppNumArgs(v_a_1621_);
lean_inc(v___x_1627_);
v___x_1628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1628_, 0, v___y_1626_);
lean_ctor_set(v___x_1628_, 1, v___x_1627_);
v___x_1629_ = lean_mk_empty_array_with_capacity(v___x_1627_);
lean_dec(v___x_1627_);
v___x_1630_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1621_, v___x_1629_);
v___x_1631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1628_);
lean_ctor_set(v___x_1631_, 1, v___x_1630_);
if (v_isShared_1624_ == 0)
{
lean_ctor_set(v___x_1623_, 0, v___x_1631_);
v___x_1633_ = v___x_1623_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v___x_1631_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
v___jp_1635_:
{
lean_object* v___x_1640_; 
v___x_1640_ = l_Lean_Expr_getAppFn(v_a_1621_);
switch(lean_obj_tag(v___x_1640_))
{
case 1:
{
lean_object* v_fvarId_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; 
lean_del_object(v___x_1623_);
v_fvarId_1641_ = lean_ctor_get(v___x_1640_, 0);
lean_inc(v_fvarId_1641_);
lean_dec_ref_known(v___x_1640_, 1);
v___x_1642_ = l_Lean_Expr_getAppNumArgs(v_a_1621_);
lean_inc(v___x_1642_);
v___x_1643_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1643_, 0, v_fvarId_1641_);
lean_ctor_set(v___x_1643_, 1, v___x_1642_);
v___x_1644_ = lean_mk_empty_array_with_capacity(v___x_1642_);
lean_dec(v___x_1642_);
v___x_1645_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1621_, v___x_1644_);
v___x_1646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1643_);
lean_ctor_set(v___x_1646_, 1, v___x_1645_);
v___x_1647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1646_);
return v___x_1647_;
}
case 2:
{
lean_del_object(v___x_1623_);
lean_dec(v_a_1621_);
if (v_isMatch_1600_ == 0)
{
lean_object* v_mvarId_1648_; lean_object* v___x_1649_; uint8_t v_isDefEqStuckEx_1650_; 
v_mvarId_1648_ = lean_ctor_get(v___x_1640_, 0);
lean_inc(v_mvarId_1648_);
lean_dec_ref_known(v___x_1640_, 1);
v___x_1649_ = l_Lean_Meta_Context_config(v___y_1636_);
v_isDefEqStuckEx_1650_ = lean_ctor_get_uint8(v___x_1649_, 4);
lean_dec_ref(v___x_1649_);
if (v_isDefEqStuckEx_1650_ == 0)
{
lean_object* v___x_1651_; 
v___x_1651_ = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(v_mvarId_1648_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_);
if (lean_obj_tag(v___x_1651_) == 0)
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1665_; 
v_a_1652_ = lean_ctor_get(v___x_1651_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1654_ = v___x_1651_;
v_isShared_1655_ = v_isSharedCheck_1665_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1651_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1665_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
uint8_t v___x_1656_; 
v___x_1656_ = lean_unbox(v_a_1652_);
lean_dec(v_a_1652_);
if (v___x_1656_ == 0)
{
lean_object* v___x_1657_; lean_object* v___x_1659_; 
v___x_1657_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__2));
if (v_isShared_1655_ == 0)
{
lean_ctor_set(v___x_1654_, 0, v___x_1657_);
v___x_1659_ = v___x_1654_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v___x_1657_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
else
{
lean_object* v___x_1661_; lean_object* v___x_1663_; 
v___x_1661_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
if (v_isShared_1655_ == 0)
{
lean_ctor_set(v___x_1654_, 0, v___x_1661_);
v___x_1663_ = v___x_1654_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v___x_1661_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
}
else
{
lean_object* v_a_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1673_; 
v_a_1666_ = lean_ctor_get(v___x_1651_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1668_ = v___x_1651_;
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_a_1666_);
lean_dec(v___x_1651_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1671_; 
if (v_isShared_1669_ == 0)
{
v___x_1671_ = v___x_1668_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_a_1666_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
}
else
{
lean_object* v___x_1674_; lean_object* v___x_1675_; 
lean_dec(v_mvarId_1648_);
v___x_1674_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__2));
v___x_1675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1674_);
return v___x_1675_;
}
}
else
{
lean_object* v___x_1676_; lean_object* v___x_1677_; 
lean_dec_ref_known(v___x_1640_, 1);
v___x_1676_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
v___x_1677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1676_);
return v___x_1677_;
}
}
case 4:
{
lean_object* v_declName_1678_; lean_object* v___x_1679_; uint8_t v_isDefEqStuckEx_1680_; 
v_declName_1678_ = lean_ctor_get(v___x_1640_, 0);
lean_inc(v_declName_1678_);
lean_dec_ref_known(v___x_1640_, 2);
v___x_1679_ = l_Lean_Meta_Context_config(v___y_1636_);
v_isDefEqStuckEx_1680_ = lean_ctor_get_uint8(v___x_1679_, 4);
lean_dec_ref(v___x_1679_);
if (v_isDefEqStuckEx_1680_ == 0)
{
v___y_1626_ = v_declName_1678_;
goto v___jp_1625_;
}
else
{
uint8_t v___x_1681_; 
v___x_1681_ = l_Lean_Expr_hasExprMVar(v_a_1621_);
if (v___x_1681_ == 0)
{
v___y_1626_ = v_declName_1678_;
goto v___jp_1625_;
}
else
{
lean_object* v___x_1682_; 
lean_inc(v_declName_1678_);
v___x_1682_ = l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0(v_declName_1678_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_);
if (lean_obj_tag(v___x_1682_) == 0)
{
lean_object* v_a_1683_; uint8_t v___x_1684_; 
v_a_1683_ = lean_ctor_get(v___x_1682_, 0);
lean_inc(v_a_1683_);
lean_dec_ref_known(v___x_1682_, 1);
v___x_1684_ = lean_unbox(v_a_1683_);
lean_dec(v_a_1683_);
if (v___x_1684_ == 0)
{
lean_object* v___x_1685_; lean_object* v_env_1686_; lean_object* v___x_1687_; 
v___x_1685_ = lean_st_ref_get(v___y_1639_);
v_env_1686_ = lean_ctor_get(v___x_1685_, 0);
lean_inc_ref(v_env_1686_);
lean_dec(v___x_1685_);
v___x_1687_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_1686_, v_a_1621_);
if (lean_obj_tag(v___x_1687_) == 1)
{
lean_object* v_val_1688_; lean_object* v_numDiscrs_1689_; lean_object* v_nargs_1690_; lean_object* v_dummy_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
v_val_1688_ = lean_ctor_get(v___x_1687_, 0);
lean_inc(v_val_1688_);
lean_dec_ref_known(v___x_1687_, 1);
v_numDiscrs_1689_ = lean_ctor_get(v_val_1688_, 1);
lean_inc(v_numDiscrs_1689_);
v_nargs_1690_ = l_Lean_Expr_getAppNumArgs(v_a_1621_);
v_dummy_1691_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0);
lean_inc(v_nargs_1690_);
v___x_1692_ = lean_mk_array(v_nargs_1690_, v_dummy_1691_);
v___x_1693_ = lean_unsigned_to_nat(1u);
v___x_1694_ = lean_nat_sub(v_nargs_1690_, v___x_1693_);
lean_dec(v_nargs_1690_);
lean_inc(v_a_1621_);
v___x_1695_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1621_, v___x_1692_, v___x_1694_);
v___x_1696_ = l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(v_val_1688_);
lean_dec(v_val_1688_);
v___x_1697_ = lean_nat_add(v___x_1696_, v_numDiscrs_1689_);
lean_dec(v_numDiscrs_1689_);
v___x_1698_ = l_Array_toSubarray___redArg(v___x_1695_, v___x_1696_, v___x_1697_);
v___x_1699_ = lean_box(0);
v___x_1700_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(v___x_1698_, v___x_1699_);
if (lean_obj_tag(v___x_1700_) == 0)
{
lean_dec_ref_known(v___x_1700_, 1);
v___y_1626_ = v_declName_1678_;
goto v___jp_1625_;
}
else
{
lean_object* v_a_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1708_; 
lean_dec(v_declName_1678_);
lean_del_object(v___x_1623_);
lean_dec(v_a_1621_);
v_a_1701_ = lean_ctor_get(v___x_1700_, 0);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1700_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1703_ = v___x_1700_;
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_a_1701_);
lean_dec(v___x_1700_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1706_; 
if (v_isShared_1704_ == 0)
{
v___x_1706_ = v___x_1703_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_a_1701_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
return v___x_1706_;
}
}
}
}
else
{
lean_object* v___x_1709_; lean_object* v_a_1710_; uint8_t v___x_1711_; 
lean_dec(v___x_1687_);
lean_inc(v_declName_1678_);
v___x_1709_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(v_declName_1678_, v___y_1639_);
v_a_1710_ = lean_ctor_get(v___x_1709_, 0);
lean_inc(v_a_1710_);
lean_dec_ref(v___x_1709_);
v___x_1711_ = lean_unbox(v_a_1710_);
lean_dec(v_a_1710_);
if (v___x_1711_ == 0)
{
v___y_1626_ = v_declName_1678_;
goto v___jp_1625_;
}
else
{
lean_object* v___x_1712_; 
v___x_1712_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1712_) == 0)
{
lean_dec_ref_known(v___x_1712_, 1);
v___y_1626_ = v_declName_1678_;
goto v___jp_1625_;
}
else
{
lean_object* v_a_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1720_; 
lean_dec(v_declName_1678_);
lean_del_object(v___x_1623_);
lean_dec(v_a_1621_);
v_a_1713_ = lean_ctor_get(v___x_1712_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1712_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1715_ = v___x_1712_;
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_a_1713_);
lean_dec(v___x_1712_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1718_; 
if (v_isShared_1716_ == 0)
{
v___x_1718_ = v___x_1715_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_a_1713_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
}
}
}
}
else
{
lean_object* v___x_1721_; 
v___x_1721_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1721_) == 0)
{
lean_dec_ref_known(v___x_1721_, 1);
v___y_1626_ = v_declName_1678_;
goto v___jp_1625_;
}
else
{
lean_object* v_a_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1729_; 
lean_dec(v_declName_1678_);
lean_del_object(v___x_1623_);
lean_dec(v_a_1621_);
v_a_1722_ = lean_ctor_get(v___x_1721_, 0);
v_isSharedCheck_1729_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1724_ = v___x_1721_;
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_a_1722_);
lean_dec(v___x_1721_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1727_; 
if (v_isShared_1725_ == 0)
{
v___x_1727_ = v___x_1724_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v_a_1722_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
}
}
}
else
{
lean_object* v_a_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1737_; 
lean_dec(v_declName_1678_);
lean_del_object(v___x_1623_);
lean_dec(v_a_1621_);
v_a_1730_ = lean_ctor_get(v___x_1682_, 0);
v_isSharedCheck_1737_ = !lean_is_exclusive(v___x_1682_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1732_ = v___x_1682_;
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_a_1730_);
lean_dec(v___x_1682_);
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
case 7:
{
lean_object* v_binderType_1738_; lean_object* v_body_1739_; uint8_t v___x_1740_; 
lean_del_object(v___x_1623_);
lean_dec(v_a_1621_);
v_binderType_1738_ = lean_ctor_get(v___x_1640_, 1);
lean_inc_ref(v_binderType_1738_);
v_body_1739_ = lean_ctor_get(v___x_1640_, 2);
lean_inc_ref(v_body_1739_);
lean_dec_ref_known(v___x_1640_, 3);
v___x_1740_ = l_Lean_Expr_hasLooseBVars(v_body_1739_);
if (v___x_1740_ == 0)
{
v___y_1608_ = v_binderType_1738_;
v_b_1609_ = v_body_1739_;
goto v___jp_1607_;
}
else
{
lean_object* v___x_1741_; 
v___x_1741_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(v_body_1739_, v___y_1638_, v___y_1639_);
if (lean_obj_tag(v___x_1741_) == 0)
{
lean_object* v_a_1742_; 
v_a_1742_ = lean_ctor_get(v___x_1741_, 0);
lean_inc(v_a_1742_);
lean_dec_ref_known(v___x_1741_, 1);
v___y_1608_ = v_binderType_1738_;
v_b_1609_ = v_a_1742_;
goto v___jp_1607_;
}
else
{
lean_object* v_a_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1750_; 
lean_dec_ref(v_binderType_1738_);
v_a_1743_ = lean_ctor_get(v___x_1741_, 0);
v_isSharedCheck_1750_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1750_ == 0)
{
v___x_1745_ = v___x_1741_;
v_isShared_1746_ = v_isSharedCheck_1750_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_a_1743_);
lean_dec(v___x_1741_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1750_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1748_; 
if (v_isShared_1746_ == 0)
{
v___x_1748_ = v___x_1745_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v_a_1743_);
v___x_1748_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
return v___x_1748_;
}
}
}
}
}
case 9:
{
lean_object* v_a_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
lean_del_object(v___x_1623_);
lean_dec(v_a_1621_);
v_a_1751_ = lean_ctor_get(v___x_1640_, 0);
lean_inc_ref(v_a_1751_);
lean_dec_ref_known(v___x_1640_, 1);
v___x_1752_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1752_, 0, v_a_1751_);
v___x_1753_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
v___x_1754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1752_);
lean_ctor_set(v___x_1754_, 1, v___x_1753_);
v___x_1755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1755_, 0, v___x_1754_);
return v___x_1755_;
}
case 11:
{
lean_object* v_typeName_1756_; lean_object* v_idx_1757_; lean_object* v_struct_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; 
lean_del_object(v___x_1623_);
v_typeName_1756_ = lean_ctor_get(v___x_1640_, 0);
lean_inc(v_typeName_1756_);
v_idx_1757_ = lean_ctor_get(v___x_1640_, 1);
lean_inc(v_idx_1757_);
v_struct_1758_ = lean_ctor_get(v___x_1640_, 2);
lean_inc_ref(v_struct_1758_);
lean_dec_ref_known(v___x_1640_, 3);
v___x_1759_ = l_Lean_Expr_getAppNumArgs(v_a_1621_);
lean_inc(v___x_1759_);
v___x_1760_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_1760_, 0, v_typeName_1756_);
lean_ctor_set(v___x_1760_, 1, v_idx_1757_);
lean_ctor_set(v___x_1760_, 2, v___x_1759_);
v___x_1761_ = lean_unsigned_to_nat(1u);
v___x_1762_ = lean_mk_empty_array_with_capacity(v___x_1761_);
v___x_1763_ = lean_array_push(v___x_1762_, v_struct_1758_);
v___x_1764_ = lean_mk_empty_array_with_capacity(v___x_1759_);
lean_dec(v___x_1759_);
v___x_1765_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1621_, v___x_1764_);
v___x_1766_ = l_Array_append___redArg(v___x_1763_, v___x_1765_);
lean_dec_ref(v___x_1765_);
v___x_1767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1760_);
lean_ctor_set(v___x_1767_, 1, v___x_1766_);
v___x_1768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1767_);
return v___x_1768_;
}
default: 
{
lean_object* v___x_1769_; lean_object* v___x_1770_; 
lean_dec_ref(v___x_1640_);
lean_del_object(v___x_1623_);
lean_dec(v_a_1621_);
v___x_1769_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
v___x_1770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1769_);
return v___x_1770_;
}
}
}
}
}
else
{
lean_object* v_a_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1791_; 
v_a_1784_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1786_ = v___x_1620_;
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_a_1784_);
lean_dec(v___x_1620_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___x_1789_; 
if (v_isShared_1787_ == 0)
{
v___x_1789_ = v___x_1786_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_a_1784_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
return v___x_1789_;
}
}
}
v___jp_1607_:
{
uint8_t v___x_1610_; 
v___x_1610_ = l_Lean_Expr_hasLooseBVars(v_b_1609_);
if (v___x_1610_ == 0)
{
lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1611_ = lean_box(5);
v___x_1612_ = lean_unsigned_to_nat(2u);
v___x_1613_ = lean_mk_empty_array_with_capacity(v___x_1612_);
v___x_1614_ = lean_array_push(v___x_1613_, v___y_1608_);
v___x_1615_ = lean_array_push(v___x_1614_, v_b_1609_);
v___x_1616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1611_);
lean_ctor_set(v___x_1616_, 1, v___x_1615_);
v___x_1617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1616_);
return v___x_1617_;
}
else
{
lean_object* v___x_1618_; lean_object* v___x_1619_; 
lean_dec_ref(v_b_1609_);
lean_dec_ref(v___y_1608_);
v___x_1618_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
v___x_1619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1618_);
return v___x_1619_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___boxed(lean_object* v_e_1792_, lean_object* v_isMatch_1793_, lean_object* v_root_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_){
_start:
{
uint8_t v_isMatch_boxed_1800_; uint8_t v_root_boxed_1801_; lean_object* v_res_1802_; 
v_isMatch_boxed_1800_ = lean_unbox(v_isMatch_1793_);
v_root_boxed_1801_ = lean_unbox(v_root_1794_);
v_res_1802_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_1792_, v_isMatch_boxed_1800_, v_root_boxed_1801_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_);
lean_dec(v_a_1798_);
lean_dec_ref(v_a_1797_);
lean_dec(v_a_1796_);
lean_dec_ref(v_a_1795_);
return v_res_1802_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0(lean_object* v_declName_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_){
_start:
{
lean_object* v___x_1809_; 
v___x_1809_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(v_declName_1803_, v___y_1807_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___boxed(lean_object* v_declName_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_){
_start:
{
lean_object* v_res_1816_; 
v_res_1816_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0(v_declName_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
return v_res_1816_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1(lean_object* v_inst_1817_, lean_object* v_R_1818_, lean_object* v_a_1819_, lean_object* v_b_1820_, lean_object* v_c_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_){
_start:
{
lean_object* v___x_1827_; 
v___x_1827_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(v_a_1819_, v_b_1820_);
return v___x_1827_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___boxed(lean_object* v_inst_1828_, lean_object* v_R_1829_, lean_object* v_a_1830_, lean_object* v_b_1831_, lean_object* v_c_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1(v_inst_1828_, v_R_1829_, v_a_1830_, v_b_1831_, v_c_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getMatchKeyArgs(lean_object* v_e_1839_, uint8_t v_root_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_){
_start:
{
uint8_t v___x_1846_; lean_object* v___x_1847_; 
v___x_1846_ = 1;
v___x_1847_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_1839_, v___x_1846_, v_root_1840_, v_a_1841_, v_a_1842_, v_a_1843_, v_a_1844_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getMatchKeyArgs___boxed(lean_object* v_e_1848_, lean_object* v_root_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_){
_start:
{
uint8_t v_root_boxed_1855_; lean_object* v_res_1856_; 
v_root_boxed_1855_ = lean_unbox(v_root_1849_);
v_res_1856_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getMatchKeyArgs(v_e_1848_, v_root_boxed_1855_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_);
lean_dec(v_a_1853_);
lean_dec_ref(v_a_1852_);
lean_dec(v_a_1851_);
lean_dec_ref(v_a_1850_);
return v_res_1856_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__1(void){
_start:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1859_ = lean_box(0);
v___x_1860_ = lean_unsigned_to_nat(16u);
v___x_1861_ = lean_mk_array(v___x_1860_, v___x_1859_);
return v___x_1861_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2(void){
_start:
{
lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; 
v___x_1862_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__1);
v___x_1863_ = lean_unsigned_to_nat(0u);
v___x_1864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1863_);
lean_ctor_set(v___x_1864_, 1, v___x_1862_);
return v___x_1864_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__4(void){
_start:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1867_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__3));
v___x_1868_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2);
v___x_1869_ = lean_unsigned_to_nat(0u);
v___x_1870_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__0));
v___x_1871_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1870_);
lean_ctor_set(v___x_1871_, 1, v___x_1869_);
lean_ctor_set(v___x_1871_, 2, v___x_1868_);
lean_ctor_set(v___x_1871_, 3, v___x_1867_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg(){
_start:
{
lean_object* v___x_1873_; 
v___x_1873_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__4);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___boxed(lean_object* v___dummy_1874_){
_start:
{
lean_object* v_res_1875_; 
v_res_1875_ = l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg();
return v_res_1875_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0(void){
_start:
{
lean_object* v___x_1876_; 
v___x_1876_ = l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg();
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default(lean_object* v_00_u03b1_1877_){
_start:
{
lean_object* v___x_1878_; 
v___x_1878_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___redArg(){
_start:
{
lean_object* v___x_1880_; 
v___x_1880_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___redArg___boxed(lean_object* v___dummy_1881_){
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___redArg();
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie(lean_object* v_a_1883_){
_start:
{
lean_object* v___x_1884_; 
v___x_1884_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0);
return v___x_1884_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__1(void){
_start:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; 
v___x_1887_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2);
v___x_1888_ = lean_unsigned_to_nat(0u);
v___x_1889_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___x_1890_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1889_);
lean_ctor_set(v___x_1890_, 1, v___x_1888_);
lean_ctor_set(v___x_1890_, 2, v___x_1887_);
lean_ctor_set(v___x_1890_, 3, v___x_1889_);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg(){
_start:
{
lean_object* v___x_1892_; 
v___x_1892_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__1);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___boxed(lean_object* v___dummy_1893_){
_start:
{
lean_object* v_res_1894_; 
v_res_1894_ = l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg();
return v_res_1894_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0(void){
_start:
{
lean_object* v___x_1895_; 
v___x_1895_ = l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg();
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie(lean_object* v_00_u03b1_1896_){
_start:
{
lean_object* v___x_1897_; 
v___x_1897_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0, &l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Trie_pushPending___redArg(lean_object* v_x_1898_, lean_object* v_x_1899_){
_start:
{
lean_object* v_values_1900_; lean_object* v_star_1901_; lean_object* v_children_1902_; lean_object* v_pending_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1911_; 
v_values_1900_ = lean_ctor_get(v_x_1898_, 0);
v_star_1901_ = lean_ctor_get(v_x_1898_, 1);
v_children_1902_ = lean_ctor_get(v_x_1898_, 2);
v_pending_1903_ = lean_ctor_get(v_x_1898_, 3);
v_isSharedCheck_1911_ = !lean_is_exclusive(v_x_1898_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1905_ = v_x_1898_;
v_isShared_1906_ = v_isSharedCheck_1911_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_pending_1903_);
lean_inc(v_children_1902_);
lean_inc(v_star_1901_);
lean_inc(v_values_1900_);
lean_dec(v_x_1898_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1911_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1907_; lean_object* v___x_1909_; 
v___x_1907_ = lean_array_push(v_pending_1903_, v_x_1899_);
if (v_isShared_1906_ == 0)
{
lean_ctor_set(v___x_1905_, 3, v___x_1907_);
v___x_1909_ = v___x_1905_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_values_1900_);
lean_ctor_set(v_reuseFailAlloc_1910_, 1, v_star_1901_);
lean_ctor_set(v_reuseFailAlloc_1910_, 2, v_children_1902_);
lean_ctor_set(v_reuseFailAlloc_1910_, 3, v___x_1907_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Trie_pushPending(lean_object* v_00_u03b1_1912_, lean_object* v_x_1913_, lean_object* v_x_1914_){
_start:
{
lean_object* v___x_1915_; 
v___x_1915_ = l_Lean_Meta_LazyDiscrTree_Trie_pushPending___redArg(v_x_1913_, v_x_1914_);
return v___x_1915_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__0(void){
_start:
{
lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1916_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0);
v___x_1917_ = lean_unsigned_to_nat(1u);
v___x_1918_ = lean_mk_empty_array_with_capacity(v___x_1917_);
v___x_1919_ = lean_array_push(v___x_1918_, v___x_1916_);
return v___x_1919_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__1(void){
_start:
{
lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; 
v___x_1920_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2);
v___x_1921_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__0);
v___x_1922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1921_);
lean_ctor_set(v___x_1922_, 1, v___x_1920_);
return v___x_1922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabited___redArg(){
_start:
{
lean_object* v___x_1924_; 
v___x_1924_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__1);
return v___x_1924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___boxed(lean_object* v___dummy_1925_){
_start:
{
lean_object* v_res_1926_; 
v_res_1926_ = l_Lean_Meta_LazyDiscrTree_instInhabited___redArg();
return v_res_1926_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_1927_; 
v___x_1927_ = l_Lean_Meta_LazyDiscrTree_instInhabited___redArg();
return v___x_1927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabited(lean_object* v_00_u03b1_1928_){
_start:
{
lean_object* v___x_1929_; 
v___x_1929_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0);
return v___x_1929_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(lean_object* v_msgData_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_){
_start:
{
lean_object* v___x_1936_; lean_object* v_env_1937_; lean_object* v___x_1938_; lean_object* v_toCold_1939_; lean_object* v_mctx_1940_; lean_object* v_lctx_1941_; lean_object* v_options_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; 
v___x_1936_ = lean_st_ref_get(v___y_1934_);
v_env_1937_ = lean_ctor_get(v___x_1936_, 0);
lean_inc_ref(v_env_1937_);
lean_dec(v___x_1936_);
v___x_1938_ = lean_st_ref_get(v___y_1932_);
v_toCold_1939_ = lean_ctor_get(v___y_1933_, 0);
v_mctx_1940_ = lean_ctor_get(v___x_1938_, 0);
lean_inc_ref(v_mctx_1940_);
lean_dec(v___x_1938_);
v_lctx_1941_ = lean_ctor_get(v___y_1931_, 2);
v_options_1942_ = lean_ctor_get(v_toCold_1939_, 2);
lean_inc_ref(v_options_1942_);
lean_inc_ref(v_lctx_1941_);
v___x_1943_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1943_, 0, v_env_1937_);
lean_ctor_set(v___x_1943_, 1, v_mctx_1940_);
lean_ctor_set(v___x_1943_, 2, v_lctx_1941_);
lean_ctor_set(v___x_1943_, 3, v_options_1942_);
v___x_1944_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1943_);
lean_ctor_set(v___x_1944_, 1, v_msgData_1930_);
v___x_1945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1944_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0___boxed(lean_object* v_msgData_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_){
_start:
{
lean_object* v_res_1952_; 
v_res_1952_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(v_msgData_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
lean_dec(v___y_1948_);
lean_dec_ref(v___y_1947_);
return v_res_1952_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(lean_object* v_msg_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_){
_start:
{
lean_object* v_ref_1959_; lean_object* v___x_1960_; lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1969_; 
v_ref_1959_ = lean_ctor_get(v___y_1956_, 2);
v___x_1960_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(v_msg_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
v_a_1961_ = lean_ctor_get(v___x_1960_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1963_ = v___x_1960_;
v_isShared_1964_ = v_isSharedCheck_1969_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___x_1960_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1969_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1965_; lean_object* v___x_1967_; 
lean_inc(v_ref_1959_);
v___x_1965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1965_, 0, v_ref_1959_);
lean_ctor_set(v___x_1965_, 1, v_a_1961_);
if (v_isShared_1964_ == 0)
{
lean_ctor_set_tag(v___x_1963_, 1);
lean_ctor_set(v___x_1963_, 0, v___x_1965_);
v___x_1967_ = v___x_1963_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v___x_1965_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg___boxed(lean_object* v_msg_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_){
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(v_msg_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
lean_dec(v___y_1974_);
lean_dec_ref(v___y_1973_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
return v_res_1976_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1(void){
_start:
{
lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1978_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_pushArgs___closed__0));
v___x_1979_ = l_Lean_stringToMessageData(v___x_1978_);
return v___x_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushArgs(uint8_t v_root_1980_, lean_object* v_todo_1981_, lean_object* v_e_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_){
_start:
{
lean_object* v_v_1989_; uint8_t v___x_1993_; 
v___x_1993_ = l_Lean_Meta_DiscrTree_hasNoindexAnnotation(v_e_1982_);
if (v___x_1993_ == 0)
{
lean_object* v___x_1994_; 
v___x_1994_ = l_Lean_Meta_DiscrTree_reduceDT(v_e_1982_, v_root_1980_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_);
if (lean_obj_tag(v___x_1994_) == 0)
{
lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2137_; 
v_a_1995_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_1997_ = v___x_1994_;
v_isShared_1998_ = v_isSharedCheck_2137_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1994_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2137_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_1999_; lean_object* v_k_2001_; lean_object* v_nargs_2002_; lean_object* v_todo_2003_; lean_object* v___y_2004_; lean_object* v___y_2005_; lean_object* v___y_2006_; lean_object* v___y_2007_; 
v___x_1999_ = l_Lean_Expr_getAppFn(v_a_1995_);
switch(lean_obj_tag(v___x_1999_))
{
case 9:
{
lean_object* v_a_2046_; 
lean_del_object(v___x_1997_);
lean_dec(v_a_1995_);
v_a_2046_ = lean_ctor_get(v___x_1999_, 0);
lean_inc_ref(v_a_2046_);
lean_dec_ref_known(v___x_1999_, 1);
v_v_1989_ = v_a_2046_;
goto v___jp_1988_;
}
case 4:
{
lean_object* v_declName_2047_; lean_object* v___y_2049_; lean_object* v___y_2050_; lean_object* v___y_2051_; lean_object* v___y_2052_; 
lean_del_object(v___x_1997_);
v_declName_2047_ = lean_ctor_get(v___x_1999_, 0);
lean_inc(v_declName_2047_);
if (v_root_1980_ == 0)
{
lean_object* v___x_2055_; 
lean_inc(v_a_1995_);
v___x_2055_ = l_Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f(v_a_1995_);
if (lean_obj_tag(v___x_2055_) == 1)
{
lean_object* v_val_2056_; 
lean_dec(v_declName_2047_);
lean_dec_ref_known(v___x_1999_, 2);
lean_dec(v_a_1995_);
v_val_2056_ = lean_ctor_get(v___x_2055_, 0);
lean_inc(v_val_2056_);
lean_dec_ref_known(v___x_2055_, 1);
v_v_1989_ = v_val_2056_;
goto v___jp_1988_;
}
else
{
lean_object* v___x_2057_; 
lean_dec(v___x_2055_);
v___x_2057_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset(v_declName_2047_, v_a_1995_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_);
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
v___y_2049_ = v_a_1983_;
v___y_2050_ = v_a_1984_;
v___y_2051_ = v_a_1985_;
v___y_2052_ = v_a_1986_;
goto v___jp_2048_;
}
else
{
lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2066_; 
lean_dec(v_declName_2047_);
lean_dec_ref_known(v___x_1999_, 2);
lean_dec(v_a_1995_);
v___x_2063_ = lean_box(3);
v___x_2064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2063_);
lean_ctor_set(v___x_2064_, 1, v_todo_1981_);
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
lean_dec(v_declName_2047_);
lean_dec_ref_known(v___x_1999_, 2);
lean_dec(v_a_1995_);
lean_dec_ref(v_todo_1981_);
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
v___y_2049_ = v_a_1983_;
v___y_2050_ = v_a_1984_;
v___y_2051_ = v_a_1985_;
v___y_2052_ = v_a_1986_;
goto v___jp_2048_;
}
v___jp_2048_:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2053_ = l_Lean_Expr_getAppNumArgs(v_a_1995_);
lean_inc(v___x_2053_);
v___x_2054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2054_, 0, v_declName_2047_);
lean_ctor_set(v___x_2054_, 1, v___x_2053_);
v_k_2001_ = v___x_2054_;
v_nargs_2002_ = v___x_2053_;
v_todo_2003_ = v_todo_1981_;
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
lean_del_object(v___x_1997_);
v_typeName_2077_ = lean_ctor_get(v___x_1999_, 0);
lean_inc(v_typeName_2077_);
v_idx_2078_ = lean_ctor_get(v___x_1999_, 1);
lean_inc(v_idx_2078_);
v_struct_2079_ = lean_ctor_get(v___x_1999_, 2);
lean_inc_ref(v_struct_2079_);
v___x_2080_ = lean_st_ref_get(v_a_1986_);
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
v___x_2083_ = l_Lean_Expr_getAppNumArgs(v_a_1995_);
lean_inc(v___x_2083_);
v___x_2084_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_2084_, 0, v_typeName_2077_);
lean_ctor_set(v___x_2084_, 1, v_idx_2078_);
lean_ctor_set(v___x_2084_, 2, v___x_2083_);
v___x_2085_ = lean_array_push(v_todo_1981_, v___y_2082_);
v_k_2001_ = v___x_2084_;
v_nargs_2002_ = v___x_2083_;
v_todo_2003_ = v___x_2085_;
v___y_2004_ = v_a_1983_;
v___y_2005_ = v_a_1984_;
v___y_2006_ = v_a_1985_;
v___y_2007_ = v_a_1986_;
goto v___jp_2000_;
}
}
case 1:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2092_; 
lean_dec_ref_known(v___x_1999_, 1);
lean_dec(v_a_1995_);
v___x_2089_ = lean_box(3);
v___x_2090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2089_);
lean_ctor_set(v___x_2090_, 1, v_todo_1981_);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 0, v___x_2090_);
v___x_2092_ = v___x_1997_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v___x_2090_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
case 2:
{
lean_object* v_mvarId_2094_; lean_object* v___x_2095_; uint8_t v___x_2096_; 
lean_dec(v_a_1995_);
v_mvarId_2094_ = lean_ctor_get(v___x_1999_, 0);
lean_inc(v_mvarId_2094_);
lean_dec_ref_known(v___x_1999_, 1);
v___x_2095_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_tmpMVarId));
v___x_2096_ = l_Lean_instBEqMVarId_beq(v_mvarId_2094_, v___x_2095_);
lean_dec(v_mvarId_2094_);
if (v___x_2096_ == 0)
{
lean_object* v___x_2097_; lean_object* v___x_2098_; 
lean_del_object(v___x_1997_);
lean_dec_ref(v_todo_1981_);
v___x_2097_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1, &l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1);
v___x_2098_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(v___x_2097_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_);
return v___x_2098_;
}
else
{
lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2102_; 
v___x_2099_ = lean_box(3);
v___x_2100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2100_, 0, v___x_2099_);
lean_ctor_set(v___x_2100_, 1, v_todo_1981_);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 0, v___x_2100_);
v___x_2102_ = v___x_1997_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v___x_2100_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
case 7:
{
lean_object* v_binderType_2104_; lean_object* v_body_2105_; lean_object* v_b_2107_; uint8_t v___x_2121_; 
lean_dec(v_a_1995_);
v_binderType_2104_ = lean_ctor_get(v___x_1999_, 1);
lean_inc_ref(v_binderType_2104_);
v_body_2105_ = lean_ctor_get(v___x_1999_, 2);
lean_inc_ref(v_body_2105_);
lean_dec_ref_known(v___x_1999_, 3);
v___x_2121_ = l_Lean_Expr_hasLooseBVars(v_body_2105_);
if (v___x_2121_ == 0)
{
v_b_2107_ = v_body_2105_;
goto v___jp_2106_;
}
else
{
lean_object* v___x_2122_; 
v___x_2122_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(v_body_2105_, v_a_1985_, v_a_1986_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v_a_2123_; 
v_a_2123_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_a_2123_);
lean_dec_ref_known(v___x_2122_, 1);
v_b_2107_ = v_a_2123_;
goto v___jp_2106_;
}
else
{
lean_object* v_a_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2131_; 
lean_dec_ref(v_binderType_2104_);
lean_del_object(v___x_1997_);
lean_dec_ref(v_todo_1981_);
v_a_2124_ = lean_ctor_get(v___x_2122_, 0);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2126_ = v___x_2122_;
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_a_2124_);
lean_dec(v___x_2122_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2129_; 
if (v_isShared_2127_ == 0)
{
v___x_2129_ = v___x_2126_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_a_2124_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
}
}
v___jp_2106_:
{
uint8_t v___x_2108_; 
v___x_2108_ = l_Lean_Expr_hasLooseBVars(v_b_2107_);
if (v___x_2108_ == 0)
{
lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2114_; 
v___x_2109_ = lean_box(5);
v___x_2110_ = lean_array_push(v_todo_1981_, v_binderType_2104_);
v___x_2111_ = lean_array_push(v___x_2110_, v_b_2107_);
v___x_2112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2109_);
lean_ctor_set(v___x_2112_, 1, v___x_2111_);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 0, v___x_2112_);
v___x_2114_ = v___x_1997_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v___x_2112_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
else
{
lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2119_; 
lean_dec_ref(v_b_2107_);
lean_dec_ref(v_binderType_2104_);
v___x_2116_ = lean_box(4);
v___x_2117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2116_);
lean_ctor_set(v___x_2117_, 1, v_todo_1981_);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 0, v___x_2117_);
v___x_2119_ = v___x_1997_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v___x_2117_);
v___x_2119_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
return v___x_2119_;
}
}
}
}
default: 
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2135_; 
lean_dec_ref(v___x_1999_);
lean_dec(v_a_1995_);
v___x_2132_ = lean_box(4);
v___x_2133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2132_);
lean_ctor_set(v___x_2133_, 1, v_todo_1981_);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 0, v___x_2133_);
v___x_2135_ = v___x_1997_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v___x_2133_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
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
v___x_2016_ = l_Lean_Meta_LazyDiscrTree_MatchClone_pushArgsAux(v_paramInfo_2010_, v___x_2015_, v_a_1995_, v_todo_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_);
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
lean_dec(v_a_1995_);
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
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2145_; 
lean_dec_ref(v_todo_1981_);
v_a_2138_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2140_ = v___x_1994_;
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_1994_);
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
else
{
lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
lean_dec_ref(v_e_1982_);
v___x_2146_ = lean_box(3);
v___x_2147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2146_);
lean_ctor_set(v___x_2147_, 1, v_todo_1981_);
v___x_2148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2148_, 0, v___x_2147_);
return v___x_2148_;
}
v___jp_1988_:
{
lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; 
v___x_1990_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1990_, 0, v_v_1989_);
v___x_1991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1990_);
lean_ctor_set(v___x_1991_, 1, v_todo_1981_);
v___x_1992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1992_, 0, v___x_1991_);
return v___x_1992_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushArgs___boxed(lean_object* v_root_2149_, lean_object* v_todo_2150_, lean_object* v_e_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_){
_start:
{
uint8_t v_root_boxed_2157_; lean_object* v_res_2158_; 
v_root_boxed_2157_ = lean_unbox(v_root_2149_);
v_res_2158_ = l_Lean_Meta_LazyDiscrTree_pushArgs(v_root_boxed_2157_, v_todo_2150_, v_e_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_);
lean_dec(v_a_2155_);
lean_dec_ref(v_a_2154_);
lean_dec(v_a_2153_);
lean_dec_ref(v_a_2152_);
return v_res_2158_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0(lean_object* v_00_u03b1_2159_, lean_object* v_msg_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_){
_start:
{
lean_object* v___x_2166_; 
v___x_2166_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(v_msg_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
return v___x_2166_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___boxed(lean_object* v_00_u03b1_2167_, lean_object* v_msg_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_){
_start:
{
lean_object* v_res_2174_; 
v_res_2174_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0(v_00_u03b1_2167_, v_msg_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_);
lean_dec(v___y_2172_);
lean_dec_ref(v___y_2171_);
lean_dec(v___y_2170_);
lean_dec_ref(v___y_2169_);
return v_res_2174_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_initCapacity(void){
_start:
{
lean_object* v___x_2175_; 
v___x_2175_ = lean_unsigned_to_nat(8u);
return v___x_2175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_rootKey(lean_object* v_e_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_){
_start:
{
uint8_t v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___x_2182_ = 1;
v___x_2183_ = lean_unsigned_to_nat(8u);
v___x_2184_ = lean_mk_empty_array_with_capacity(v___x_2183_);
v___x_2185_ = l_Lean_Meta_LazyDiscrTree_pushArgs(v___x_2182_, v___x_2184_, v_e_2176_, v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_);
return v___x_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_rootKey___boxed(lean_object* v_e_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_){
_start:
{
lean_object* v_res_2192_; 
v_res_2192_ = l_Lean_Meta_LazyDiscrTree_rootKey(v_e_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_);
lean_dec(v_a_2190_);
lean_dec_ref(v_a_2189_);
lean_dec(v_a_2188_);
lean_dec_ref(v_a_2187_);
return v_res_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_buildPath(lean_object* v_op_2193_, uint8_t v_root_2194_, lean_object* v_todo_2195_, lean_object* v_keys_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_){
_start:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; uint8_t v___x_2204_; 
v___x_2202_ = lean_array_get_size(v_todo_2195_);
v___x_2203_ = lean_unsigned_to_nat(0u);
v___x_2204_ = lean_nat_dec_eq(v___x_2202_, v___x_2203_);
if (v___x_2204_ == 0)
{
lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v_e_2208_; lean_object* v_todo_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
v___x_2205_ = l_Lean_instInhabitedExpr;
v___x_2206_ = lean_unsigned_to_nat(1u);
v___x_2207_ = lean_nat_sub(v___x_2202_, v___x_2206_);
v_e_2208_ = lean_array_get(v___x_2205_, v_todo_2195_, v___x_2207_);
lean_dec(v___x_2207_);
v_todo_2209_ = lean_array_pop(v_todo_2195_);
v___x_2210_ = lean_box(v_root_2194_);
lean_inc_ref(v_op_2193_);
lean_inc(v_a_2200_);
lean_inc_ref(v_a_2199_);
lean_inc(v_a_2198_);
lean_inc_ref(v_a_2197_);
v___x_2211_ = lean_apply_8(v_op_2193_, v___x_2210_, v_todo_2209_, v_e_2208_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, lean_box(0));
if (lean_obj_tag(v___x_2211_) == 0)
{
lean_object* v_a_2212_; lean_object* v_fst_2213_; lean_object* v_snd_2214_; lean_object* v___x_2215_; 
v_a_2212_ = lean_ctor_get(v___x_2211_, 0);
lean_inc(v_a_2212_);
lean_dec_ref_known(v___x_2211_, 1);
v_fst_2213_ = lean_ctor_get(v_a_2212_, 0);
lean_inc(v_fst_2213_);
v_snd_2214_ = lean_ctor_get(v_a_2212_, 1);
lean_inc(v_snd_2214_);
lean_dec(v_a_2212_);
v___x_2215_ = lean_array_push(v_keys_2196_, v_fst_2213_);
v_root_2194_ = v___x_2204_;
v_todo_2195_ = v_snd_2214_;
v_keys_2196_ = v___x_2215_;
goto _start;
}
else
{
lean_object* v_a_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2224_; 
lean_dec_ref(v_keys_2196_);
lean_dec_ref(v_op_2193_);
v_a_2217_ = lean_ctor_get(v___x_2211_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2211_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2219_ = v___x_2211_;
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_a_2217_);
lean_dec(v___x_2211_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v___x_2222_; 
if (v_isShared_2220_ == 0)
{
v___x_2222_ = v___x_2219_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_a_2217_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
}
}
else
{
lean_object* v___x_2225_; 
lean_dec_ref(v_todo_2195_);
lean_dec_ref(v_op_2193_);
v___x_2225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2225_, 0, v_keys_2196_);
return v___x_2225_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_buildPath___boxed(lean_object* v_op_2226_, lean_object* v_root_2227_, lean_object* v_todo_2228_, lean_object* v_keys_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_){
_start:
{
uint8_t v_root_boxed_2235_; lean_object* v_res_2236_; 
v_root_boxed_2235_ = lean_unbox(v_root_2227_);
v_res_2236_ = l_Lean_Meta_LazyDiscrTree_buildPath(v_op_2226_, v_root_boxed_2235_, v_todo_2228_, v_keys_2229_, v_a_2230_, v_a_2231_, v_a_2232_, v_a_2233_);
lean_dec(v_a_2233_);
lean_dec_ref(v_a_2232_);
lean_dec(v_a_2231_);
lean_dec_ref(v_a_2230_);
return v_res_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_patternPath(lean_object* v_e_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_){
_start:
{
lean_object* v_op_2244_; lean_object* v___x_2245_; lean_object* v_todo_2246_; uint8_t v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; 
v_op_2244_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_patternPath___closed__0));
v___x_2245_ = lean_unsigned_to_nat(8u);
v_todo_2246_ = lean_mk_empty_array_with_capacity(v___x_2245_);
v___x_2247_ = 1;
lean_inc_ref(v_todo_2246_);
v___x_2248_ = lean_array_push(v_todo_2246_, v_e_2238_);
v___x_2249_ = l_Lean_Meta_LazyDiscrTree_buildPath(v_op_2244_, v___x_2247_, v___x_2248_, v_todo_2246_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_);
return v___x_2249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_patternPath___boxed(lean_object* v_e_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_){
_start:
{
lean_object* v_res_2256_; 
v_res_2256_ = l_Lean_Meta_LazyDiscrTree_patternPath(v_e_2250_, v_a_2251_, v_a_2252_, v_a_2253_, v_a_2254_);
lean_dec(v_a_2254_);
lean_dec_ref(v_a_2253_);
lean_dec(v_a_2252_);
lean_dec_ref(v_a_2251_);
return v_res_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath___lam__0(uint8_t v_root_2257_, lean_object* v_todo_2258_, lean_object* v_e_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_){
_start:
{
uint8_t v___x_2265_; lean_object* v___x_2266_; 
v___x_2265_ = 1;
v___x_2266_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_2259_, v___x_2265_, v_root_2257_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_);
if (lean_obj_tag(v___x_2266_) == 0)
{
lean_object* v_a_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2284_; 
v_a_2267_ = lean_ctor_get(v___x_2266_, 0);
v_isSharedCheck_2284_ = !lean_is_exclusive(v___x_2266_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2269_ = v___x_2266_;
v_isShared_2270_ = v_isSharedCheck_2284_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_a_2267_);
lean_dec(v___x_2266_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2284_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
lean_object* v_fst_2271_; lean_object* v_snd_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2283_; 
v_fst_2271_ = lean_ctor_get(v_a_2267_, 0);
v_snd_2272_ = lean_ctor_get(v_a_2267_, 1);
v_isSharedCheck_2283_ = !lean_is_exclusive(v_a_2267_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2274_ = v_a_2267_;
v_isShared_2275_ = v_isSharedCheck_2283_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_snd_2272_);
lean_inc(v_fst_2271_);
lean_dec(v_a_2267_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2283_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2276_; lean_object* v___x_2278_; 
v___x_2276_ = l_Array_append___redArg(v_todo_2258_, v_snd_2272_);
lean_dec(v_snd_2272_);
if (v_isShared_2275_ == 0)
{
lean_ctor_set(v___x_2274_, 1, v___x_2276_);
v___x_2278_ = v___x_2274_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_fst_2271_);
lean_ctor_set(v_reuseFailAlloc_2282_, 1, v___x_2276_);
v___x_2278_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
lean_object* v___x_2280_; 
if (v_isShared_2270_ == 0)
{
lean_ctor_set(v___x_2269_, 0, v___x_2278_);
v___x_2280_ = v___x_2269_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v___x_2278_);
v___x_2280_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
return v___x_2280_;
}
}
}
}
}
else
{
lean_dec_ref(v_todo_2258_);
return v___x_2266_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath___lam__0___boxed(lean_object* v_root_2285_, lean_object* v_todo_2286_, lean_object* v_e_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_){
_start:
{
uint8_t v_root_boxed_2293_; lean_object* v_res_2294_; 
v_root_boxed_2293_ = lean_unbox(v_root_2285_);
v_res_2294_ = l_Lean_Meta_LazyDiscrTree_targetPath___lam__0(v_root_boxed_2293_, v_todo_2286_, v_e_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_);
lean_dec(v___y_2291_);
lean_dec_ref(v___y_2290_);
lean_dec(v___y_2289_);
lean_dec_ref(v___y_2288_);
return v_res_2294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath(lean_object* v_e_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_){
_start:
{
lean_object* v_op_2302_; lean_object* v___x_2303_; lean_object* v_todo_2304_; uint8_t v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; 
v_op_2302_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_targetPath___closed__0));
v___x_2303_ = lean_unsigned_to_nat(8u);
v_todo_2304_ = lean_mk_empty_array_with_capacity(v___x_2303_);
v___x_2305_ = 1;
lean_inc_ref(v_todo_2304_);
v___x_2306_ = lean_array_push(v_todo_2304_, v_e_2296_);
v___x_2307_ = l_Lean_Meta_LazyDiscrTree_buildPath(v_op_2302_, v___x_2305_, v___x_2306_, v_todo_2304_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
return v___x_2307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath___boxed(lean_object* v_e_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_){
_start:
{
lean_object* v_res_2314_; 
v_res_2314_ = l_Lean_Meta_LazyDiscrTree_targetPath(v_e_2308_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_);
lean_dec(v_a_2312_);
lean_dec_ref(v_a_2311_);
lean_dec(v_a_2310_);
lean_dec_ref(v_a_2309_);
return v_res_2314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___redArg___lam__0(lean_object* v_tries_2315_, lean_object* v_m_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_){
_start:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; 
v___x_2322_ = lean_st_mk_ref(v_tries_2315_);
lean_inc(v___x_2322_);
v___x_2323_ = lean_apply_6(v_m_2316_, v___x_2322_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, lean_box(0));
if (lean_obj_tag(v___x_2323_) == 0)
{
lean_object* v_a_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2333_; 
v_a_2324_ = lean_ctor_get(v___x_2323_, 0);
v_isSharedCheck_2333_ = !lean_is_exclusive(v___x_2323_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2326_ = v___x_2323_;
v_isShared_2327_ = v_isSharedCheck_2333_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_a_2324_);
lean_dec(v___x_2323_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2333_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2331_; 
v___x_2328_ = lean_st_ref_get(v___x_2322_);
lean_dec(v___x_2322_);
v___x_2329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2329_, 0, v_a_2324_);
lean_ctor_set(v___x_2329_, 1, v___x_2328_);
if (v_isShared_2327_ == 0)
{
lean_ctor_set(v___x_2326_, 0, v___x_2329_);
v___x_2331_ = v___x_2326_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v___x_2329_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
}
else
{
lean_object* v_a_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2341_; 
lean_dec(v___x_2322_);
v_a_2334_ = lean_ctor_get(v___x_2323_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2323_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2336_ = v___x_2323_;
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_a_2334_);
lean_dec(v___x_2323_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2339_; 
if (v_isShared_2337_ == 0)
{
v___x_2339_ = v___x_2336_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_a_2334_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___redArg___lam__0___boxed(lean_object* v_tries_2342_, lean_object* v_m_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_){
_start:
{
lean_object* v_res_2349_; 
v_res_2349_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg___lam__0(v_tries_2342_, v_m_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_);
return v_res_2349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___redArg(lean_object* v_d_2350_, lean_object* v_m_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_){
_start:
{
lean_object* v_tries_2357_; lean_object* v_roots_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2411_; 
v_tries_2357_ = lean_ctor_get(v_d_2350_, 0);
v_roots_2358_ = lean_ctor_get(v_d_2350_, 1);
v_isSharedCheck_2411_ = !lean_is_exclusive(v_d_2350_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2360_ = v_d_2350_;
v_isShared_2361_ = v_isSharedCheck_2411_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_roots_2358_);
lean_inc(v_tries_2357_);
lean_dec(v_d_2350_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2411_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___y_2363_; lean_object* v___x_2392_; uint8_t v_transparency_2393_; uint8_t v___x_2394_; uint8_t v___x_2395_; 
v___x_2392_ = l_Lean_Meta_Context_config(v_a_2352_);
v_transparency_2393_ = lean_ctor_get_uint8(v___x_2392_, 9);
lean_dec_ref(v___x_2392_);
v___x_2394_ = 2;
v___x_2395_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2393_, v___x_2394_);
if (v___x_2395_ == 0)
{
lean_object* v_keyedConfig_2396_; uint8_t v_trackZetaDelta_2397_; lean_object* v_zetaDeltaSet_2398_; lean_object* v_lctx_2399_; lean_object* v_localInstances_2400_; lean_object* v_defEqCtx_x3f_2401_; lean_object* v_synthPendingDepth_2402_; lean_object* v_customCanUnfoldPredicate_x3f_2403_; uint8_t v_univApprox_2404_; uint8_t v_inTypeClassResolution_2405_; uint8_t v_cacheInferType_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; 
v_keyedConfig_2396_ = lean_ctor_get(v_a_2352_, 0);
v_trackZetaDelta_2397_ = lean_ctor_get_uint8(v_a_2352_, sizeof(void*)*7);
v_zetaDeltaSet_2398_ = lean_ctor_get(v_a_2352_, 1);
v_lctx_2399_ = lean_ctor_get(v_a_2352_, 2);
v_localInstances_2400_ = lean_ctor_get(v_a_2352_, 3);
v_defEqCtx_x3f_2401_ = lean_ctor_get(v_a_2352_, 4);
v_synthPendingDepth_2402_ = lean_ctor_get(v_a_2352_, 5);
v_customCanUnfoldPredicate_x3f_2403_ = lean_ctor_get(v_a_2352_, 6);
v_univApprox_2404_ = lean_ctor_get_uint8(v_a_2352_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2405_ = lean_ctor_get_uint8(v_a_2352_, sizeof(void*)*7 + 2);
v_cacheInferType_2406_ = lean_ctor_get_uint8(v_a_2352_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2396_);
v___x_2407_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2394_, v_keyedConfig_2396_);
lean_inc(v_customCanUnfoldPredicate_x3f_2403_);
lean_inc(v_synthPendingDepth_2402_);
lean_inc(v_defEqCtx_x3f_2401_);
lean_inc_ref(v_localInstances_2400_);
lean_inc_ref(v_lctx_2399_);
lean_inc(v_zetaDeltaSet_2398_);
v___x_2408_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2408_, 0, v___x_2407_);
lean_ctor_set(v___x_2408_, 1, v_zetaDeltaSet_2398_);
lean_ctor_set(v___x_2408_, 2, v_lctx_2399_);
lean_ctor_set(v___x_2408_, 3, v_localInstances_2400_);
lean_ctor_set(v___x_2408_, 4, v_defEqCtx_x3f_2401_);
lean_ctor_set(v___x_2408_, 5, v_synthPendingDepth_2402_);
lean_ctor_set(v___x_2408_, 6, v_customCanUnfoldPredicate_x3f_2403_);
lean_ctor_set_uint8(v___x_2408_, sizeof(void*)*7, v_trackZetaDelta_2397_);
lean_ctor_set_uint8(v___x_2408_, sizeof(void*)*7 + 1, v_univApprox_2404_);
lean_ctor_set_uint8(v___x_2408_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2405_);
lean_ctor_set_uint8(v___x_2408_, sizeof(void*)*7 + 3, v_cacheInferType_2406_);
lean_inc(v_a_2355_);
lean_inc_ref(v_a_2354_);
lean_inc(v_a_2353_);
v___x_2409_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg___lam__0(v_tries_2357_, v_m_2351_, v___x_2408_, v_a_2353_, v_a_2354_, v_a_2355_);
v___y_2363_ = v___x_2409_;
goto v___jp_2362_;
}
else
{
lean_object* v___x_2410_; 
lean_inc(v_a_2355_);
lean_inc_ref(v_a_2354_);
lean_inc(v_a_2353_);
lean_inc_ref(v_a_2352_);
v___x_2410_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg___lam__0(v_tries_2357_, v_m_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_);
v___y_2363_ = v___x_2410_;
goto v___jp_2362_;
}
v___jp_2362_:
{
if (lean_obj_tag(v___y_2363_) == 0)
{
lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2383_; 
v_a_2364_ = lean_ctor_get(v___y_2363_, 0);
v_isSharedCheck_2383_ = !lean_is_exclusive(v___y_2363_);
if (v_isSharedCheck_2383_ == 0)
{
v___x_2366_ = v___y_2363_;
v_isShared_2367_ = v_isSharedCheck_2383_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v___y_2363_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2383_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v_fst_2368_; lean_object* v_snd_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2382_; 
v_fst_2368_ = lean_ctor_get(v_a_2364_, 0);
v_snd_2369_ = lean_ctor_get(v_a_2364_, 1);
v_isSharedCheck_2382_ = !lean_is_exclusive(v_a_2364_);
if (v_isSharedCheck_2382_ == 0)
{
v___x_2371_ = v_a_2364_;
v_isShared_2372_ = v_isSharedCheck_2382_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_snd_2369_);
lean_inc(v_fst_2368_);
lean_dec(v_a_2364_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2382_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v___x_2374_; 
if (v_isShared_2361_ == 0)
{
lean_ctor_set(v___x_2360_, 0, v_snd_2369_);
v___x_2374_ = v___x_2360_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v_snd_2369_);
lean_ctor_set(v_reuseFailAlloc_2381_, 1, v_roots_2358_);
v___x_2374_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
lean_object* v___x_2376_; 
if (v_isShared_2372_ == 0)
{
lean_ctor_set(v___x_2371_, 1, v___x_2374_);
v___x_2376_ = v___x_2371_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v_fst_2368_);
lean_ctor_set(v_reuseFailAlloc_2380_, 1, v___x_2374_);
v___x_2376_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
lean_object* v___x_2378_; 
if (v_isShared_2367_ == 0)
{
lean_ctor_set(v___x_2366_, 0, v___x_2376_);
v___x_2378_ = v___x_2366_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v___x_2376_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
return v___x_2378_;
}
}
}
}
}
}
else
{
lean_object* v_a_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2391_; 
lean_del_object(v___x_2360_);
lean_dec_ref(v_roots_2358_);
v_a_2384_ = lean_ctor_get(v___y_2363_, 0);
v_isSharedCheck_2391_ = !lean_is_exclusive(v___y_2363_);
if (v_isSharedCheck_2391_ == 0)
{
v___x_2386_ = v___y_2363_;
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_a_2384_);
lean_dec(v___y_2363_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
lean_object* v___x_2389_; 
if (v_isShared_2387_ == 0)
{
v___x_2389_ = v___x_2386_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v_a_2384_);
v___x_2389_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
return v___x_2389_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___redArg___boxed(lean_object* v_d_2412_, lean_object* v_m_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_){
_start:
{
lean_object* v_res_2419_; 
v_res_2419_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_d_2412_, v_m_2413_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_);
lean_dec(v_a_2417_);
lean_dec_ref(v_a_2416_);
lean_dec(v_a_2415_);
lean_dec_ref(v_a_2414_);
return v_res_2419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch(lean_object* v_00_u03b1_2420_, lean_object* v_00_u03b2_2421_, lean_object* v_d_2422_, lean_object* v_m_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_){
_start:
{
lean_object* v___x_2429_; 
v___x_2429_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_d_2422_, v_m_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_);
return v___x_2429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___boxed(lean_object* v_00_u03b1_2430_, lean_object* v_00_u03b2_2431_, lean_object* v_d_2432_, lean_object* v_m_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_){
_start:
{
lean_object* v_res_2439_; 
v_res_2439_ = l_Lean_Meta_LazyDiscrTree_runMatch(v_00_u03b1_2430_, v_00_u03b2_2431_, v_d_2432_, v_m_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_);
lean_dec(v_a_2437_);
lean_dec_ref(v_a_2436_);
lean_dec(v_a_2435_);
lean_dec_ref(v_a_2434_);
return v_res_2439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie___redArg(lean_object* v_i_2440_, lean_object* v_v_2441_, lean_object* v_a_2442_){
_start:
{
lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; 
v___x_2444_ = lean_st_ref_take(v_a_2442_);
v___x_2445_ = lean_box(0);
v___x_2446_ = lean_array_set(v___x_2444_, v_i_2440_, v_v_2441_);
v___x_2447_ = lean_st_ref_put(v_a_2442_, v___x_2446_);
v___x_2448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2445_);
return v___x_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie___redArg___boxed(lean_object* v_i_2449_, lean_object* v_v_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_){
_start:
{
lean_object* v_res_2453_; 
v_res_2453_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_i_2449_, v_v_2450_, v_a_2451_);
lean_dec(v_a_2451_);
lean_dec(v_i_2449_);
return v_res_2453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie(lean_object* v_00_u03b1_2454_, lean_object* v_i_2455_, lean_object* v_v_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_){
_start:
{
lean_object* v___x_2463_; 
v___x_2463_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_i_2455_, v_v_2456_, v_a_2457_);
return v___x_2463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie___boxed(lean_object* v_00_u03b1_2464_, lean_object* v_i_2465_, lean_object* v_v_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_){
_start:
{
lean_object* v_res_2473_; 
v_res_2473_ = l_Lean_Meta_LazyDiscrTree_setTrie(v_00_u03b1_2464_, v_i_2465_, v_v_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_);
lean_dec(v_a_2471_);
lean_dec_ref(v_a_2470_);
lean_dec(v_a_2469_);
lean_dec_ref(v_a_2468_);
lean_dec(v_a_2467_);
lean_dec(v_i_2465_);
return v_res_2473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___redArg___lam__0(lean_object* v_e_2474_, lean_object* v_a_2475_){
_start:
{
lean_object* v_sz_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; 
v_sz_2476_ = lean_array_get_size(v_a_2475_);
v___x_2477_ = lean_unsigned_to_nat(0u);
v___x_2478_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___x_2479_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2);
v___x_2480_ = lean_unsigned_to_nat(1u);
v___x_2481_ = lean_mk_empty_array_with_capacity(v___x_2480_);
v___x_2482_ = lean_array_push(v___x_2481_, v_e_2474_);
v___x_2483_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2478_);
lean_ctor_set(v___x_2483_, 1, v___x_2477_);
lean_ctor_set(v___x_2483_, 2, v___x_2479_);
lean_ctor_set(v___x_2483_, 3, v___x_2482_);
v___x_2484_ = lean_array_push(v_a_2475_, v___x_2483_);
v___x_2485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2485_, 0, v_sz_2476_);
lean_ctor_set(v___x_2485_, 1, v___x_2484_);
return v___x_2485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___redArg(lean_object* v_inst_2486_, lean_object* v_e_2487_){
_start:
{
lean_object* v_modifyGet_2488_; lean_object* v___f_2489_; lean_object* v___x_2490_; 
v_modifyGet_2488_ = lean_ctor_get(v_inst_2486_, 2);
lean_inc(v_modifyGet_2488_);
lean_dec_ref(v_inst_2486_);
v___f_2489_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_newTrie___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2489_, 0, v_e_2487_);
v___x_2490_ = lean_apply_2(v_modifyGet_2488_, lean_box(0), v___f_2489_);
return v___x_2490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie(lean_object* v_m_2491_, lean_object* v_00_u03b1_2492_, lean_object* v_inst_2493_, lean_object* v_inst_2494_, lean_object* v_e_2495_){
_start:
{
lean_object* v___x_2496_; 
v___x_2496_ = l_Lean_Meta_LazyDiscrTree_newTrie___redArg(v_inst_2494_, v_e_2495_);
return v___x_2496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___boxed(lean_object* v_m_2497_, lean_object* v_00_u03b1_2498_, lean_object* v_inst_2499_, lean_object* v_inst_2500_, lean_object* v_e_2501_){
_start:
{
lean_object* v_res_2502_; 
v_res_2502_ = l_Lean_Meta_LazyDiscrTree_newTrie(v_m_2497_, v_00_u03b1_2498_, v_inst_2499_, v_inst_2500_, v_e_2501_);
lean_dec_ref(v_inst_2499_);
return v_res_2502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(lean_object* v_i_2503_, lean_object* v_e_2504_, lean_object* v_a_2505_){
_start:
{
lean_object* v___x_2507_; lean_object* v_fst_2509_; lean_object* v_snd_2510_; lean_object* v___x_2513_; lean_object* v___x_2514_; uint8_t v___x_2515_; 
v___x_2507_ = lean_st_ref_take(v_a_2505_);
v___x_2513_ = lean_box(0);
v___x_2514_ = lean_array_get_size(v___x_2507_);
v___x_2515_ = lean_nat_dec_lt(v_i_2503_, v___x_2514_);
if (v___x_2515_ == 0)
{
lean_dec_ref(v_e_2504_);
v_fst_2509_ = v___x_2513_;
v_snd_2510_ = v___x_2507_;
goto v___jp_2508_;
}
else
{
lean_object* v_v_2516_; lean_object* v_xs_x27_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; 
v_v_2516_ = lean_array_fget(v___x_2507_, v_i_2503_);
v_xs_x27_2517_ = lean_array_fset(v___x_2507_, v_i_2503_, v___x_2513_);
v___x_2518_ = l_Lean_Meta_LazyDiscrTree_Trie_pushPending___redArg(v_v_2516_, v_e_2504_);
v___x_2519_ = lean_array_fset(v_xs_x27_2517_, v_i_2503_, v___x_2518_);
v_fst_2509_ = v___x_2513_;
v_snd_2510_ = v___x_2519_;
goto v___jp_2508_;
}
v___jp_2508_:
{
lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2511_ = lean_st_ref_put(v_a_2505_, v_snd_2510_);
v___x_2512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2512_, 0, v_fst_2509_);
return v___x_2512_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg___boxed(lean_object* v_i_2520_, lean_object* v_e_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_){
_start:
{
lean_object* v_res_2524_; 
v_res_2524_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_i_2520_, v_e_2521_, v_a_2522_);
lean_dec(v_a_2522_);
lean_dec(v_i_2520_);
return v_res_2524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie(lean_object* v_00_u03b1_2525_, lean_object* v_i_2526_, lean_object* v_e_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_){
_start:
{
lean_object* v___x_2534_; 
v___x_2534_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_i_2526_, v_e_2527_, v_a_2528_);
return v___x_2534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___boxed(lean_object* v_00_u03b1_2535_, lean_object* v_i_2536_, lean_object* v_e_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_){
_start:
{
lean_object* v_res_2544_; 
v_res_2544_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie(v_00_u03b1_2535_, v_i_2536_, v_e_2537_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_);
lean_dec(v_a_2542_);
lean_dec_ref(v_a_2541_);
lean_dec(v_a_2540_);
lean_dec_ref(v_a_2539_);
lean_dec(v_a_2538_);
lean_dec(v_i_2536_);
return v_res_2544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0(lean_object* v_x_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_){
_start:
{
lean_object* v___x_2552_; 
lean_inc(v___y_2546_);
v___x_2552_ = lean_apply_6(v_x_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_, lean_box(0));
return v___x_2552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0___boxed(lean_object* v_x_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_){
_start:
{
lean_object* v_res_2560_; 
v_res_2560_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0(v_x_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_);
lean_dec(v___y_2554_);
return v_res_2560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(lean_object* v_lctx_2561_, lean_object* v_localInsts_2562_, lean_object* v_x_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_){
_start:
{
lean_object* v___f_2570_; lean_object* v___x_2571_; 
lean_inc(v___y_2564_);
v___f_2570_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2570_, 0, v_x_2563_);
lean_closure_set(v___f_2570_, 1, v___y_2564_);
v___x_2571_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_2561_, v_localInsts_2562_, v___f_2570_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_);
if (lean_obj_tag(v___x_2571_) == 0)
{
return v___x_2571_;
}
else
{
lean_object* v_a_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2579_; 
v_a_2572_ = lean_ctor_get(v___x_2571_, 0);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2574_ = v___x_2571_;
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_a_2572_);
lean_dec(v___x_2571_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___x_2577_; 
if (v_isShared_2575_ == 0)
{
v___x_2577_ = v___x_2574_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_a_2572_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___boxed(lean_object* v_lctx_2580_, lean_object* v_localInsts_2581_, lean_object* v_x_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_){
_start:
{
lean_object* v_res_2589_; 
v_res_2589_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(v_lctx_2580_, v_localInsts_2581_, v_x_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_);
lean_dec(v___y_2587_);
lean_dec_ref(v___y_2586_);
lean_dec(v___y_2585_);
lean_dec_ref(v___y_2584_);
lean_dec(v___y_2583_);
return v_res_2589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0(lean_object* v_00_u03b1_2590_, lean_object* v_00_u03b1_2591_, lean_object* v_lctx_2592_, lean_object* v_localInsts_2593_, lean_object* v_x_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_){
_start:
{
lean_object* v___x_2601_; 
v___x_2601_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(v_lctx_2592_, v_localInsts_2593_, v_x_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_);
return v___x_2601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___boxed(lean_object* v_00_u03b1_2602_, lean_object* v_00_u03b1_2603_, lean_object* v_lctx_2604_, lean_object* v_localInsts_2605_, lean_object* v_x_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_){
_start:
{
lean_object* v_res_2613_; 
v_res_2613_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0(v_00_u03b1_2602_, v_00_u03b1_2603_, v_lctx_2604_, v_localInsts_2605_, v_x_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec(v___y_2609_);
lean_dec_ref(v___y_2608_);
lean_dec(v___y_2607_);
return v_res_2613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(lean_object* v_e_2614_, lean_object* v___y_2615_){
_start:
{
lean_object* v___x_2617_; lean_object* v_sz_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; 
v___x_2617_ = lean_st_ref_take(v___y_2615_);
v_sz_2618_ = lean_array_get_size(v___x_2617_);
v___x_2619_ = lean_unsigned_to_nat(0u);
v___x_2620_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___x_2621_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2);
v___x_2622_ = lean_unsigned_to_nat(1u);
v___x_2623_ = lean_mk_empty_array_with_capacity(v___x_2622_);
v___x_2624_ = lean_array_push(v___x_2623_, v_e_2614_);
v___x_2625_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2625_, 0, v___x_2620_);
lean_ctor_set(v___x_2625_, 1, v___x_2619_);
lean_ctor_set(v___x_2625_, 2, v___x_2621_);
lean_ctor_set(v___x_2625_, 3, v___x_2624_);
v___x_2626_ = lean_array_push(v___x_2617_, v___x_2625_);
v___x_2627_ = lean_st_ref_put(v___y_2615_, v___x_2626_);
v___x_2628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2628_, 0, v_sz_2618_);
return v___x_2628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg___boxed(lean_object* v_e_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_){
_start:
{
lean_object* v_res_2632_; 
v_res_2632_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v_e_2629_, v___y_2630_);
lean_dec(v___y_2630_);
return v_res_2632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2(lean_object* v_00_u03b1_2633_, lean_object* v_e_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_){
_start:
{
lean_object* v___x_2641_; 
v___x_2641_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v_e_2634_, v___y_2635_);
return v___x_2641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___boxed(lean_object* v_00_u03b1_2642_, lean_object* v_e_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_){
_start:
{
lean_object* v_res_2650_; 
v_res_2650_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2(v_00_u03b1_2642_, v_e_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_);
lean_dec(v___y_2648_);
lean_dec_ref(v___y_2647_);
lean_dec(v___y_2646_);
lean_dec_ref(v___y_2645_);
lean_dec(v___y_2644_);
return v_res_2650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0(uint8_t v___x_2651_, lean_object* v_todo_2652_, lean_object* v_e_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_){
_start:
{
lean_object* v___x_2660_; 
v___x_2660_ = l_Lean_Meta_LazyDiscrTree_pushArgs(v___x_2651_, v_todo_2652_, v_e_2653_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_);
return v___x_2660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0___boxed(lean_object* v___x_2661_, lean_object* v_todo_2662_, lean_object* v_e_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_){
_start:
{
uint8_t v___x_3414__boxed_2670_; lean_object* v_res_2671_; 
v___x_3414__boxed_2670_ = lean_unbox(v___x_2661_);
v_res_2671_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0(v___x_3414__boxed_2670_, v_todo_2662_, v_e_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
lean_dec(v___y_2668_);
lean_dec_ref(v___y_2667_);
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2665_);
lean_dec(v___y_2664_);
return v_res_2671_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(lean_object* v_a_2672_, lean_object* v_b_2673_, lean_object* v_x_2674_){
_start:
{
if (lean_obj_tag(v_x_2674_) == 0)
{
lean_dec(v_b_2673_);
lean_dec(v_a_2672_);
return v_x_2674_;
}
else
{
lean_object* v_key_2675_; lean_object* v_value_2676_; lean_object* v_tail_2677_; lean_object* v___x_2679_; uint8_t v_isShared_2680_; uint8_t v_isSharedCheck_2689_; 
v_key_2675_ = lean_ctor_get(v_x_2674_, 0);
v_value_2676_ = lean_ctor_get(v_x_2674_, 1);
v_tail_2677_ = lean_ctor_get(v_x_2674_, 2);
v_isSharedCheck_2689_ = !lean_is_exclusive(v_x_2674_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2679_ = v_x_2674_;
v_isShared_2680_ = v_isSharedCheck_2689_;
goto v_resetjp_2678_;
}
else
{
lean_inc(v_tail_2677_);
lean_inc(v_value_2676_);
lean_inc(v_key_2675_);
lean_dec(v_x_2674_);
v___x_2679_ = lean_box(0);
v_isShared_2680_ = v_isSharedCheck_2689_;
goto v_resetjp_2678_;
}
v_resetjp_2678_:
{
uint8_t v___x_2681_; 
v___x_2681_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_2675_, v_a_2672_);
if (v___x_2681_ == 0)
{
lean_object* v___x_2682_; lean_object* v___x_2684_; 
v___x_2682_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(v_a_2672_, v_b_2673_, v_tail_2677_);
if (v_isShared_2680_ == 0)
{
lean_ctor_set(v___x_2679_, 2, v___x_2682_);
v___x_2684_ = v___x_2679_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v_key_2675_);
lean_ctor_set(v_reuseFailAlloc_2685_, 1, v_value_2676_);
lean_ctor_set(v_reuseFailAlloc_2685_, 2, v___x_2682_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
return v___x_2684_;
}
}
else
{
lean_object* v___x_2687_; 
lean_dec(v_value_2676_);
lean_dec(v_key_2675_);
if (v_isShared_2680_ == 0)
{
lean_ctor_set(v___x_2679_, 1, v_b_2673_);
lean_ctor_set(v___x_2679_, 0, v_a_2672_);
v___x_2687_ = v___x_2679_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v_a_2672_);
lean_ctor_set(v_reuseFailAlloc_2688_, 1, v_b_2673_);
lean_ctor_set(v_reuseFailAlloc_2688_, 2, v_tail_2677_);
v___x_2687_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
return v___x_2687_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(lean_object* v_a_2690_, lean_object* v_x_2691_){
_start:
{
if (lean_obj_tag(v_x_2691_) == 0)
{
uint8_t v___x_2692_; 
v___x_2692_ = 0;
return v___x_2692_;
}
else
{
lean_object* v_key_2693_; lean_object* v_tail_2694_; uint8_t v___x_2695_; 
v_key_2693_ = lean_ctor_get(v_x_2691_, 0);
v_tail_2694_ = lean_ctor_get(v_x_2691_, 2);
v___x_2695_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_2693_, v_a_2690_);
if (v___x_2695_ == 0)
{
v_x_2691_ = v_tail_2694_;
goto _start;
}
else
{
return v___x_2695_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg___boxed(lean_object* v_a_2697_, lean_object* v_x_2698_){
_start:
{
uint8_t v_res_2699_; lean_object* v_r_2700_; 
v_res_2699_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(v_a_2697_, v_x_2698_);
lean_dec(v_x_2698_);
lean_dec(v_a_2697_);
v_r_2700_ = lean_box(v_res_2699_);
return v_r_2700_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7___redArg(lean_object* v_x_2701_, lean_object* v_x_2702_){
_start:
{
if (lean_obj_tag(v_x_2702_) == 0)
{
return v_x_2701_;
}
else
{
lean_object* v_key_2703_; lean_object* v_value_2704_; lean_object* v_tail_2705_; lean_object* v___x_2707_; uint8_t v_isShared_2708_; uint8_t v_isSharedCheck_2728_; 
v_key_2703_ = lean_ctor_get(v_x_2702_, 0);
v_value_2704_ = lean_ctor_get(v_x_2702_, 1);
v_tail_2705_ = lean_ctor_get(v_x_2702_, 2);
v_isSharedCheck_2728_ = !lean_is_exclusive(v_x_2702_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2707_ = v_x_2702_;
v_isShared_2708_ = v_isSharedCheck_2728_;
goto v_resetjp_2706_;
}
else
{
lean_inc(v_tail_2705_);
lean_inc(v_value_2704_);
lean_inc(v_key_2703_);
lean_dec(v_x_2702_);
v___x_2707_ = lean_box(0);
v_isShared_2708_ = v_isSharedCheck_2728_;
goto v_resetjp_2706_;
}
v_resetjp_2706_:
{
lean_object* v___x_2709_; uint64_t v___x_2710_; uint64_t v___x_2711_; uint64_t v___x_2712_; uint64_t v_fold_2713_; uint64_t v___x_2714_; uint64_t v___x_2715_; uint64_t v___x_2716_; size_t v___x_2717_; size_t v___x_2718_; size_t v___x_2719_; size_t v___x_2720_; size_t v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2724_; 
v___x_2709_ = lean_array_get_size(v_x_2701_);
v___x_2710_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_key_2703_);
v___x_2711_ = 32ULL;
v___x_2712_ = lean_uint64_shift_right(v___x_2710_, v___x_2711_);
v_fold_2713_ = lean_uint64_xor(v___x_2710_, v___x_2712_);
v___x_2714_ = 16ULL;
v___x_2715_ = lean_uint64_shift_right(v_fold_2713_, v___x_2714_);
v___x_2716_ = lean_uint64_xor(v_fold_2713_, v___x_2715_);
v___x_2717_ = lean_uint64_to_usize(v___x_2716_);
v___x_2718_ = lean_usize_of_nat(v___x_2709_);
v___x_2719_ = ((size_t)1ULL);
v___x_2720_ = lean_usize_sub(v___x_2718_, v___x_2719_);
v___x_2721_ = lean_usize_land(v___x_2717_, v___x_2720_);
v___x_2722_ = lean_array_uget_borrowed(v_x_2701_, v___x_2721_);
lean_inc(v___x_2722_);
if (v_isShared_2708_ == 0)
{
lean_ctor_set(v___x_2707_, 2, v___x_2722_);
v___x_2724_ = v___x_2707_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v_key_2703_);
lean_ctor_set(v_reuseFailAlloc_2727_, 1, v_value_2704_);
lean_ctor_set(v_reuseFailAlloc_2727_, 2, v___x_2722_);
v___x_2724_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
lean_object* v___x_2725_; 
v___x_2725_ = lean_array_uset(v_x_2701_, v___x_2721_, v___x_2724_);
v_x_2701_ = v___x_2725_;
v_x_2702_ = v_tail_2705_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6___redArg(lean_object* v_i_2729_, lean_object* v_source_2730_, lean_object* v_target_2731_){
_start:
{
lean_object* v___x_2732_; uint8_t v___x_2733_; 
v___x_2732_ = lean_array_get_size(v_source_2730_);
v___x_2733_ = lean_nat_dec_lt(v_i_2729_, v___x_2732_);
if (v___x_2733_ == 0)
{
lean_dec_ref(v_source_2730_);
lean_dec(v_i_2729_);
return v_target_2731_;
}
else
{
lean_object* v_es_2734_; lean_object* v___x_2735_; lean_object* v_source_2736_; lean_object* v_target_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; 
v_es_2734_ = lean_array_fget(v_source_2730_, v_i_2729_);
v___x_2735_ = lean_box(0);
v_source_2736_ = lean_array_fset(v_source_2730_, v_i_2729_, v___x_2735_);
v_target_2737_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7___redArg(v_target_2731_, v_es_2734_);
v___x_2738_ = lean_unsigned_to_nat(1u);
v___x_2739_ = lean_nat_add(v_i_2729_, v___x_2738_);
lean_dec(v_i_2729_);
v_i_2729_ = v___x_2739_;
v_source_2730_ = v_source_2736_;
v_target_2731_ = v_target_2737_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5___redArg(lean_object* v_data_2741_){
_start:
{
lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v_nbuckets_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; 
v___x_2742_ = lean_array_get_size(v_data_2741_);
v___x_2743_ = lean_unsigned_to_nat(2u);
v_nbuckets_2744_ = lean_nat_mul(v___x_2742_, v___x_2743_);
v___x_2745_ = lean_unsigned_to_nat(0u);
v___x_2746_ = lean_box(0);
v___x_2747_ = lean_mk_array(v_nbuckets_2744_, v___x_2746_);
v___x_2748_ = lean_array_propagate_mark(v_data_2741_, v___x_2747_);
v___x_2749_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6___redArg(v___x_2745_, v_data_2741_, v___x_2748_);
return v___x_2749_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(lean_object* v_m_2750_, lean_object* v_a_2751_, lean_object* v_b_2752_){
_start:
{
lean_object* v_size_2753_; lean_object* v_buckets_2754_; lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2797_; 
v_size_2753_ = lean_ctor_get(v_m_2750_, 0);
v_buckets_2754_ = lean_ctor_get(v_m_2750_, 1);
v_isSharedCheck_2797_ = !lean_is_exclusive(v_m_2750_);
if (v_isSharedCheck_2797_ == 0)
{
v___x_2756_ = v_m_2750_;
v_isShared_2757_ = v_isSharedCheck_2797_;
goto v_resetjp_2755_;
}
else
{
lean_inc(v_buckets_2754_);
lean_inc(v_size_2753_);
lean_dec(v_m_2750_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2797_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
lean_object* v___x_2758_; uint64_t v___x_2759_; uint64_t v___x_2760_; uint64_t v___x_2761_; uint64_t v_fold_2762_; uint64_t v___x_2763_; uint64_t v___x_2764_; uint64_t v___x_2765_; size_t v___x_2766_; size_t v___x_2767_; size_t v___x_2768_; size_t v___x_2769_; size_t v___x_2770_; lean_object* v_bkt_2771_; uint8_t v___x_2772_; 
v___x_2758_ = lean_array_get_size(v_buckets_2754_);
v___x_2759_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_a_2751_);
v___x_2760_ = 32ULL;
v___x_2761_ = lean_uint64_shift_right(v___x_2759_, v___x_2760_);
v_fold_2762_ = lean_uint64_xor(v___x_2759_, v___x_2761_);
v___x_2763_ = 16ULL;
v___x_2764_ = lean_uint64_shift_right(v_fold_2762_, v___x_2763_);
v___x_2765_ = lean_uint64_xor(v_fold_2762_, v___x_2764_);
v___x_2766_ = lean_uint64_to_usize(v___x_2765_);
v___x_2767_ = lean_usize_of_nat(v___x_2758_);
v___x_2768_ = ((size_t)1ULL);
v___x_2769_ = lean_usize_sub(v___x_2767_, v___x_2768_);
v___x_2770_ = lean_usize_land(v___x_2766_, v___x_2769_);
v_bkt_2771_ = lean_array_uget_borrowed(v_buckets_2754_, v___x_2770_);
v___x_2772_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(v_a_2751_, v_bkt_2771_);
if (v___x_2772_ == 0)
{
lean_object* v___x_2773_; lean_object* v_size_x27_2774_; lean_object* v___x_2775_; lean_object* v_buckets_x27_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; uint8_t v___x_2782_; 
v___x_2773_ = lean_unsigned_to_nat(1u);
v_size_x27_2774_ = lean_nat_add(v_size_2753_, v___x_2773_);
lean_dec(v_size_2753_);
lean_inc(v_bkt_2771_);
v___x_2775_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2775_, 0, v_a_2751_);
lean_ctor_set(v___x_2775_, 1, v_b_2752_);
lean_ctor_set(v___x_2775_, 2, v_bkt_2771_);
v_buckets_x27_2776_ = lean_array_uset(v_buckets_2754_, v___x_2770_, v___x_2775_);
v___x_2777_ = lean_unsigned_to_nat(4u);
v___x_2778_ = lean_nat_mul(v_size_x27_2774_, v___x_2777_);
v___x_2779_ = lean_unsigned_to_nat(3u);
v___x_2780_ = lean_nat_div(v___x_2778_, v___x_2779_);
lean_dec(v___x_2778_);
v___x_2781_ = lean_array_get_size(v_buckets_x27_2776_);
v___x_2782_ = lean_nat_dec_le(v___x_2780_, v___x_2781_);
lean_dec(v___x_2780_);
if (v___x_2782_ == 0)
{
lean_object* v_val_2783_; lean_object* v___x_2785_; 
v_val_2783_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5___redArg(v_buckets_x27_2776_);
if (v_isShared_2757_ == 0)
{
lean_ctor_set(v___x_2756_, 1, v_val_2783_);
lean_ctor_set(v___x_2756_, 0, v_size_x27_2774_);
v___x_2785_ = v___x_2756_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v_size_x27_2774_);
lean_ctor_set(v_reuseFailAlloc_2786_, 1, v_val_2783_);
v___x_2785_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
return v___x_2785_;
}
}
else
{
lean_object* v___x_2788_; 
if (v_isShared_2757_ == 0)
{
lean_ctor_set(v___x_2756_, 1, v_buckets_x27_2776_);
lean_ctor_set(v___x_2756_, 0, v_size_x27_2774_);
v___x_2788_ = v___x_2756_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v_size_x27_2774_);
lean_ctor_set(v_reuseFailAlloc_2789_, 1, v_buckets_x27_2776_);
v___x_2788_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
return v___x_2788_;
}
}
}
else
{
lean_object* v___x_2790_; lean_object* v_buckets_x27_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2795_; 
lean_inc(v_bkt_2771_);
v___x_2790_ = lean_box(0);
v_buckets_x27_2791_ = lean_array_uset(v_buckets_2754_, v___x_2770_, v___x_2790_);
v___x_2792_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(v_a_2751_, v_b_2752_, v_bkt_2771_);
v___x_2793_ = lean_array_uset(v_buckets_x27_2791_, v___x_2770_, v___x_2792_);
if (v_isShared_2757_ == 0)
{
lean_ctor_set(v___x_2756_, 1, v___x_2793_);
v___x_2795_ = v___x_2756_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v_size_2753_);
lean_ctor_set(v_reuseFailAlloc_2796_, 1, v___x_2793_);
v___x_2795_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
return v___x_2795_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(lean_object* v_a_2798_, lean_object* v_x_2799_){
_start:
{
if (lean_obj_tag(v_x_2799_) == 0)
{
lean_object* v___x_2800_; 
v___x_2800_ = lean_box(0);
return v___x_2800_;
}
else
{
lean_object* v_key_2801_; lean_object* v_value_2802_; lean_object* v_tail_2803_; uint8_t v___x_2804_; 
v_key_2801_ = lean_ctor_get(v_x_2799_, 0);
v_value_2802_ = lean_ctor_get(v_x_2799_, 1);
v_tail_2803_ = lean_ctor_get(v_x_2799_, 2);
v___x_2804_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_2801_, v_a_2798_);
if (v___x_2804_ == 0)
{
v_x_2799_ = v_tail_2803_;
goto _start;
}
else
{
lean_object* v___x_2806_; 
lean_inc(v_value_2802_);
v___x_2806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2806_, 0, v_value_2802_);
return v___x_2806_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg___boxed(lean_object* v_a_2807_, lean_object* v_x_2808_){
_start:
{
lean_object* v_res_2809_; 
v_res_2809_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(v_a_2807_, v_x_2808_);
lean_dec(v_x_2808_);
lean_dec(v_a_2807_);
return v_res_2809_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(lean_object* v_m_2810_, lean_object* v_a_2811_){
_start:
{
lean_object* v_buckets_2812_; lean_object* v___x_2813_; uint64_t v___x_2814_; uint64_t v___x_2815_; uint64_t v___x_2816_; uint64_t v_fold_2817_; uint64_t v___x_2818_; uint64_t v___x_2819_; uint64_t v___x_2820_; size_t v___x_2821_; size_t v___x_2822_; size_t v___x_2823_; size_t v___x_2824_; size_t v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; 
v_buckets_2812_ = lean_ctor_get(v_m_2810_, 1);
v___x_2813_ = lean_array_get_size(v_buckets_2812_);
v___x_2814_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_a_2811_);
v___x_2815_ = 32ULL;
v___x_2816_ = lean_uint64_shift_right(v___x_2814_, v___x_2815_);
v_fold_2817_ = lean_uint64_xor(v___x_2814_, v___x_2816_);
v___x_2818_ = 16ULL;
v___x_2819_ = lean_uint64_shift_right(v_fold_2817_, v___x_2818_);
v___x_2820_ = lean_uint64_xor(v_fold_2817_, v___x_2819_);
v___x_2821_ = lean_uint64_to_usize(v___x_2820_);
v___x_2822_ = lean_usize_of_nat(v___x_2813_);
v___x_2823_ = ((size_t)1ULL);
v___x_2824_ = lean_usize_sub(v___x_2822_, v___x_2823_);
v___x_2825_ = lean_usize_land(v___x_2821_, v___x_2824_);
v___x_2826_ = lean_array_uget_borrowed(v_buckets_2812_, v___x_2825_);
v___x_2827_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(v_a_2811_, v___x_2826_);
return v___x_2827_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg___boxed(lean_object* v_m_2828_, lean_object* v_a_2829_){
_start:
{
lean_object* v_res_2830_; 
v_res_2830_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_m_2828_, v_a_2829_);
lean_dec(v_a_2829_);
lean_dec_ref(v_m_2828_);
return v_res_2830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(lean_object* v_p_2831_, lean_object* v_entry_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_){
_start:
{
lean_object* v_snd_2839_; lean_object* v_snd_2840_; lean_object* v_fst_2841_; lean_object* v_fst_2842_; lean_object* v_snd_2843_; lean_object* v_fst_2844_; lean_object* v_fst_2845_; lean_object* v_snd_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; uint8_t v___x_2849_; 
v_snd_2839_ = lean_ctor_get(v_p_2831_, 1);
v_snd_2840_ = lean_ctor_get(v_entry_2832_, 1);
lean_inc(v_snd_2840_);
v_fst_2841_ = lean_ctor_get(v_p_2831_, 0);
v_fst_2842_ = lean_ctor_get(v_snd_2839_, 0);
v_snd_2843_ = lean_ctor_get(v_snd_2839_, 1);
v_fst_2844_ = lean_ctor_get(v_entry_2832_, 0);
lean_inc(v_fst_2844_);
lean_dec_ref(v_entry_2832_);
v_fst_2845_ = lean_ctor_get(v_snd_2840_, 0);
lean_inc(v_fst_2845_);
v_snd_2846_ = lean_ctor_get(v_snd_2840_, 1);
v___x_2847_ = lean_array_get_size(v_fst_2844_);
v___x_2848_ = lean_unsigned_to_nat(0u);
v___x_2849_ = lean_nat_dec_eq(v___x_2847_, v___x_2848_);
if (v___x_2849_ == 0)
{
lean_object* v_fst_2850_; lean_object* v_snd_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2956_; 
v_fst_2850_ = lean_ctor_get(v_fst_2845_, 0);
v_snd_2851_ = lean_ctor_get(v_fst_2845_, 1);
v_isSharedCheck_2956_ = !lean_is_exclusive(v_fst_2845_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2853_ = v_fst_2845_;
v_isShared_2854_ = v_isSharedCheck_2956_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_snd_2851_);
lean_inc(v_fst_2850_);
lean_dec(v_fst_2845_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2956_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v_e_2858_; lean_object* v_todo_2859_; lean_object* v___x_2860_; lean_object* v___f_2861_; lean_object* v___x_2862_; 
v___x_2855_ = l_Lean_instInhabitedExpr;
v___x_2856_ = lean_unsigned_to_nat(1u);
v___x_2857_ = lean_nat_sub(v___x_2847_, v___x_2856_);
v_e_2858_ = lean_array_get(v___x_2855_, v_fst_2844_, v___x_2857_);
lean_dec(v___x_2857_);
v_todo_2859_ = lean_array_pop(v_fst_2844_);
v___x_2860_ = lean_box(v___x_2849_);
v___f_2861_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2861_, 0, v___x_2860_);
lean_closure_set(v___f_2861_, 1, v_todo_2859_);
lean_closure_set(v___f_2861_, 2, v_e_2858_);
v___x_2862_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(v_fst_2850_, v_snd_2851_, v___f_2861_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_);
if (lean_obj_tag(v___x_2862_) == 0)
{
lean_object* v_a_2863_; lean_object* v_fst_2864_; lean_object* v_snd_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2947_; 
v_a_2863_ = lean_ctor_get(v___x_2862_, 0);
lean_inc(v_a_2863_);
lean_dec_ref_known(v___x_2862_, 1);
v_fst_2864_ = lean_ctor_get(v_a_2863_, 0);
v_snd_2865_ = lean_ctor_get(v_a_2863_, 1);
v_isSharedCheck_2947_ = !lean_is_exclusive(v_a_2863_);
if (v_isSharedCheck_2947_ == 0)
{
v___x_2867_ = v_a_2863_;
v_isShared_2868_ = v_isSharedCheck_2947_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_snd_2865_);
lean_inc(v_fst_2864_);
lean_dec(v_a_2863_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2947_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
lean_object* v___x_2869_; uint8_t v___x_2870_; 
v___x_2869_ = lean_box(3);
v___x_2870_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_fst_2864_, v___x_2869_);
if (v___x_2870_ == 0)
{
lean_object* v___x_2871_; 
v___x_2871_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_snd_2843_, v_fst_2864_);
if (lean_obj_tag(v___x_2871_) == 0)
{
lean_object* v___x_2873_; 
lean_inc(v_snd_2843_);
lean_inc(v_fst_2842_);
lean_inc(v_fst_2841_);
lean_dec_ref(v_p_2831_);
lean_inc(v_snd_2840_);
if (v_isShared_2868_ == 0)
{
lean_ctor_set(v___x_2867_, 1, v_snd_2840_);
lean_ctor_set(v___x_2867_, 0, v_snd_2865_);
v___x_2873_ = v___x_2867_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v_snd_2865_);
lean_ctor_set(v_reuseFailAlloc_2896_, 1, v_snd_2840_);
v___x_2873_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2893_; 
v_isSharedCheck_2893_ = !lean_is_exclusive(v_snd_2840_);
if (v_isSharedCheck_2893_ == 0)
{
lean_object* v_unused_2894_; lean_object* v_unused_2895_; 
v_unused_2894_ = lean_ctor_get(v_snd_2840_, 1);
lean_dec(v_unused_2894_);
v_unused_2895_ = lean_ctor_get(v_snd_2840_, 0);
lean_dec(v_unused_2895_);
v___x_2875_ = v_snd_2840_;
v_isShared_2876_ = v_isSharedCheck_2893_;
goto v_resetjp_2874_;
}
else
{
lean_dec(v_snd_2840_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2893_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
lean_object* v___x_2877_; lean_object* v_a_2878_; lean_object* v___x_2880_; uint8_t v_isShared_2881_; uint8_t v_isSharedCheck_2892_; 
v___x_2877_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v___x_2873_, v_a_2833_);
v_a_2878_ = lean_ctor_get(v___x_2877_, 0);
v_isSharedCheck_2892_ = !lean_is_exclusive(v___x_2877_);
if (v_isSharedCheck_2892_ == 0)
{
v___x_2880_ = v___x_2877_;
v_isShared_2881_ = v_isSharedCheck_2892_;
goto v_resetjp_2879_;
}
else
{
lean_inc(v_a_2878_);
lean_dec(v___x_2877_);
v___x_2880_ = lean_box(0);
v_isShared_2881_ = v_isSharedCheck_2892_;
goto v_resetjp_2879_;
}
v_resetjp_2879_:
{
lean_object* v___x_2882_; lean_object* v___x_2884_; 
v___x_2882_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_snd_2843_, v_fst_2864_, v_a_2878_);
if (v_isShared_2854_ == 0)
{
lean_ctor_set(v___x_2853_, 1, v___x_2882_);
lean_ctor_set(v___x_2853_, 0, v_fst_2842_);
v___x_2884_ = v___x_2853_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v_fst_2842_);
lean_ctor_set(v_reuseFailAlloc_2891_, 1, v___x_2882_);
v___x_2884_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
lean_object* v___x_2886_; 
if (v_isShared_2876_ == 0)
{
lean_ctor_set(v___x_2875_, 1, v___x_2884_);
lean_ctor_set(v___x_2875_, 0, v_fst_2841_);
v___x_2886_ = v___x_2875_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v_fst_2841_);
lean_ctor_set(v_reuseFailAlloc_2890_, 1, v___x_2884_);
v___x_2886_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
lean_object* v___x_2888_; 
if (v_isShared_2881_ == 0)
{
lean_ctor_set(v___x_2880_, 0, v___x_2886_);
v___x_2888_ = v___x_2880_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v___x_2886_);
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
}
}
}
else
{
lean_object* v_val_2897_; lean_object* v___x_2899_; 
lean_dec(v_fst_2864_);
lean_del_object(v___x_2853_);
v_val_2897_ = lean_ctor_get(v___x_2871_, 0);
lean_inc(v_val_2897_);
lean_dec_ref_known(v___x_2871_, 1);
if (v_isShared_2868_ == 0)
{
lean_ctor_set(v___x_2867_, 1, v_snd_2840_);
lean_ctor_set(v___x_2867_, 0, v_snd_2865_);
v___x_2899_ = v___x_2867_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v_snd_2865_);
lean_ctor_set(v_reuseFailAlloc_2909_, 1, v_snd_2840_);
v___x_2899_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
lean_object* v___x_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2907_; 
v___x_2900_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_val_2897_, v___x_2899_, v_a_2833_);
lean_dec(v_val_2897_);
v_isSharedCheck_2907_ = !lean_is_exclusive(v___x_2900_);
if (v_isSharedCheck_2907_ == 0)
{
lean_object* v_unused_2908_; 
v_unused_2908_ = lean_ctor_get(v___x_2900_, 0);
lean_dec(v_unused_2908_);
v___x_2902_ = v___x_2900_;
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
else
{
lean_dec(v___x_2900_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v___x_2905_; 
if (v_isShared_2903_ == 0)
{
lean_ctor_set(v___x_2902_, 0, v_p_2831_);
v___x_2905_ = v___x_2902_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v_p_2831_);
v___x_2905_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
return v___x_2905_;
}
}
}
}
}
else
{
uint8_t v___x_2910_; 
lean_dec(v_fst_2864_);
v___x_2910_ = lean_nat_dec_eq(v_fst_2842_, v___x_2848_);
if (v___x_2910_ == 0)
{
lean_object* v___x_2912_; 
lean_del_object(v___x_2853_);
if (v_isShared_2868_ == 0)
{
lean_ctor_set(v___x_2867_, 1, v_snd_2840_);
lean_ctor_set(v___x_2867_, 0, v_snd_2865_);
v___x_2912_ = v___x_2867_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v_snd_2865_);
lean_ctor_set(v_reuseFailAlloc_2922_, 1, v_snd_2840_);
v___x_2912_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
lean_object* v___x_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2920_; 
v___x_2913_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_fst_2842_, v___x_2912_, v_a_2833_);
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2913_);
if (v_isSharedCheck_2920_ == 0)
{
lean_object* v_unused_2921_; 
v_unused_2921_ = lean_ctor_get(v___x_2913_, 0);
lean_dec(v_unused_2921_);
v___x_2915_ = v___x_2913_;
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
else
{
lean_dec(v___x_2913_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
lean_object* v___x_2918_; 
if (v_isShared_2916_ == 0)
{
lean_ctor_set(v___x_2915_, 0, v_p_2831_);
v___x_2918_ = v___x_2915_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v_p_2831_);
v___x_2918_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
return v___x_2918_;
}
}
}
}
else
{
lean_object* v___x_2924_; 
lean_inc(v_snd_2843_);
lean_inc(v_fst_2841_);
lean_dec_ref(v_p_2831_);
lean_inc(v_snd_2840_);
if (v_isShared_2868_ == 0)
{
lean_ctor_set(v___x_2867_, 1, v_snd_2840_);
lean_ctor_set(v___x_2867_, 0, v_snd_2865_);
v___x_2924_ = v___x_2867_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v_snd_2865_);
lean_ctor_set(v_reuseFailAlloc_2946_, 1, v_snd_2840_);
v___x_2924_ = v_reuseFailAlloc_2946_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2943_; 
v_isSharedCheck_2943_ = !lean_is_exclusive(v_snd_2840_);
if (v_isSharedCheck_2943_ == 0)
{
lean_object* v_unused_2944_; lean_object* v_unused_2945_; 
v_unused_2944_ = lean_ctor_get(v_snd_2840_, 1);
lean_dec(v_unused_2944_);
v_unused_2945_ = lean_ctor_get(v_snd_2840_, 0);
lean_dec(v_unused_2945_);
v___x_2926_ = v_snd_2840_;
v_isShared_2927_ = v_isSharedCheck_2943_;
goto v_resetjp_2925_;
}
else
{
lean_dec(v_snd_2840_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_2943_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
lean_object* v___x_2928_; lean_object* v_a_2929_; lean_object* v___x_2931_; uint8_t v_isShared_2932_; uint8_t v_isSharedCheck_2942_; 
v___x_2928_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v___x_2924_, v_a_2833_);
v_a_2929_ = lean_ctor_get(v___x_2928_, 0);
v_isSharedCheck_2942_ = !lean_is_exclusive(v___x_2928_);
if (v_isSharedCheck_2942_ == 0)
{
v___x_2931_ = v___x_2928_;
v_isShared_2932_ = v_isSharedCheck_2942_;
goto v_resetjp_2930_;
}
else
{
lean_inc(v_a_2929_);
lean_dec(v___x_2928_);
v___x_2931_ = lean_box(0);
v_isShared_2932_ = v_isSharedCheck_2942_;
goto v_resetjp_2930_;
}
v_resetjp_2930_:
{
lean_object* v___x_2934_; 
if (v_isShared_2854_ == 0)
{
lean_ctor_set(v___x_2853_, 1, v_snd_2843_);
lean_ctor_set(v___x_2853_, 0, v_a_2929_);
v___x_2934_ = v___x_2853_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2941_; 
v_reuseFailAlloc_2941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2941_, 0, v_a_2929_);
lean_ctor_set(v_reuseFailAlloc_2941_, 1, v_snd_2843_);
v___x_2934_ = v_reuseFailAlloc_2941_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
lean_object* v___x_2936_; 
if (v_isShared_2927_ == 0)
{
lean_ctor_set(v___x_2926_, 1, v___x_2934_);
lean_ctor_set(v___x_2926_, 0, v_fst_2841_);
v___x_2936_ = v___x_2926_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_fst_2841_);
lean_ctor_set(v_reuseFailAlloc_2940_, 1, v___x_2934_);
v___x_2936_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2935_;
}
v_reusejp_2935_:
{
lean_object* v___x_2938_; 
if (v_isShared_2932_ == 0)
{
lean_ctor_set(v___x_2931_, 0, v___x_2936_);
v___x_2938_ = v___x_2931_;
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
}
}
}
}
}
}
}
else
{
lean_object* v_a_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2955_; 
lean_del_object(v___x_2853_);
lean_dec(v_snd_2840_);
lean_dec_ref(v_p_2831_);
v_a_2948_ = lean_ctor_get(v___x_2862_, 0);
v_isSharedCheck_2955_ = !lean_is_exclusive(v___x_2862_);
if (v_isSharedCheck_2955_ == 0)
{
v___x_2950_ = v___x_2862_;
v_isShared_2951_ = v_isSharedCheck_2955_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_a_2948_);
lean_dec(v___x_2862_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_2955_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v___x_2953_; 
if (v_isShared_2951_ == 0)
{
v___x_2953_ = v___x_2950_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v_a_2948_);
v___x_2953_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
return v___x_2953_;
}
}
}
}
}
else
{
lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_2965_; 
lean_inc(v_snd_2846_);
lean_inc(v_fst_2841_);
lean_inc(v_snd_2839_);
lean_dec(v_fst_2845_);
lean_dec(v_fst_2844_);
lean_dec_ref(v_p_2831_);
v_isSharedCheck_2965_ = !lean_is_exclusive(v_snd_2840_);
if (v_isSharedCheck_2965_ == 0)
{
lean_object* v_unused_2966_; lean_object* v_unused_2967_; 
v_unused_2966_ = lean_ctor_get(v_snd_2840_, 1);
lean_dec(v_unused_2966_);
v_unused_2967_ = lean_ctor_get(v_snd_2840_, 0);
lean_dec(v_unused_2967_);
v___x_2958_ = v_snd_2840_;
v_isShared_2959_ = v_isSharedCheck_2965_;
goto v_resetjp_2957_;
}
else
{
lean_dec(v_snd_2840_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_2965_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v_values_2960_; lean_object* v___x_2962_; 
v_values_2960_ = lean_array_push(v_fst_2841_, v_snd_2846_);
if (v_isShared_2959_ == 0)
{
lean_ctor_set(v___x_2958_, 1, v_snd_2839_);
lean_ctor_set(v___x_2958_, 0, v_values_2960_);
v___x_2962_ = v___x_2958_;
goto v_reusejp_2961_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v_values_2960_);
lean_ctor_set(v_reuseFailAlloc_2964_, 1, v_snd_2839_);
v___x_2962_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2961_;
}
v_reusejp_2961_:
{
lean_object* v___x_2963_; 
v___x_2963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2963_, 0, v___x_2962_);
return v___x_2963_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___boxed(lean_object* v_p_2968_, lean_object* v_entry_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_){
_start:
{
lean_object* v_res_2976_; 
v_res_2976_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(v_p_2968_, v_entry_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
lean_dec(v_a_2974_);
lean_dec_ref(v_a_2973_);
lean_dec(v_a_2972_);
lean_dec_ref(v_a_2971_);
lean_dec(v_a_2970_);
return v_res_2976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry(lean_object* v_00_u03b1_2977_, lean_object* v_p_2978_, lean_object* v_entry_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_){
_start:
{
lean_object* v___x_2986_; 
v___x_2986_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(v_p_2978_, v_entry_2979_, v_a_2980_, v_a_2981_, v_a_2982_, v_a_2983_, v_a_2984_);
return v___x_2986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___boxed(lean_object* v_00_u03b1_2987_, lean_object* v_p_2988_, lean_object* v_entry_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_){
_start:
{
lean_object* v_res_2996_; 
v_res_2996_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry(v_00_u03b1_2987_, v_p_2988_, v_entry_2989_, v_a_2990_, v_a_2991_, v_a_2992_, v_a_2993_, v_a_2994_);
lean_dec(v_a_2994_);
lean_dec_ref(v_a_2993_);
lean_dec(v_a_2992_);
lean_dec_ref(v_a_2991_);
lean_dec(v_a_2990_);
return v_res_2996_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1(lean_object* v_00_u03b2_2997_, lean_object* v_m_2998_, lean_object* v_a_2999_){
_start:
{
lean_object* v___x_3000_; 
v___x_3000_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_m_2998_, v_a_2999_);
return v___x_3000_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___boxed(lean_object* v_00_u03b2_3001_, lean_object* v_m_3002_, lean_object* v_a_3003_){
_start:
{
lean_object* v_res_3004_; 
v_res_3004_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1(v_00_u03b2_3001_, v_m_3002_, v_a_3003_);
lean_dec(v_a_3003_);
lean_dec_ref(v_m_3002_);
return v_res_3004_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3(lean_object* v_00_u03b2_3005_, lean_object* v_m_3006_, lean_object* v_a_3007_, lean_object* v_b_3008_){
_start:
{
lean_object* v___x_3009_; 
v___x_3009_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_m_3006_, v_a_3007_, v_b_3008_);
return v___x_3009_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1(lean_object* v_00_u03b2_3010_, lean_object* v_a_3011_, lean_object* v_x_3012_){
_start:
{
lean_object* v___x_3013_; 
v___x_3013_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(v_a_3011_, v_x_3012_);
return v___x_3013_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___boxed(lean_object* v_00_u03b2_3014_, lean_object* v_a_3015_, lean_object* v_x_3016_){
_start:
{
lean_object* v_res_3017_; 
v_res_3017_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1(v_00_u03b2_3014_, v_a_3015_, v_x_3016_);
lean_dec(v_x_3016_);
lean_dec(v_a_3015_);
return v_res_3017_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4(lean_object* v_00_u03b2_3018_, lean_object* v_a_3019_, lean_object* v_x_3020_){
_start:
{
uint8_t v___x_3021_; 
v___x_3021_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(v_a_3019_, v_x_3020_);
return v___x_3021_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___boxed(lean_object* v_00_u03b2_3022_, lean_object* v_a_3023_, lean_object* v_x_3024_){
_start:
{
uint8_t v_res_3025_; lean_object* v_r_3026_; 
v_res_3025_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4(v_00_u03b2_3022_, v_a_3023_, v_x_3024_);
lean_dec(v_x_3024_);
lean_dec(v_a_3023_);
v_r_3026_ = lean_box(v_res_3025_);
return v_r_3026_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5(lean_object* v_00_u03b2_3027_, lean_object* v_data_3028_){
_start:
{
lean_object* v___x_3029_; 
v___x_3029_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5___redArg(v_data_3028_);
return v___x_3029_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6(lean_object* v_00_u03b2_3030_, lean_object* v_a_3031_, lean_object* v_b_3032_, lean_object* v_x_3033_){
_start:
{
lean_object* v___x_3034_; 
v___x_3034_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(v_a_3031_, v_b_3032_, v_x_3033_);
return v___x_3034_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_3035_, lean_object* v_i_3036_, lean_object* v_source_3037_, lean_object* v_target_3038_){
_start:
{
lean_object* v___x_3039_; 
v___x_3039_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6___redArg(v_i_3036_, v_source_3037_, v_target_3038_);
return v___x_3039_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_3040_, lean_object* v_x_3041_, lean_object* v_x_3042_){
_start:
{
lean_object* v___x_3043_; 
v___x_3043_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7___redArg(v_x_3041_, v_x_3042_);
return v___x_3043_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(lean_object* v_as_3044_, size_t v_i_3045_, size_t v_stop_3046_, lean_object* v_b_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_){
_start:
{
uint8_t v___x_3054_; 
v___x_3054_ = lean_usize_dec_eq(v_i_3045_, v_stop_3046_);
if (v___x_3054_ == 0)
{
lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3055_ = lean_array_uget_borrowed(v_as_3044_, v_i_3045_);
lean_inc(v___x_3055_);
v___x_3056_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(v_b_3047_, v___x_3055_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_);
if (lean_obj_tag(v___x_3056_) == 0)
{
lean_object* v_a_3057_; size_t v___x_3058_; size_t v___x_3059_; 
v_a_3057_ = lean_ctor_get(v___x_3056_, 0);
lean_inc(v_a_3057_);
lean_dec_ref_known(v___x_3056_, 1);
v___x_3058_ = ((size_t)1ULL);
v___x_3059_ = lean_usize_add(v_i_3045_, v___x_3058_);
v_i_3045_ = v___x_3059_;
v_b_3047_ = v_a_3057_;
goto _start;
}
else
{
return v___x_3056_;
}
}
else
{
lean_object* v___x_3061_; 
v___x_3061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3061_, 0, v_b_3047_);
return v___x_3061_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg___boxed(lean_object* v_as_3062_, lean_object* v_i_3063_, lean_object* v_stop_3064_, lean_object* v_b_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_){
_start:
{
size_t v_i_boxed_3072_; size_t v_stop_boxed_3073_; lean_object* v_res_3074_; 
v_i_boxed_3072_ = lean_unbox_usize(v_i_3063_);
lean_dec(v_i_3063_);
v_stop_boxed_3073_ = lean_unbox_usize(v_stop_3064_);
lean_dec(v_stop_3064_);
v_res_3074_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_as_3062_, v_i_boxed_3072_, v_stop_boxed_3073_, v_b_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_);
lean_dec(v___y_3070_);
lean_dec_ref(v___y_3069_);
lean_dec(v___y_3068_);
lean_dec_ref(v___y_3067_);
lean_dec(v___y_3066_);
lean_dec_ref(v_as_3062_);
return v_res_3074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(lean_object* v_values_3075_, lean_object* v_starIdx_3076_, lean_object* v_children_3077_, lean_object* v_entries_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_){
_start:
{
lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; uint8_t v___x_3089_; 
v___x_3085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3085_, 0, v_starIdx_3076_);
lean_ctor_set(v___x_3085_, 1, v_children_3077_);
v___x_3086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3086_, 0, v_values_3075_);
lean_ctor_set(v___x_3086_, 1, v___x_3085_);
v___x_3087_ = lean_unsigned_to_nat(0u);
v___x_3088_ = lean_array_get_size(v_entries_3078_);
v___x_3089_ = lean_nat_dec_lt(v___x_3087_, v___x_3088_);
if (v___x_3089_ == 0)
{
lean_object* v___x_3090_; 
v___x_3090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3090_, 0, v___x_3086_);
return v___x_3090_;
}
else
{
uint8_t v___x_3091_; 
v___x_3091_ = lean_nat_dec_le(v___x_3088_, v___x_3088_);
if (v___x_3091_ == 0)
{
if (v___x_3089_ == 0)
{
lean_object* v___x_3092_; 
v___x_3092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3092_, 0, v___x_3086_);
return v___x_3092_;
}
else
{
size_t v___x_3093_; size_t v___x_3094_; lean_object* v___x_3095_; 
v___x_3093_ = ((size_t)0ULL);
v___x_3094_ = lean_usize_of_nat(v___x_3088_);
v___x_3095_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_entries_3078_, v___x_3093_, v___x_3094_, v___x_3086_, v_a_3079_, v_a_3080_, v_a_3081_, v_a_3082_, v_a_3083_);
return v___x_3095_;
}
}
else
{
size_t v___x_3096_; size_t v___x_3097_; lean_object* v___x_3098_; 
v___x_3096_ = ((size_t)0ULL);
v___x_3097_ = lean_usize_of_nat(v___x_3088_);
v___x_3098_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_entries_3078_, v___x_3096_, v___x_3097_, v___x_3086_, v_a_3079_, v_a_3080_, v_a_3081_, v_a_3082_, v_a_3083_);
return v___x_3098_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg___boxed(lean_object* v_values_3099_, lean_object* v_starIdx_3100_, lean_object* v_children_3101_, lean_object* v_entries_3102_, lean_object* v_a_3103_, lean_object* v_a_3104_, lean_object* v_a_3105_, lean_object* v_a_3106_, lean_object* v_a_3107_, lean_object* v_a_3108_){
_start:
{
lean_object* v_res_3109_; 
v_res_3109_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(v_values_3099_, v_starIdx_3100_, v_children_3101_, v_entries_3102_, v_a_3103_, v_a_3104_, v_a_3105_, v_a_3106_, v_a_3107_);
lean_dec(v_a_3107_);
lean_dec_ref(v_a_3106_);
lean_dec(v_a_3105_);
lean_dec_ref(v_a_3104_);
lean_dec(v_a_3103_);
lean_dec_ref(v_entries_3102_);
return v_res_3109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries(lean_object* v_00_u03b1_3110_, lean_object* v_values_3111_, lean_object* v_starIdx_3112_, lean_object* v_children_3113_, lean_object* v_entries_3114_, lean_object* v_a_3115_, lean_object* v_a_3116_, lean_object* v_a_3117_, lean_object* v_a_3118_, lean_object* v_a_3119_){
_start:
{
lean_object* v___x_3121_; 
v___x_3121_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(v_values_3111_, v_starIdx_3112_, v_children_3113_, v_entries_3114_, v_a_3115_, v_a_3116_, v_a_3117_, v_a_3118_, v_a_3119_);
return v___x_3121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries___boxed(lean_object* v_00_u03b1_3122_, lean_object* v_values_3123_, lean_object* v_starIdx_3124_, lean_object* v_children_3125_, lean_object* v_entries_3126_, lean_object* v_a_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_){
_start:
{
lean_object* v_res_3133_; 
v_res_3133_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries(v_00_u03b1_3122_, v_values_3123_, v_starIdx_3124_, v_children_3125_, v_entries_3126_, v_a_3127_, v_a_3128_, v_a_3129_, v_a_3130_, v_a_3131_);
lean_dec(v_a_3131_);
lean_dec_ref(v_a_3130_);
lean_dec(v_a_3129_);
lean_dec_ref(v_a_3128_);
lean_dec(v_a_3127_);
lean_dec_ref(v_entries_3126_);
return v_res_3133_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0(lean_object* v_00_u03b1_3134_, lean_object* v_as_3135_, size_t v_i_3136_, size_t v_stop_3137_, lean_object* v_b_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_){
_start:
{
lean_object* v___x_3145_; 
v___x_3145_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_as_3135_, v_i_3136_, v_stop_3137_, v_b_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
return v___x_3145_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___boxed(lean_object* v_00_u03b1_3146_, lean_object* v_as_3147_, lean_object* v_i_3148_, lean_object* v_stop_3149_, lean_object* v_b_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_){
_start:
{
size_t v_i_boxed_3157_; size_t v_stop_boxed_3158_; lean_object* v_res_3159_; 
v_i_boxed_3157_ = lean_unbox_usize(v_i_3148_);
lean_dec(v_i_3148_);
v_stop_boxed_3158_ = lean_unbox_usize(v_stop_3149_);
lean_dec(v_stop_3149_);
v_res_3159_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0(v_00_u03b1_3146_, v_as_3147_, v_i_boxed_3157_, v_stop_boxed_3158_, v_b_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_);
lean_dec(v___y_3155_);
lean_dec_ref(v___y_3154_);
lean_dec(v___y_3153_);
lean_dec_ref(v___y_3152_);
lean_dec(v___y_3151_);
lean_dec_ref(v_as_3147_);
return v_res_3159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode___redArg(lean_object* v_c_3160_, lean_object* v_a_3161_, lean_object* v_a_3162_, lean_object* v_a_3163_, lean_object* v_a_3164_, lean_object* v_a_3165_){
_start:
{
lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v_values_3170_; lean_object* v_star_3171_; lean_object* v_children_3172_; lean_object* v_pending_3173_; lean_object* v___x_3175_; uint8_t v_isShared_3176_; uint8_t v_isSharedCheck_3203_; 
v___x_3167_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0);
v___x_3168_ = lean_st_ref_get(v_a_3161_);
v___x_3169_ = lean_array_get(v___x_3167_, v___x_3168_, v_c_3160_);
lean_dec(v___x_3168_);
v_values_3170_ = lean_ctor_get(v___x_3169_, 0);
v_star_3171_ = lean_ctor_get(v___x_3169_, 1);
v_children_3172_ = lean_ctor_get(v___x_3169_, 2);
v_pending_3173_ = lean_ctor_get(v___x_3169_, 3);
v_isSharedCheck_3203_ = !lean_is_exclusive(v___x_3169_);
if (v_isSharedCheck_3203_ == 0)
{
v___x_3175_ = v___x_3169_;
v_isShared_3176_ = v_isSharedCheck_3203_;
goto v_resetjp_3174_;
}
else
{
lean_inc(v_pending_3173_);
lean_inc(v_children_3172_);
lean_inc(v_star_3171_);
lean_inc(v_values_3170_);
lean_dec(v___x_3169_);
v___x_3175_ = lean_box(0);
v_isShared_3176_ = v_isSharedCheck_3203_;
goto v_resetjp_3174_;
}
v_resetjp_3174_:
{
lean_object* v___x_3177_; lean_object* v___x_3178_; uint8_t v___x_3179_; 
v___x_3177_ = lean_array_get_size(v_pending_3173_);
v___x_3178_ = lean_unsigned_to_nat(0u);
v___x_3179_ = lean_nat_dec_eq(v___x_3177_, v___x_3178_);
if (v___x_3179_ == 0)
{
lean_object* v___x_3180_; lean_object* v___x_3181_; 
v___x_3180_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_c_3160_, v___x_3167_, v_a_3161_);
lean_dec_ref(v___x_3180_);
v___x_3181_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(v_values_3170_, v_star_3171_, v_children_3172_, v_pending_3173_, v_a_3161_, v_a_3162_, v_a_3163_, v_a_3164_, v_a_3165_);
lean_dec_ref(v_pending_3173_);
if (lean_obj_tag(v___x_3181_) == 0)
{
lean_object* v_a_3182_; lean_object* v_snd_3183_; lean_object* v_fst_3184_; lean_object* v_fst_3185_; lean_object* v_snd_3186_; lean_object* v___x_3187_; lean_object* v___x_3189_; 
v_a_3182_ = lean_ctor_get(v___x_3181_, 0);
lean_inc(v_a_3182_);
lean_dec_ref_known(v___x_3181_, 1);
v_snd_3183_ = lean_ctor_get(v_a_3182_, 1);
v_fst_3184_ = lean_ctor_get(v_a_3182_, 0);
v_fst_3185_ = lean_ctor_get(v_snd_3183_, 0);
v_snd_3186_ = lean_ctor_get(v_snd_3183_, 1);
v___x_3187_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__3));
lean_inc(v_snd_3186_);
lean_inc(v_fst_3185_);
lean_inc(v_fst_3184_);
if (v_isShared_3176_ == 0)
{
lean_ctor_set(v___x_3175_, 3, v___x_3187_);
lean_ctor_set(v___x_3175_, 2, v_snd_3186_);
lean_ctor_set(v___x_3175_, 1, v_fst_3185_);
lean_ctor_set(v___x_3175_, 0, v_fst_3184_);
v___x_3189_ = v___x_3175_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v_fst_3184_);
lean_ctor_set(v_reuseFailAlloc_3199_, 1, v_fst_3185_);
lean_ctor_set(v_reuseFailAlloc_3199_, 2, v_snd_3186_);
lean_ctor_set(v_reuseFailAlloc_3199_, 3, v___x_3187_);
v___x_3189_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
lean_object* v___x_3190_; lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3197_; 
v___x_3190_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_c_3160_, v___x_3189_, v_a_3161_);
v_isSharedCheck_3197_ = !lean_is_exclusive(v___x_3190_);
if (v_isSharedCheck_3197_ == 0)
{
lean_object* v_unused_3198_; 
v_unused_3198_ = lean_ctor_get(v___x_3190_, 0);
lean_dec(v_unused_3198_);
v___x_3192_ = v___x_3190_;
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
else
{
lean_dec(v___x_3190_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
lean_object* v___x_3195_; 
if (v_isShared_3193_ == 0)
{
lean_ctor_set(v___x_3192_, 0, v_a_3182_);
v___x_3195_ = v___x_3192_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v_a_3182_);
v___x_3195_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
return v___x_3195_;
}
}
}
}
else
{
lean_del_object(v___x_3175_);
return v___x_3181_;
}
}
else
{
lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; 
lean_del_object(v___x_3175_);
lean_dec_ref(v_pending_3173_);
v___x_3200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3200_, 0, v_star_3171_);
lean_ctor_set(v___x_3200_, 1, v_children_3172_);
v___x_3201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3201_, 0, v_values_3170_);
lean_ctor_set(v___x_3201_, 1, v___x_3200_);
v___x_3202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3202_, 0, v___x_3201_);
return v___x_3202_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode___redArg___boxed(lean_object* v_c_3204_, lean_object* v_a_3205_, lean_object* v_a_3206_, lean_object* v_a_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_){
_start:
{
lean_object* v_res_3211_; 
v_res_3211_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_c_3204_, v_a_3205_, v_a_3206_, v_a_3207_, v_a_3208_, v_a_3209_);
lean_dec(v_a_3209_);
lean_dec_ref(v_a_3208_);
lean_dec(v_a_3207_);
lean_dec_ref(v_a_3206_);
lean_dec(v_a_3205_);
lean_dec(v_c_3204_);
return v_res_3211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode(lean_object* v_00_u03b1_3212_, lean_object* v_c_3213_, lean_object* v_a_3214_, lean_object* v_a_3215_, lean_object* v_a_3216_, lean_object* v_a_3217_, lean_object* v_a_3218_){
_start:
{
lean_object* v___x_3220_; 
v___x_3220_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_c_3213_, v_a_3214_, v_a_3215_, v_a_3216_, v_a_3217_, v_a_3218_);
return v___x_3220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode___boxed(lean_object* v_00_u03b1_3221_, lean_object* v_c_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_, lean_object* v_a_3227_, lean_object* v_a_3228_){
_start:
{
lean_object* v_res_3229_; 
v_res_3229_ = l_Lean_Meta_LazyDiscrTree_evalNode(v_00_u03b1_3221_, v_c_3222_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_);
lean_dec(v_a_3227_);
lean_dec_ref(v_a_3226_);
lean_dec(v_a_3225_);
lean_dec_ref(v_a_3224_);
lean_dec(v_a_3223_);
lean_dec(v_c_3222_);
return v_res_3229_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(lean_object* v_a_3230_, lean_object* v_fallback_3231_, lean_object* v_x_3232_){
_start:
{
if (lean_obj_tag(v_x_3232_) == 0)
{
lean_inc(v_fallback_3231_);
return v_fallback_3231_;
}
else
{
lean_object* v_key_3233_; lean_object* v_value_3234_; lean_object* v_tail_3235_; uint8_t v___x_3236_; 
v_key_3233_ = lean_ctor_get(v_x_3232_, 0);
v_value_3234_ = lean_ctor_get(v_x_3232_, 1);
v_tail_3235_ = lean_ctor_get(v_x_3232_, 2);
v___x_3236_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_3233_, v_a_3230_);
if (v___x_3236_ == 0)
{
v_x_3232_ = v_tail_3235_;
goto _start;
}
else
{
lean_inc(v_value_3234_);
return v_value_3234_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg___boxed(lean_object* v_a_3238_, lean_object* v_fallback_3239_, lean_object* v_x_3240_){
_start:
{
lean_object* v_res_3241_; 
v_res_3241_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(v_a_3238_, v_fallback_3239_, v_x_3240_);
lean_dec(v_x_3240_);
lean_dec(v_fallback_3239_);
lean_dec(v_a_3238_);
return v_res_3241_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(lean_object* v_m_3242_, lean_object* v_a_3243_, lean_object* v_fallback_3244_){
_start:
{
lean_object* v_buckets_3245_; lean_object* v___x_3246_; uint64_t v___x_3247_; uint64_t v___x_3248_; uint64_t v___x_3249_; uint64_t v_fold_3250_; uint64_t v___x_3251_; uint64_t v___x_3252_; uint64_t v___x_3253_; size_t v___x_3254_; size_t v___x_3255_; size_t v___x_3256_; size_t v___x_3257_; size_t v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; 
v_buckets_3245_ = lean_ctor_get(v_m_3242_, 1);
v___x_3246_ = lean_array_get_size(v_buckets_3245_);
v___x_3247_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_a_3243_);
v___x_3248_ = 32ULL;
v___x_3249_ = lean_uint64_shift_right(v___x_3247_, v___x_3248_);
v_fold_3250_ = lean_uint64_xor(v___x_3247_, v___x_3249_);
v___x_3251_ = 16ULL;
v___x_3252_ = lean_uint64_shift_right(v_fold_3250_, v___x_3251_);
v___x_3253_ = lean_uint64_xor(v_fold_3250_, v___x_3252_);
v___x_3254_ = lean_uint64_to_usize(v___x_3253_);
v___x_3255_ = lean_usize_of_nat(v___x_3246_);
v___x_3256_ = ((size_t)1ULL);
v___x_3257_ = lean_usize_sub(v___x_3255_, v___x_3256_);
v___x_3258_ = lean_usize_land(v___x_3254_, v___x_3257_);
v___x_3259_ = lean_array_uget_borrowed(v_buckets_3245_, v___x_3258_);
v___x_3260_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(v_a_3243_, v_fallback_3244_, v___x_3259_);
return v___x_3260_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg___boxed(lean_object* v_m_3261_, lean_object* v_a_3262_, lean_object* v_fallback_3263_){
_start:
{
lean_object* v_res_3264_; 
v_res_3264_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_m_3261_, v_a_3262_, v_fallback_3263_);
lean_dec(v_fallback_3263_);
lean_dec(v_a_3262_);
lean_dec_ref(v_m_3261_);
return v_res_3264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg(lean_object* v_next_3265_, lean_object* v_rest_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_, lean_object* v_a_3271_){
_start:
{
lean_object* v___x_3273_; uint8_t v___x_3274_; 
v___x_3273_ = lean_unsigned_to_nat(0u);
v___x_3274_ = lean_nat_dec_eq(v_next_3265_, v___x_3273_);
if (v___x_3274_ == 0)
{
lean_object* v___x_3275_; 
v___x_3275_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_next_3265_, v_a_3267_, v_a_3268_, v_a_3269_, v_a_3270_, v_a_3271_);
if (lean_obj_tag(v___x_3275_) == 0)
{
lean_object* v_a_3276_; lean_object* v___x_3278_; uint8_t v_isShared_3279_; uint8_t v_isSharedCheck_3301_; 
v_a_3276_ = lean_ctor_get(v___x_3275_, 0);
v_isSharedCheck_3301_ = !lean_is_exclusive(v___x_3275_);
if (v_isSharedCheck_3301_ == 0)
{
v___x_3278_ = v___x_3275_;
v_isShared_3279_ = v_isSharedCheck_3301_;
goto v_resetjp_3277_;
}
else
{
lean_inc(v_a_3276_);
lean_dec(v___x_3275_);
v___x_3278_ = lean_box(0);
v_isShared_3279_ = v_isSharedCheck_3301_;
goto v_resetjp_3277_;
}
v_resetjp_3277_:
{
lean_object* v_snd_3280_; 
v_snd_3280_ = lean_ctor_get(v_a_3276_, 1);
lean_inc(v_snd_3280_);
lean_dec(v_a_3276_);
if (lean_obj_tag(v_rest_3266_) == 0)
{
lean_object* v_fst_3281_; lean_object* v_snd_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3290_; 
v_fst_3281_ = lean_ctor_get(v_snd_3280_, 0);
lean_inc(v_fst_3281_);
v_snd_3282_ = lean_ctor_get(v_snd_3280_, 1);
lean_inc(v_snd_3282_);
lean_dec(v_snd_3280_);
v___x_3283_ = lean_st_ref_take(v_a_3267_);
v___x_3284_ = lean_box(0);
v___x_3285_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___x_3286_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3286_, 0, v___x_3285_);
lean_ctor_set(v___x_3286_, 1, v_fst_3281_);
lean_ctor_set(v___x_3286_, 2, v_snd_3282_);
lean_ctor_set(v___x_3286_, 3, v___x_3285_);
v___x_3287_ = lean_array_set(v___x_3283_, v_next_3265_, v___x_3286_);
lean_dec(v_next_3265_);
v___x_3288_ = lean_st_ref_put(v_a_3267_, v___x_3287_);
if (v_isShared_3279_ == 0)
{
lean_ctor_set(v___x_3278_, 0, v___x_3284_);
v___x_3290_ = v___x_3278_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3291_; 
v_reuseFailAlloc_3291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3291_, 0, v___x_3284_);
v___x_3290_ = v_reuseFailAlloc_3291_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
return v___x_3290_;
}
}
else
{
lean_object* v_fst_3292_; lean_object* v_snd_3293_; lean_object* v_head_3294_; lean_object* v_tail_3295_; lean_object* v___x_3296_; uint8_t v___x_3297_; 
lean_del_object(v___x_3278_);
lean_dec(v_next_3265_);
v_fst_3292_ = lean_ctor_get(v_snd_3280_, 0);
lean_inc(v_fst_3292_);
v_snd_3293_ = lean_ctor_get(v_snd_3280_, 1);
lean_inc(v_snd_3293_);
lean_dec(v_snd_3280_);
v_head_3294_ = lean_ctor_get(v_rest_3266_, 0);
v_tail_3295_ = lean_ctor_get(v_rest_3266_, 1);
v___x_3296_ = lean_box(3);
v___x_3297_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_head_3294_, v___x_3296_);
if (v___x_3297_ == 0)
{
lean_object* v___x_3298_; 
lean_dec(v_fst_3292_);
v___x_3298_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_snd_3293_, v_head_3294_, v___x_3273_);
lean_dec(v_snd_3293_);
v_next_3265_ = v___x_3298_;
v_rest_3266_ = v_tail_3295_;
goto _start;
}
else
{
lean_dec(v_snd_3293_);
v_next_3265_ = v_fst_3292_;
v_rest_3266_ = v_tail_3295_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3309_; 
lean_dec(v_next_3265_);
v_a_3302_ = lean_ctor_get(v___x_3275_, 0);
v_isSharedCheck_3309_ = !lean_is_exclusive(v___x_3275_);
if (v_isSharedCheck_3309_ == 0)
{
v___x_3304_ = v___x_3275_;
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_a_3302_);
lean_dec(v___x_3275_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v___x_3307_; 
if (v_isShared_3305_ == 0)
{
v___x_3307_ = v___x_3304_;
goto v_reusejp_3306_;
}
else
{
lean_object* v_reuseFailAlloc_3308_; 
v_reuseFailAlloc_3308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3308_, 0, v_a_3302_);
v___x_3307_ = v_reuseFailAlloc_3308_;
goto v_reusejp_3306_;
}
v_reusejp_3306_:
{
return v___x_3307_;
}
}
}
}
else
{
lean_object* v___x_3310_; lean_object* v___x_3311_; 
lean_dec(v_next_3265_);
v___x_3310_ = lean_box(0);
v___x_3311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3311_, 0, v___x_3310_);
return v___x_3311_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg___boxed(lean_object* v_next_3312_, lean_object* v_rest_3313_, lean_object* v_a_3314_, lean_object* v_a_3315_, lean_object* v_a_3316_, lean_object* v_a_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_){
_start:
{
lean_object* v_res_3320_; 
v_res_3320_ = l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg(v_next_3312_, v_rest_3313_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
lean_dec(v_a_3318_);
lean_dec_ref(v_a_3317_);
lean_dec(v_a_3316_);
lean_dec_ref(v_a_3315_);
lean_dec(v_a_3314_);
lean_dec(v_rest_3313_);
return v_res_3320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux(lean_object* v_00_u03b1_3321_, lean_object* v_next_3322_, lean_object* v_rest_3323_, lean_object* v_a_3324_, lean_object* v_a_3325_, lean_object* v_a_3326_, lean_object* v_a_3327_, lean_object* v_a_3328_){
_start:
{
lean_object* v___x_3330_; 
v___x_3330_ = l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg(v_next_3322_, v_rest_3323_, v_a_3324_, v_a_3325_, v_a_3326_, v_a_3327_, v_a_3328_);
return v___x_3330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux___boxed(lean_object* v_00_u03b1_3331_, lean_object* v_next_3332_, lean_object* v_rest_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_){
_start:
{
lean_object* v_res_3340_; 
v_res_3340_ = l_Lean_Meta_LazyDiscrTree_dropKeyAux(v_00_u03b1_3331_, v_next_3332_, v_rest_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_);
lean_dec(v_a_3338_);
lean_dec_ref(v_a_3337_);
lean_dec(v_a_3336_);
lean_dec_ref(v_a_3335_);
lean_dec(v_a_3334_);
lean_dec(v_rest_3333_);
return v_res_3340_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0(lean_object* v_00_u03b2_3341_, lean_object* v_m_3342_, lean_object* v_a_3343_, lean_object* v_fallback_3344_){
_start:
{
lean_object* v___x_3345_; 
v___x_3345_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_m_3342_, v_a_3343_, v_fallback_3344_);
return v___x_3345_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___boxed(lean_object* v_00_u03b2_3346_, lean_object* v_m_3347_, lean_object* v_a_3348_, lean_object* v_fallback_3349_){
_start:
{
lean_object* v_res_3350_; 
v_res_3350_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0(v_00_u03b2_3346_, v_m_3347_, v_a_3348_, v_fallback_3349_);
lean_dec(v_fallback_3349_);
lean_dec(v_a_3348_);
lean_dec_ref(v_m_3347_);
return v_res_3350_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0(lean_object* v_00_u03b2_3351_, lean_object* v_a_3352_, lean_object* v_fallback_3353_, lean_object* v_x_3354_){
_start:
{
lean_object* v___x_3355_; 
v___x_3355_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(v_a_3352_, v_fallback_3353_, v_x_3354_);
return v___x_3355_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3356_, lean_object* v_a_3357_, lean_object* v_fallback_3358_, lean_object* v_x_3359_){
_start:
{
lean_object* v_res_3360_; 
v_res_3360_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0(v_00_u03b2_3356_, v_a_3357_, v_fallback_3358_, v_x_3359_);
lean_dec(v_x_3359_);
lean_dec(v_fallback_3358_);
lean_dec(v_a_3357_);
return v_res_3360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey___redArg(lean_object* v_t_3361_, lean_object* v_path_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_){
_start:
{
if (lean_obj_tag(v_path_3362_) == 0)
{
lean_object* v___x_3368_; 
v___x_3368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3368_, 0, v_t_3361_);
return v___x_3368_;
}
else
{
lean_object* v_head_3369_; lean_object* v_tail_3370_; lean_object* v_roots_3371_; lean_object* v___x_3372_; lean_object* v_idx_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; 
v_head_3369_ = lean_ctor_get(v_path_3362_, 0);
lean_inc(v_head_3369_);
v_tail_3370_ = lean_ctor_get(v_path_3362_, 1);
lean_inc(v_tail_3370_);
lean_dec_ref_known(v_path_3362_, 2);
v_roots_3371_ = lean_ctor_get(v_t_3361_, 1);
v___x_3372_ = lean_unsigned_to_nat(0u);
v_idx_3373_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_roots_3371_, v_head_3369_, v___x_3372_);
lean_dec(v_head_3369_);
v___x_3374_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_dropKeyAux___boxed), 9, 3);
lean_closure_set(v___x_3374_, 0, lean_box(0));
lean_closure_set(v___x_3374_, 1, v_idx_3373_);
lean_closure_set(v___x_3374_, 2, v_tail_3370_);
v___x_3375_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_t_3361_, v___x_3374_, v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_);
if (lean_obj_tag(v___x_3375_) == 0)
{
lean_object* v_a_3376_; lean_object* v___x_3378_; uint8_t v_isShared_3379_; uint8_t v_isSharedCheck_3384_; 
v_a_3376_ = lean_ctor_get(v___x_3375_, 0);
v_isSharedCheck_3384_ = !lean_is_exclusive(v___x_3375_);
if (v_isSharedCheck_3384_ == 0)
{
v___x_3378_ = v___x_3375_;
v_isShared_3379_ = v_isSharedCheck_3384_;
goto v_resetjp_3377_;
}
else
{
lean_inc(v_a_3376_);
lean_dec(v___x_3375_);
v___x_3378_ = lean_box(0);
v_isShared_3379_ = v_isSharedCheck_3384_;
goto v_resetjp_3377_;
}
v_resetjp_3377_:
{
lean_object* v_snd_3380_; lean_object* v___x_3382_; 
v_snd_3380_ = lean_ctor_get(v_a_3376_, 1);
lean_inc(v_snd_3380_);
lean_dec(v_a_3376_);
if (v_isShared_3379_ == 0)
{
lean_ctor_set(v___x_3378_, 0, v_snd_3380_);
v___x_3382_ = v___x_3378_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v_snd_3380_);
v___x_3382_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
return v___x_3382_;
}
}
}
else
{
lean_object* v_a_3385_; lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3392_; 
v_a_3385_ = lean_ctor_get(v___x_3375_, 0);
v_isSharedCheck_3392_ = !lean_is_exclusive(v___x_3375_);
if (v_isSharedCheck_3392_ == 0)
{
v___x_3387_ = v___x_3375_;
v_isShared_3388_ = v_isSharedCheck_3392_;
goto v_resetjp_3386_;
}
else
{
lean_inc(v_a_3385_);
lean_dec(v___x_3375_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3392_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
lean_object* v___x_3390_; 
if (v_isShared_3388_ == 0)
{
v___x_3390_ = v___x_3387_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3391_; 
v_reuseFailAlloc_3391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3391_, 0, v_a_3385_);
v___x_3390_ = v_reuseFailAlloc_3391_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
return v___x_3390_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey___redArg___boxed(lean_object* v_t_3393_, lean_object* v_path_3394_, lean_object* v_a_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_){
_start:
{
lean_object* v_res_3400_; 
v_res_3400_ = l_Lean_Meta_LazyDiscrTree_dropKey___redArg(v_t_3393_, v_path_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_);
lean_dec(v_a_3398_);
lean_dec_ref(v_a_3397_);
lean_dec(v_a_3396_);
lean_dec_ref(v_a_3395_);
return v_res_3400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey(lean_object* v_00_u03b1_3401_, lean_object* v_t_3402_, lean_object* v_path_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_){
_start:
{
lean_object* v___x_3409_; 
v___x_3409_ = l_Lean_Meta_LazyDiscrTree_dropKey___redArg(v_t_3402_, v_path_3403_, v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_);
return v___x_3409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey___boxed(lean_object* v_00_u03b1_3410_, lean_object* v_t_3411_, lean_object* v_path_3412_, lean_object* v_a_3413_, lean_object* v_a_3414_, lean_object* v_a_3415_, lean_object* v_a_3416_, lean_object* v_a_3417_){
_start:
{
lean_object* v_res_3418_; 
v_res_3418_ = l_Lean_Meta_LazyDiscrTree_dropKey(v_00_u03b1_3410_, v_t_3411_, v_path_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_);
lean_dec(v_a_3416_);
lean_dec_ref(v_a_3415_);
lean_dec(v_a_3414_);
lean_dec_ref(v_a_3413_);
return v_res_3418_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(lean_object* v_score_3421_, lean_object* v_e_3422_, lean_object* v_a_3423_){
_start:
{
lean_object* v___x_3424_; uint8_t v___x_3425_; 
v___x_3424_ = lean_array_get_size(v_a_3423_);
v___x_3425_ = lean_nat_dec_lt(v___x_3424_, v_score_3421_);
if (v___x_3425_ == 0)
{
lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; 
v___x_3426_ = lean_unsigned_to_nat(1u);
v___x_3427_ = lean_mk_empty_array_with_capacity(v___x_3426_);
v___x_3428_ = lean_array_push(v___x_3427_, v_e_3422_);
v___x_3429_ = lean_array_push(v_a_3423_, v___x_3428_);
return v___x_3429_;
}
else
{
lean_object* v___x_3430_; lean_object* v___x_3431_; 
v___x_3430_ = ((lean_object*)(l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg___closed__0));
v___x_3431_ = lean_array_push(v_a_3423_, v___x_3430_);
v_a_3423_ = v___x_3431_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg___boxed(lean_object* v_score_3433_, lean_object* v_e_3434_, lean_object* v_a_3435_){
_start:
{
lean_object* v_res_3436_; 
v_res_3436_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(v_score_3433_, v_e_3434_, v_a_3435_);
lean_dec(v_score_3433_);
return v_res_3436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop(lean_object* v_00_u03b1_3437_, lean_object* v_score_3438_, lean_object* v_e_3439_, lean_object* v_a_3440_){
_start:
{
lean_object* v___x_3441_; 
v___x_3441_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(v_score_3438_, v_e_3439_, v_a_3440_);
return v___x_3441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___boxed(lean_object* v_00_u03b1_3442_, lean_object* v_score_3443_, lean_object* v_e_3444_, lean_object* v_a_3445_){
_start:
{
lean_object* v_res_3446_; 
v_res_3446_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop(v_00_u03b1_3442_, v_score_3443_, v_e_3444_, v_a_3445_);
lean_dec(v_score_3443_);
return v_res_3446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(lean_object* v_r_3447_, lean_object* v_score_3448_, lean_object* v_e_3449_){
_start:
{
lean_object* v___x_3450_; lean_object* v___x_3451_; uint8_t v___x_3452_; 
v___x_3450_ = lean_array_get_size(v_e_3449_);
v___x_3451_ = lean_unsigned_to_nat(0u);
v___x_3452_ = lean_nat_dec_eq(v___x_3450_, v___x_3451_);
if (v___x_3452_ == 0)
{
lean_object* v___x_3453_; uint8_t v___x_3454_; 
v___x_3453_ = lean_array_get_size(v_r_3447_);
v___x_3454_ = lean_nat_dec_lt(v_score_3448_, v___x_3453_);
if (v___x_3454_ == 0)
{
lean_object* v___x_3455_; 
v___x_3455_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(v_score_3448_, v_e_3449_, v_r_3447_);
return v___x_3455_;
}
else
{
if (v___x_3454_ == 0)
{
lean_dec_ref(v_e_3449_);
return v_r_3447_;
}
else
{
lean_object* v_v_3456_; lean_object* v___x_3457_; lean_object* v_xs_x27_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; 
v_v_3456_ = lean_array_fget(v_r_3447_, v_score_3448_);
v___x_3457_ = lean_box(0);
v_xs_x27_3458_ = lean_array_fset(v_r_3447_, v_score_3448_, v___x_3457_);
v___x_3459_ = lean_array_push(v_v_3456_, v_e_3449_);
v___x_3460_ = lean_array_fset(v_xs_x27_3458_, v_score_3448_, v___x_3459_);
return v___x_3460_;
}
}
}
else
{
lean_dec_ref(v_e_3449_);
return v_r_3447_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg___boxed(lean_object* v_r_3461_, lean_object* v_score_3462_, lean_object* v_e_3463_){
_start:
{
lean_object* v_res_3464_; 
v_res_3464_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v_r_3461_, v_score_3462_, v_e_3463_);
lean_dec(v_score_3462_);
return v_res_3464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push(lean_object* v_00_u03b1_3465_, lean_object* v_r_3466_, lean_object* v_score_3467_, lean_object* v_e_3468_){
_start:
{
lean_object* v___x_3469_; 
v___x_3469_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v_r_3466_, v_score_3467_, v_e_3468_);
return v___x_3469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push___boxed(lean_object* v_00_u03b1_3470_, lean_object* v_r_3471_, lean_object* v_score_3472_, lean_object* v_e_3473_){
_start:
{
lean_object* v_res_3474_; 
v_res_3474_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push(v_00_u03b1_3470_, v_r_3471_, v_score_3472_, v_e_3473_);
lean_dec(v_score_3472_);
return v_res_3474_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(lean_object* v_as_3475_, size_t v_i_3476_, size_t v_stop_3477_, lean_object* v_b_3478_){
_start:
{
uint8_t v___x_3479_; 
v___x_3479_ = lean_usize_dec_eq(v_i_3476_, v_stop_3477_);
if (v___x_3479_ == 0)
{
lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; size_t v___x_3483_; size_t v___x_3484_; 
v___x_3480_ = lean_array_uget_borrowed(v_as_3475_, v_i_3476_);
v___x_3481_ = lean_array_get_size(v___x_3480_);
v___x_3482_ = lean_nat_add(v_b_3478_, v___x_3481_);
lean_dec(v_b_3478_);
v___x_3483_ = ((size_t)1ULL);
v___x_3484_ = lean_usize_add(v_i_3476_, v___x_3483_);
v_i_3476_ = v___x_3484_;
v_b_3478_ = v___x_3482_;
goto _start;
}
else
{
return v_b_3478_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg___boxed(lean_object* v_as_3486_, lean_object* v_i_3487_, lean_object* v_stop_3488_, lean_object* v_b_3489_){
_start:
{
size_t v_i_boxed_3490_; size_t v_stop_boxed_3491_; lean_object* v_res_3492_; 
v_i_boxed_3490_ = lean_unbox_usize(v_i_3487_);
lean_dec(v_i_3487_);
v_stop_boxed_3491_ = lean_unbox_usize(v_stop_3488_);
lean_dec(v_stop_3488_);
v_res_3492_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v_as_3486_, v_i_boxed_3490_, v_stop_boxed_3491_, v_b_3489_);
lean_dec_ref(v_as_3486_);
return v_res_3492_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(lean_object* v_as_3493_, size_t v_i_3494_, size_t v_stop_3495_, lean_object* v_b_3496_){
_start:
{
lean_object* v___y_3498_; uint8_t v___x_3502_; 
v___x_3502_ = lean_usize_dec_eq(v_i_3494_, v_stop_3495_);
if (v___x_3502_ == 0)
{
lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; uint8_t v___x_3506_; 
v___x_3503_ = lean_array_uget_borrowed(v_as_3493_, v_i_3494_);
v___x_3504_ = lean_unsigned_to_nat(0u);
v___x_3505_ = lean_array_get_size(v___x_3503_);
v___x_3506_ = lean_nat_dec_lt(v___x_3504_, v___x_3505_);
if (v___x_3506_ == 0)
{
v___y_3498_ = v_b_3496_;
goto v___jp_3497_;
}
else
{
uint8_t v___x_3507_; 
v___x_3507_ = lean_nat_dec_le(v___x_3505_, v___x_3505_);
if (v___x_3507_ == 0)
{
if (v___x_3506_ == 0)
{
v___y_3498_ = v_b_3496_;
goto v___jp_3497_;
}
else
{
size_t v___x_3508_; size_t v___x_3509_; lean_object* v___x_3510_; 
v___x_3508_ = ((size_t)0ULL);
v___x_3509_ = lean_usize_of_nat(v___x_3505_);
v___x_3510_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v___x_3503_, v___x_3508_, v___x_3509_, v_b_3496_);
v___y_3498_ = v___x_3510_;
goto v___jp_3497_;
}
}
else
{
size_t v___x_3511_; size_t v___x_3512_; lean_object* v___x_3513_; 
v___x_3511_ = ((size_t)0ULL);
v___x_3512_ = lean_usize_of_nat(v___x_3505_);
v___x_3513_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v___x_3503_, v___x_3511_, v___x_3512_, v_b_3496_);
v___y_3498_ = v___x_3513_;
goto v___jp_3497_;
}
}
}
else
{
return v_b_3496_;
}
v___jp_3497_:
{
size_t v___x_3499_; size_t v___x_3500_; 
v___x_3499_ = ((size_t)1ULL);
v___x_3500_ = lean_usize_add(v_i_3494_, v___x_3499_);
v_i_3494_ = v___x_3500_;
v_b_3496_ = v___y_3498_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg___boxed(lean_object* v_as_3514_, lean_object* v_i_3515_, lean_object* v_stop_3516_, lean_object* v_b_3517_){
_start:
{
size_t v_i_boxed_3518_; size_t v_stop_boxed_3519_; lean_object* v_res_3520_; 
v_i_boxed_3518_ = lean_unbox_usize(v_i_3515_);
lean_dec(v_i_3515_);
v_stop_boxed_3519_ = lean_unbox_usize(v_stop_3516_);
lean_dec(v_stop_3516_);
v_res_3520_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_as_3514_, v_i_boxed_3518_, v_stop_boxed_3519_, v_b_3517_);
lean_dec_ref(v_as_3514_);
return v_res_3520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(lean_object* v_mr_3521_){
_start:
{
lean_object* v___x_3522_; lean_object* v___x_3523_; uint8_t v___x_3524_; 
v___x_3522_ = lean_unsigned_to_nat(0u);
v___x_3523_ = lean_array_get_size(v_mr_3521_);
v___x_3524_ = lean_nat_dec_lt(v___x_3522_, v___x_3523_);
if (v___x_3524_ == 0)
{
return v___x_3522_;
}
else
{
uint8_t v___x_3525_; 
v___x_3525_ = lean_nat_dec_le(v___x_3523_, v___x_3523_);
if (v___x_3525_ == 0)
{
if (v___x_3524_ == 0)
{
return v___x_3522_;
}
else
{
size_t v___x_3526_; size_t v___x_3527_; lean_object* v___x_3528_; 
v___x_3526_ = ((size_t)0ULL);
v___x_3527_ = lean_usize_of_nat(v___x_3523_);
v___x_3528_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_mr_3521_, v___x_3526_, v___x_3527_, v___x_3522_);
return v___x_3528_;
}
}
else
{
size_t v___x_3529_; size_t v___x_3530_; lean_object* v___x_3531_; 
v___x_3529_ = ((size_t)0ULL);
v___x_3530_ = lean_usize_of_nat(v___x_3523_);
v___x_3531_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_mr_3521_, v___x_3529_, v___x_3530_, v___x_3522_);
return v___x_3531_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg___boxed(lean_object* v_mr_3532_){
_start:
{
lean_object* v_res_3533_; 
v_res_3533_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_mr_3532_);
lean_dec_ref(v_mr_3532_);
return v_res_3533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size(lean_object* v_00_u03b1_3534_, lean_object* v_mr_3535_){
_start:
{
lean_object* v___x_3536_; 
v___x_3536_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_mr_3535_);
return v___x_3536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size___boxed(lean_object* v_00_u03b1_3537_, lean_object* v_mr_3538_){
_start:
{
lean_object* v_res_3539_; 
v_res_3539_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size(v_00_u03b1_3537_, v_mr_3538_);
lean_dec_ref(v_mr_3538_);
return v_res_3539_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0(lean_object* v_00_u03b1_3540_, lean_object* v_as_3541_, size_t v_i_3542_, size_t v_stop_3543_, lean_object* v_b_3544_){
_start:
{
lean_object* v___x_3545_; 
v___x_3545_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v_as_3541_, v_i_3542_, v_stop_3543_, v_b_3544_);
return v___x_3545_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___boxed(lean_object* v_00_u03b1_3546_, lean_object* v_as_3547_, lean_object* v_i_3548_, lean_object* v_stop_3549_, lean_object* v_b_3550_){
_start:
{
size_t v_i_boxed_3551_; size_t v_stop_boxed_3552_; lean_object* v_res_3553_; 
v_i_boxed_3551_ = lean_unbox_usize(v_i_3548_);
lean_dec(v_i_3548_);
v_stop_boxed_3552_ = lean_unbox_usize(v_stop_3549_);
lean_dec(v_stop_3549_);
v_res_3553_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0(v_00_u03b1_3546_, v_as_3547_, v_i_boxed_3551_, v_stop_boxed_3552_, v_b_3550_);
lean_dec_ref(v_as_3547_);
return v_res_3553_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1(lean_object* v_00_u03b1_3554_, lean_object* v_as_3555_, size_t v_i_3556_, size_t v_stop_3557_, lean_object* v_b_3558_){
_start:
{
lean_object* v___x_3559_; 
v___x_3559_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_as_3555_, v_i_3556_, v_stop_3557_, v_b_3558_);
return v___x_3559_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___boxed(lean_object* v_00_u03b1_3560_, lean_object* v_as_3561_, lean_object* v_i_3562_, lean_object* v_stop_3563_, lean_object* v_b_3564_){
_start:
{
size_t v_i_boxed_3565_; size_t v_stop_boxed_3566_; lean_object* v_res_3567_; 
v_i_boxed_3565_ = lean_unbox_usize(v_i_3562_);
lean_dec(v_i_3562_);
v_stop_boxed_3566_ = lean_unbox_usize(v_stop_3563_);
lean_dec(v_stop_3563_);
v_res_3567_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1(v_00_u03b1_3560_, v_as_3561_, v_i_boxed_3565_, v_stop_boxed_3566_, v_b_3564_);
lean_dec_ref(v_as_3561_);
return v_res_3567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__0(lean_object* v_f_3568_, lean_object* v_j_3569_, lean_object* v_x_3570_){
_start:
{
lean_object* v___x_3571_; 
v___x_3571_ = lean_apply_2(v_f_3568_, v_j_3569_, v_x_3570_);
return v___x_3571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1(lean_object* v___f_3591_, lean_object* v_x1_3592_, lean_object* v_x2_3593_){
_start:
{
lean_object* v___x_3594_; size_t v_sz_3595_; size_t v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; 
v___x_3594_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__9));
v_sz_3595_ = lean_array_size(v_x2_3593_);
v___x_3596_ = ((size_t)0ULL);
v___x_3597_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3594_, v___f_3591_, v_sz_3595_, v___x_3596_, v_x2_3593_);
v___x_3598_ = l_Array_append___redArg(v_x1_3592_, v___x_3597_);
lean_dec(v___x_3597_);
return v___x_3598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2(lean_object* v_n_3599_, lean_object* v_mr_3600_, lean_object* v_f_3601_, lean_object* v_i_3602_, lean_object* v_x_3603_, lean_object* v_r_3604_){
_start:
{
lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v_j_3607_; lean_object* v_b_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; uint8_t v___x_3612_; 
v___x_3605_ = lean_unsigned_to_nat(1u);
v___x_3606_ = lean_nat_sub(v_n_3599_, v___x_3605_);
v_j_3607_ = lean_nat_sub(v___x_3606_, v_i_3602_);
lean_dec(v___x_3606_);
v_b_3608_ = lean_array_fget_borrowed(v_mr_3600_, v_j_3607_);
v___x_3609_ = lean_unsigned_to_nat(0u);
v___x_3610_ = lean_array_get_size(v_b_3608_);
v___x_3611_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__9));
v___x_3612_ = lean_nat_dec_lt(v___x_3609_, v___x_3610_);
if (v___x_3612_ == 0)
{
lean_dec(v_j_3607_);
lean_dec(v_f_3601_);
return v_r_3604_;
}
else
{
lean_object* v___f_3613_; lean_object* v___f_3614_; uint8_t v___x_3615_; 
v___f_3613_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3613_, 0, v_f_3601_);
lean_closure_set(v___f_3613_, 1, v_j_3607_);
v___f_3614_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1), 3, 1);
lean_closure_set(v___f_3614_, 0, v___f_3613_);
v___x_3615_ = lean_nat_dec_le(v___x_3610_, v___x_3610_);
if (v___x_3615_ == 0)
{
if (v___x_3612_ == 0)
{
lean_dec_ref(v___f_3614_);
return v_r_3604_;
}
else
{
size_t v___x_3616_; size_t v___x_3617_; lean_object* v___x_3618_; 
v___x_3616_ = ((size_t)0ULL);
v___x_3617_ = lean_usize_of_nat(v___x_3610_);
lean_inc(v_b_3608_);
v___x_3618_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3611_, v___f_3614_, v_b_3608_, v___x_3616_, v___x_3617_, v_r_3604_);
return v___x_3618_;
}
}
else
{
size_t v___x_3619_; size_t v___x_3620_; lean_object* v___x_3621_; 
v___x_3619_ = ((size_t)0ULL);
v___x_3620_ = lean_usize_of_nat(v___x_3610_);
lean_inc(v_b_3608_);
v___x_3621_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3611_, v___f_3614_, v_b_3608_, v___x_3619_, v___x_3620_, v_r_3604_);
return v___x_3621_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2___boxed(lean_object* v_n_3622_, lean_object* v_mr_3623_, lean_object* v_f_3624_, lean_object* v_i_3625_, lean_object* v_x_3626_, lean_object* v_r_3627_){
_start:
{
lean_object* v_res_3628_; 
v_res_3628_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2(v_n_3622_, v_mr_3623_, v_f_3624_, v_i_3625_, v_x_3626_, v_r_3627_);
lean_dec(v_i_3625_);
lean_dec_ref(v_mr_3623_);
lean_dec(v_n_3622_);
return v_res_3628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg(lean_object* v_mr_3629_, lean_object* v_a_3630_, lean_object* v_f_3631_){
_start:
{
lean_object* v_n_3632_; lean_object* v___f_3633_; lean_object* v___x_3634_; 
v_n_3632_ = lean_array_get_size(v_mr_3629_);
v___f_3633_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_3633_, 0, v_n_3632_);
lean_closure_set(v___f_3633_, 1, v_mr_3629_);
lean_closure_set(v___f_3633_, 2, v_f_3631_);
v___x_3634_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop(lean_box(0), v_n_3632_, v___f_3633_, v_n_3632_, lean_box(0), v_a_3630_);
return v___x_3634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux(lean_object* v_00_u03b1_3635_, lean_object* v_00_u03b2_3636_, lean_object* v_mr_3637_, lean_object* v_a_3638_, lean_object* v_f_3639_){
_start:
{
lean_object* v___x_3640_; 
v___x_3640_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg(v_mr_3637_, v_a_3638_, v_f_3639_);
return v___x_3640_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(size_t v_sz_3641_, size_t v_i_3642_, lean_object* v_bs_3643_){
_start:
{
uint8_t v___x_3644_; 
v___x_3644_ = lean_usize_dec_lt(v_i_3642_, v_sz_3641_);
if (v___x_3644_ == 0)
{
return v_bs_3643_;
}
else
{
lean_object* v_v_3645_; lean_object* v___x_3646_; lean_object* v_bs_x27_3647_; size_t v___x_3648_; size_t v___x_3649_; lean_object* v___x_3650_; 
v_v_3645_ = lean_array_uget(v_bs_3643_, v_i_3642_);
v___x_3646_ = lean_unsigned_to_nat(0u);
v_bs_x27_3647_ = lean_array_uset(v_bs_3643_, v_i_3642_, v___x_3646_);
v___x_3648_ = ((size_t)1ULL);
v___x_3649_ = lean_usize_add(v_i_3642_, v___x_3648_);
v___x_3650_ = lean_array_uset(v_bs_x27_3647_, v_i_3642_, v_v_3645_);
v_i_3642_ = v___x_3649_;
v_bs_3643_ = v___x_3650_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg___boxed(lean_object* v_sz_3652_, lean_object* v_i_3653_, lean_object* v_bs_3654_){
_start:
{
size_t v_sz_boxed_3655_; size_t v_i_boxed_3656_; lean_object* v_res_3657_; 
v_sz_boxed_3655_ = lean_unbox_usize(v_sz_3652_);
lean_dec(v_sz_3652_);
v_i_boxed_3656_ = lean_unbox_usize(v_i_3653_);
lean_dec(v_i_3653_);
v_res_3657_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(v_sz_boxed_3655_, v_i_boxed_3656_, v_bs_3654_);
return v_res_3657_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(lean_object* v_as_3658_, size_t v_i_3659_, size_t v_stop_3660_, lean_object* v_b_3661_){
_start:
{
uint8_t v___x_3662_; 
v___x_3662_ = lean_usize_dec_eq(v_i_3659_, v_stop_3660_);
if (v___x_3662_ == 0)
{
lean_object* v___x_3663_; size_t v_sz_3664_; size_t v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; size_t v___x_3668_; size_t v___x_3669_; 
v___x_3663_ = lean_array_uget_borrowed(v_as_3658_, v_i_3659_);
v_sz_3664_ = lean_array_size(v___x_3663_);
v___x_3665_ = ((size_t)0ULL);
lean_inc(v___x_3663_);
v___x_3666_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(v_sz_3664_, v___x_3665_, v___x_3663_);
v___x_3667_ = l_Array_append___redArg(v_b_3661_, v___x_3666_);
lean_dec_ref(v___x_3666_);
v___x_3668_ = ((size_t)1ULL);
v___x_3669_ = lean_usize_add(v_i_3659_, v___x_3668_);
v_i_3659_ = v___x_3669_;
v_b_3661_ = v___x_3667_;
goto _start;
}
else
{
return v_b_3661_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg___boxed(lean_object* v_as_3671_, lean_object* v_i_3672_, lean_object* v_stop_3673_, lean_object* v_b_3674_){
_start:
{
size_t v_i_boxed_3675_; size_t v_stop_boxed_3676_; lean_object* v_res_3677_; 
v_i_boxed_3675_ = lean_unbox_usize(v_i_3672_);
lean_dec(v_i_3672_);
v_stop_boxed_3676_ = lean_unbox_usize(v_stop_3673_);
lean_dec(v_stop_3673_);
v_res_3677_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(v_as_3671_, v_i_boxed_3675_, v_stop_boxed_3676_, v_b_3674_);
lean_dec_ref(v_as_3671_);
return v_res_3677_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(lean_object* v_n_3678_, lean_object* v_aa_3679_, lean_object* v_n_3680_, lean_object* v_j_3681_, lean_object* v_a_3682_){
_start:
{
lean_object* v_zero_3683_; uint8_t v_isZero_3684_; 
v_zero_3683_ = lean_unsigned_to_nat(0u);
v_isZero_3684_ = lean_nat_dec_eq(v_j_3681_, v_zero_3683_);
if (v_isZero_3684_ == 1)
{
lean_dec(v_j_3681_);
return v_a_3682_;
}
else
{
lean_object* v_one_3685_; lean_object* v_n_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v_j_3689_; lean_object* v_b_3690_; lean_object* v___x_3691_; uint8_t v___x_3692_; 
v_one_3685_ = lean_unsigned_to_nat(1u);
v_n_3686_ = lean_nat_sub(v_j_3681_, v_one_3685_);
v___x_3687_ = lean_nat_sub(v_n_3680_, v_j_3681_);
lean_dec(v_j_3681_);
v___x_3688_ = lean_nat_sub(v_n_3678_, v_one_3685_);
v_j_3689_ = lean_nat_sub(v___x_3688_, v___x_3687_);
lean_dec(v___x_3687_);
lean_dec(v___x_3688_);
v_b_3690_ = lean_array_fget_borrowed(v_aa_3679_, v_j_3689_);
lean_dec(v_j_3689_);
v___x_3691_ = lean_array_get_size(v_b_3690_);
v___x_3692_ = lean_nat_dec_lt(v_zero_3683_, v___x_3691_);
if (v___x_3692_ == 0)
{
v_j_3681_ = v_n_3686_;
goto _start;
}
else
{
size_t v___x_3694_; size_t v___x_3695_; lean_object* v___x_3696_; 
v___x_3694_ = ((size_t)0ULL);
v___x_3695_ = lean_usize_of_nat(v___x_3691_);
v___x_3696_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(v_b_3690_, v___x_3694_, v___x_3695_, v_a_3682_);
v_j_3681_ = v_n_3686_;
v_a_3682_ = v___x_3696_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg___boxed(lean_object* v_n_3698_, lean_object* v_aa_3699_, lean_object* v_n_3700_, lean_object* v_j_3701_, lean_object* v_a_3702_){
_start:
{
lean_object* v_res_3703_; 
v_res_3703_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(v_n_3698_, v_aa_3699_, v_n_3700_, v_j_3701_, v_a_3702_);
lean_dec(v_n_3700_);
lean_dec_ref(v_aa_3699_);
lean_dec(v_n_3698_);
return v_res_3703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(lean_object* v_mr_3704_, lean_object* v_a_3705_){
_start:
{
lean_object* v_n_3706_; lean_object* v___x_3707_; 
v_n_3706_ = lean_array_get_size(v_mr_3704_);
v___x_3707_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(v_n_3706_, v_mr_3704_, v_n_3706_, v_n_3706_, v_a_3705_);
return v___x_3707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg___boxed(lean_object* v_mr_3708_, lean_object* v_a_3709_){
_start:
{
lean_object* v_res_3710_; 
v_res_3710_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3708_, v_a_3709_);
lean_dec_ref(v_mr_3708_);
return v_res_3710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___redArg(lean_object* v_mr_3711_, lean_object* v_a_3712_){
_start:
{
lean_object* v___x_3713_; 
v___x_3713_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3711_, v_a_3712_);
return v___x_3713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___redArg___boxed(lean_object* v_mr_3714_, lean_object* v_a_3715_){
_start:
{
lean_object* v_res_3716_; 
v_res_3716_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___redArg(v_mr_3714_, v_a_3715_);
lean_dec_ref(v_mr_3714_);
return v_res_3716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults(lean_object* v_00_u03b1_3717_, lean_object* v_mr_3718_, lean_object* v_a_3719_){
_start:
{
lean_object* v___x_3720_; 
v___x_3720_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3718_, v_a_3719_);
return v___x_3720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___boxed(lean_object* v_00_u03b1_3721_, lean_object* v_mr_3722_, lean_object* v_a_3723_){
_start:
{
lean_object* v_res_3724_; 
v_res_3724_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults(v_00_u03b1_3721_, v_mr_3722_, v_a_3723_);
lean_dec_ref(v_mr_3722_);
return v_res_3724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0(lean_object* v_00_u03b1_3725_, lean_object* v_mr_3726_, lean_object* v_a_3727_){
_start:
{
lean_object* v___x_3728_; 
v___x_3728_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3726_, v_a_3727_);
return v___x_3728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___boxed(lean_object* v_00_u03b1_3729_, lean_object* v_mr_3730_, lean_object* v_a_3731_){
_start:
{
lean_object* v_res_3732_; 
v_res_3732_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0(v_00_u03b1_3729_, v_mr_3730_, v_a_3731_);
lean_dec_ref(v_mr_3730_);
return v_res_3732_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0(lean_object* v_00_u03b1_3733_, size_t v_sz_3734_, size_t v_i_3735_, lean_object* v_bs_3736_){
_start:
{
lean_object* v___x_3737_; 
v___x_3737_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(v_sz_3734_, v_i_3735_, v_bs_3736_);
return v___x_3737_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3738_, lean_object* v_sz_3739_, lean_object* v_i_3740_, lean_object* v_bs_3741_){
_start:
{
size_t v_sz_boxed_3742_; size_t v_i_boxed_3743_; lean_object* v_res_3744_; 
v_sz_boxed_3742_ = lean_unbox_usize(v_sz_3739_);
lean_dec(v_sz_3739_);
v_i_boxed_3743_ = lean_unbox_usize(v_i_3740_);
lean_dec(v_i_3740_);
v_res_3744_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0(v_00_u03b1_3738_, v_sz_boxed_3742_, v_i_boxed_3743_, v_bs_3741_);
return v_res_3744_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1(lean_object* v_00_u03b1_3745_, lean_object* v_as_3746_, size_t v_i_3747_, size_t v_stop_3748_, lean_object* v_b_3749_){
_start:
{
lean_object* v___x_3750_; 
v___x_3750_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(v_as_3746_, v_i_3747_, v_stop_3748_, v_b_3749_);
return v___x_3750_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3751_, lean_object* v_as_3752_, lean_object* v_i_3753_, lean_object* v_stop_3754_, lean_object* v_b_3755_){
_start:
{
size_t v_i_boxed_3756_; size_t v_stop_boxed_3757_; lean_object* v_res_3758_; 
v_i_boxed_3756_ = lean_unbox_usize(v_i_3753_);
lean_dec(v_i_3753_);
v_stop_boxed_3757_ = lean_unbox_usize(v_stop_3754_);
lean_dec(v_stop_3754_);
v_res_3758_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1(v_00_u03b1_3751_, v_as_3752_, v_i_boxed_3756_, v_stop_boxed_3757_, v_b_3755_);
lean_dec_ref(v_as_3752_);
return v_res_3758_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2(lean_object* v_00_u03b1_3759_, lean_object* v_n_3760_, lean_object* v_aa_3761_, lean_object* v_n_3762_, lean_object* v_j_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_){
_start:
{
lean_object* v___x_3766_; 
v___x_3766_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(v_n_3760_, v_aa_3761_, v_n_3762_, v_j_3763_, v_a_3765_);
return v___x_3766_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___boxed(lean_object* v_00_u03b1_3767_, lean_object* v_n_3768_, lean_object* v_aa_3769_, lean_object* v_n_3770_, lean_object* v_j_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_){
_start:
{
lean_object* v_res_3774_; 
v_res_3774_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2(v_00_u03b1_3767_, v_n_3768_, v_aa_3769_, v_n_3770_, v_j_3771_, v_a_3772_, v_a_3773_);
lean_dec(v_n_3770_);
lean_dec_ref(v_aa_3769_);
lean_dec(v_n_3768_);
return v_res_3774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0(lean_object* v_snd_3782_, lean_object* v___x_3783_, lean_object* v_score_3784_, lean_object* v___x_3785_, lean_object* v_k_3786_, lean_object* v_args_3787_, lean_object* v_cases_3788_){
_start:
{
lean_object* v___x_3789_; 
v___x_3789_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_snd_3782_, v_k_3786_);
if (lean_obj_tag(v___x_3789_) == 0)
{
lean_dec_ref(v___x_3783_);
return v_cases_3788_;
}
else
{
lean_object* v_val_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; 
v_val_3790_ = lean_ctor_get(v___x_3789_, 0);
lean_inc(v_val_3790_);
lean_dec_ref_known(v___x_3789_, 1);
v___x_3791_ = l_Array_append___redArg(v___x_3783_, v_args_3787_);
v___x_3792_ = lean_nat_add(v_score_3784_, v___x_3785_);
v___x_3793_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3793_, 0, v___x_3791_);
lean_ctor_set(v___x_3793_, 1, v___x_3792_);
lean_ctor_set(v___x_3793_, 2, v_val_3790_);
v___x_3794_ = lean_array_push(v_cases_3788_, v___x_3793_);
return v___x_3794_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0___boxed(lean_object* v_snd_3795_, lean_object* v___x_3796_, lean_object* v_score_3797_, lean_object* v___x_3798_, lean_object* v_k_3799_, lean_object* v_args_3800_, lean_object* v_cases_3801_){
_start:
{
lean_object* v_res_3802_; 
v_res_3802_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0(v_snd_3795_, v___x_3796_, v_score_3797_, v___x_3798_, v_k_3799_, v_args_3800_, v_cases_3801_);
lean_dec_ref(v_args_3800_);
lean_dec(v_k_3799_);
lean_dec(v___x_3798_);
lean_dec(v_score_3797_);
lean_dec_ref(v_snd_3795_);
return v_res_3802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(lean_object* v_cases_3803_, lean_object* v_result_3804_, lean_object* v_a_3805_, lean_object* v_a_3806_, lean_object* v_a_3807_, lean_object* v_a_3808_, lean_object* v_a_3809_){
_start:
{
lean_object* v___x_3811_; lean_object* v___x_3812_; uint8_t v___x_3813_; 
v___x_3811_ = lean_array_get_size(v_cases_3803_);
v___x_3812_ = lean_unsigned_to_nat(0u);
v___x_3813_ = lean_nat_dec_eq(v___x_3811_, v___x_3812_);
if (v___x_3813_ == 0)
{
lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v_ca_3817_; lean_object* v_todo_3818_; lean_object* v_score_3819_; lean_object* v_c_3820_; lean_object* v___x_3822_; uint8_t v_isShared_3823_; uint8_t v_isSharedCheck_3886_; 
v___x_3814_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedPartialMatch_default));
v___x_3815_ = lean_unsigned_to_nat(1u);
v___x_3816_ = lean_nat_sub(v___x_3811_, v___x_3815_);
v_ca_3817_ = lean_array_get(v___x_3814_, v_cases_3803_, v___x_3816_);
lean_dec(v___x_3816_);
v_todo_3818_ = lean_ctor_get(v_ca_3817_, 0);
v_score_3819_ = lean_ctor_get(v_ca_3817_, 1);
v_c_3820_ = lean_ctor_get(v_ca_3817_, 2);
v_isSharedCheck_3886_ = !lean_is_exclusive(v_ca_3817_);
if (v_isSharedCheck_3886_ == 0)
{
v___x_3822_ = v_ca_3817_;
v_isShared_3823_ = v_isSharedCheck_3886_;
goto v_resetjp_3821_;
}
else
{
lean_inc(v_c_3820_);
lean_inc(v_score_3819_);
lean_inc(v_todo_3818_);
lean_dec(v_ca_3817_);
v___x_3822_ = lean_box(0);
v_isShared_3823_ = v_isSharedCheck_3886_;
goto v_resetjp_3821_;
}
v_resetjp_3821_:
{
lean_object* v___x_3824_; lean_object* v_cases_3825_; lean_object* v___x_3826_; 
v___x_3824_ = l_Lean_instInhabitedExpr;
v_cases_3825_ = lean_array_pop(v_cases_3803_);
v___x_3826_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_c_3820_, v_a_3805_, v_a_3806_, v_a_3807_, v_a_3808_, v_a_3809_);
lean_dec(v_c_3820_);
if (lean_obj_tag(v___x_3826_) == 0)
{
lean_object* v_a_3827_; lean_object* v___y_3829_; lean_object* v___y_3830_; uint8_t v___y_3831_; lean_object* v___y_3832_; lean_object* v_snd_3855_; lean_object* v_fst_3856_; lean_object* v_fst_3857_; lean_object* v_snd_3858_; lean_object* v___x_3859_; uint8_t v___y_3861_; uint8_t v___x_3871_; 
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
v___x_3859_ = lean_array_get_size(v_todo_3818_);
v___x_3871_ = lean_nat_dec_eq(v___x_3859_, v___x_3812_);
if (v___x_3871_ == 0)
{
uint8_t v___x_3872_; 
lean_dec(v_fst_3856_);
v___x_3872_ = lean_nat_dec_eq(v_fst_3857_, v___x_3812_);
if (v___x_3872_ == 0)
{
v___y_3861_ = v___x_3871_;
goto v___jp_3860_;
}
else
{
lean_object* v_size_3873_; uint8_t v___x_3874_; 
v_size_3873_ = lean_ctor_get(v_snd_3858_, 0);
v___x_3874_ = lean_nat_dec_eq(v_size_3873_, v___x_3812_);
if (v___x_3874_ == 0)
{
v___y_3861_ = v___x_3874_;
goto v___jp_3860_;
}
else
{
lean_dec(v_snd_3858_);
lean_dec(v_fst_3857_);
lean_del_object(v___x_3822_);
lean_dec(v_score_3819_);
lean_dec_ref(v_todo_3818_);
v_cases_3803_ = v_cases_3825_;
goto _start;
}
}
}
else
{
lean_object* v___x_3876_; 
lean_dec(v_snd_3858_);
lean_dec(v_fst_3857_);
lean_del_object(v___x_3822_);
lean_dec_ref(v_todo_3818_);
v___x_3876_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v_result_3804_, v_score_3819_, v_fst_3856_);
lean_dec(v_score_3819_);
v_cases_3803_ = v_cases_3825_;
v_result_3804_ = v___x_3876_;
goto _start;
}
v___jp_3828_:
{
uint8_t v___x_3833_; lean_object* v___x_3834_; 
v___x_3833_ = 1;
v___x_3834_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v___y_3830_, v___x_3833_, v___y_3831_, v_a_3806_, v_a_3807_, v_a_3808_, v_a_3809_);
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
lean_dec_ref(v___y_3829_);
v_cases_3803_ = v___y_3832_;
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
lean_inc_ref(v___y_3829_);
v___x_3841_ = lean_apply_3(v___y_3829_, v___x_3839_, v___x_3840_, v___y_3832_);
v___x_3842_ = lean_apply_3(v___y_3829_, v_fst_3836_, v_snd_3838_, v___x_3841_);
v_cases_3803_ = v___x_3842_;
goto _start;
}
default: 
{
lean_object* v_snd_3844_; lean_object* v___x_3845_; 
v_snd_3844_ = lean_ctor_get(v_a_3835_, 1);
lean_inc(v_snd_3844_);
lean_dec(v_a_3835_);
v___x_3845_ = lean_apply_3(v___y_3829_, v_fst_3836_, v_snd_3844_, v___y_3832_);
v_cases_3803_ = v___x_3845_;
goto _start;
}
}
}
else
{
lean_object* v_a_3847_; lean_object* v___x_3849_; uint8_t v_isShared_3850_; uint8_t v_isSharedCheck_3854_; 
lean_dec_ref(v___y_3832_);
lean_dec_ref(v___y_3829_);
lean_dec_ref(v_result_3804_);
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
v___jp_3860_:
{
lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___f_3865_; uint8_t v___x_3866_; 
v___x_3862_ = lean_nat_sub(v___x_3859_, v___x_3815_);
v___x_3863_ = lean_array_get(v___x_3824_, v_todo_3818_, v___x_3862_);
lean_dec(v___x_3862_);
v___x_3864_ = lean_array_pop(v_todo_3818_);
lean_inc(v_score_3819_);
lean_inc_ref(v___x_3864_);
v___f_3865_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0___boxed), 7, 4);
lean_closure_set(v___f_3865_, 0, v_snd_3858_);
lean_closure_set(v___f_3865_, 1, v___x_3864_);
lean_closure_set(v___f_3865_, 2, v_score_3819_);
lean_closure_set(v___f_3865_, 3, v___x_3815_);
v___x_3866_ = lean_nat_dec_eq(v_fst_3857_, v___x_3812_);
if (v___x_3866_ == 0)
{
lean_object* v___x_3868_; 
if (v_isShared_3823_ == 0)
{
lean_ctor_set(v___x_3822_, 2, v_fst_3857_);
lean_ctor_set(v___x_3822_, 0, v___x_3864_);
v___x_3868_ = v___x_3822_;
goto v_reusejp_3867_;
}
else
{
lean_object* v_reuseFailAlloc_3870_; 
v_reuseFailAlloc_3870_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3870_, 0, v___x_3864_);
lean_ctor_set(v_reuseFailAlloc_3870_, 1, v_score_3819_);
lean_ctor_set(v_reuseFailAlloc_3870_, 2, v_fst_3857_);
v___x_3868_ = v_reuseFailAlloc_3870_;
goto v_reusejp_3867_;
}
v_reusejp_3867_:
{
lean_object* v___x_3869_; 
v___x_3869_ = lean_array_push(v_cases_3825_, v___x_3868_);
v___y_3829_ = v___f_3865_;
v___y_3830_ = v___x_3863_;
v___y_3831_ = v___y_3861_;
v___y_3832_ = v___x_3869_;
goto v___jp_3828_;
}
}
else
{
lean_dec_ref(v___x_3864_);
lean_dec(v_fst_3857_);
lean_del_object(v___x_3822_);
lean_dec(v_score_3819_);
v___y_3829_ = v___f_3865_;
v___y_3830_ = v___x_3863_;
v___y_3831_ = v___y_3861_;
v___y_3832_ = v_cases_3825_;
goto v___jp_3828_;
}
}
}
else
{
lean_object* v_a_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3885_; 
lean_dec_ref(v_cases_3825_);
lean_del_object(v___x_3822_);
lean_dec(v_score_3819_);
lean_dec_ref(v_todo_3818_);
lean_dec_ref(v_result_3804_);
v_a_3878_ = lean_ctor_get(v___x_3826_, 0);
v_isSharedCheck_3885_ = !lean_is_exclusive(v___x_3826_);
if (v_isSharedCheck_3885_ == 0)
{
v___x_3880_ = v___x_3826_;
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_a_3878_);
lean_dec(v___x_3826_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
lean_object* v___x_3883_; 
if (v_isShared_3881_ == 0)
{
v___x_3883_ = v___x_3880_;
goto v_reusejp_3882_;
}
else
{
lean_object* v_reuseFailAlloc_3884_; 
v_reuseFailAlloc_3884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3884_, 0, v_a_3878_);
v___x_3883_ = v_reuseFailAlloc_3884_;
goto v_reusejp_3882_;
}
v_reusejp_3882_:
{
return v___x_3883_;
}
}
}
}
}
else
{
lean_object* v___x_3887_; 
lean_dec_ref(v_cases_3803_);
v___x_3887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3887_, 0, v_result_3804_);
return v___x_3887_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___boxed(lean_object* v_cases_3888_, lean_object* v_result_3889_, lean_object* v_a_3890_, lean_object* v_a_3891_, lean_object* v_a_3892_, lean_object* v_a_3893_, lean_object* v_a_3894_, lean_object* v_a_3895_){
_start:
{
lean_object* v_res_3896_; 
v_res_3896_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v_cases_3888_, v_result_3889_, v_a_3890_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_);
lean_dec(v_a_3894_);
lean_dec_ref(v_a_3893_);
lean_dec(v_a_3892_);
lean_dec_ref(v_a_3891_);
lean_dec(v_a_3890_);
return v_res_3896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop(lean_object* v_00_u03b1_3897_, lean_object* v_cases_3898_, lean_object* v_result_3899_, lean_object* v_a_3900_, lean_object* v_a_3901_, lean_object* v_a_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_){
_start:
{
lean_object* v___x_3906_; 
v___x_3906_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v_cases_3898_, v_result_3899_, v_a_3900_, v_a_3901_, v_a_3902_, v_a_3903_, v_a_3904_);
return v___x_3906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___boxed(lean_object* v_00_u03b1_3907_, lean_object* v_cases_3908_, lean_object* v_result_3909_, lean_object* v_a_3910_, lean_object* v_a_3911_, lean_object* v_a_3912_, lean_object* v_a_3913_, lean_object* v_a_3914_, lean_object* v_a_3915_){
_start:
{
lean_object* v_res_3916_; 
v_res_3916_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop(v_00_u03b1_3907_, v_cases_3908_, v_result_3909_, v_a_3910_, v_a_3911_, v_a_3912_, v_a_3913_, v_a_3914_);
lean_dec(v_a_3914_);
lean_dec_ref(v_a_3913_);
lean_dec(v_a_3912_);
lean_dec_ref(v_a_3911_);
lean_dec(v_a_3910_);
return v_res_3916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult___redArg(lean_object* v_root_3919_, lean_object* v_a_3920_, lean_object* v_a_3921_, lean_object* v_a_3922_, lean_object* v_a_3923_, lean_object* v_a_3924_){
_start:
{
lean_object* v___x_3926_; lean_object* v___x_3927_; 
v___x_3926_ = lean_box(3);
v___x_3927_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_root_3919_, v___x_3926_);
if (lean_obj_tag(v___x_3927_) == 0)
{
lean_object* v___x_3928_; lean_object* v___x_3929_; 
v___x_3928_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_getStarResult___redArg___closed__0));
v___x_3929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3929_, 0, v___x_3928_);
return v___x_3929_;
}
else
{
lean_object* v_val_3930_; lean_object* v___x_3931_; 
v_val_3930_ = lean_ctor_get(v___x_3927_, 0);
lean_inc(v_val_3930_);
lean_dec_ref_known(v___x_3927_, 1);
v___x_3931_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_val_3930_, v_a_3920_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_);
lean_dec(v_val_3930_);
if (lean_obj_tag(v___x_3931_) == 0)
{
lean_object* v_a_3932_; lean_object* v___x_3934_; uint8_t v_isShared_3935_; uint8_t v_isSharedCheck_3943_; 
v_a_3932_ = lean_ctor_get(v___x_3931_, 0);
v_isSharedCheck_3943_ = !lean_is_exclusive(v___x_3931_);
if (v_isSharedCheck_3943_ == 0)
{
v___x_3934_ = v___x_3931_;
v_isShared_3935_ = v_isSharedCheck_3943_;
goto v_resetjp_3933_;
}
else
{
lean_inc(v_a_3932_);
lean_dec(v___x_3931_);
v___x_3934_ = lean_box(0);
v_isShared_3935_ = v_isSharedCheck_3943_;
goto v_resetjp_3933_;
}
v_resetjp_3933_:
{
lean_object* v_fst_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3941_; 
v_fst_3936_ = lean_ctor_get(v_a_3932_, 0);
lean_inc(v_fst_3936_);
lean_dec(v_a_3932_);
v___x_3937_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_getStarResult___redArg___closed__0));
v___x_3938_ = lean_unsigned_to_nat(1u);
v___x_3939_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v___x_3937_, v___x_3938_, v_fst_3936_);
if (v_isShared_3935_ == 0)
{
lean_ctor_set(v___x_3934_, 0, v___x_3939_);
v___x_3941_ = v___x_3934_;
goto v_reusejp_3940_;
}
else
{
lean_object* v_reuseFailAlloc_3942_; 
v_reuseFailAlloc_3942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3942_, 0, v___x_3939_);
v___x_3941_ = v_reuseFailAlloc_3942_;
goto v_reusejp_3940_;
}
v_reusejp_3940_:
{
return v___x_3941_;
}
}
}
else
{
lean_object* v_a_3944_; lean_object* v___x_3946_; uint8_t v_isShared_3947_; uint8_t v_isSharedCheck_3951_; 
v_a_3944_ = lean_ctor_get(v___x_3931_, 0);
v_isSharedCheck_3951_ = !lean_is_exclusive(v___x_3931_);
if (v_isSharedCheck_3951_ == 0)
{
v___x_3946_ = v___x_3931_;
v_isShared_3947_ = v_isSharedCheck_3951_;
goto v_resetjp_3945_;
}
else
{
lean_inc(v_a_3944_);
lean_dec(v___x_3931_);
v___x_3946_ = lean_box(0);
v_isShared_3947_ = v_isSharedCheck_3951_;
goto v_resetjp_3945_;
}
v_resetjp_3945_:
{
lean_object* v___x_3949_; 
if (v_isShared_3947_ == 0)
{
v___x_3949_ = v___x_3946_;
goto v_reusejp_3948_;
}
else
{
lean_object* v_reuseFailAlloc_3950_; 
v_reuseFailAlloc_3950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3950_, 0, v_a_3944_);
v___x_3949_ = v_reuseFailAlloc_3950_;
goto v_reusejp_3948_;
}
v_reusejp_3948_:
{
return v___x_3949_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult___redArg___boxed(lean_object* v_root_3952_, lean_object* v_a_3953_, lean_object* v_a_3954_, lean_object* v_a_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_, lean_object* v_a_3958_){
_start:
{
lean_object* v_res_3959_; 
v_res_3959_ = l_Lean_Meta_LazyDiscrTree_getStarResult___redArg(v_root_3952_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_, v_a_3957_);
lean_dec(v_a_3957_);
lean_dec_ref(v_a_3956_);
lean_dec(v_a_3955_);
lean_dec_ref(v_a_3954_);
lean_dec(v_a_3953_);
lean_dec_ref(v_root_3952_);
return v_res_3959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult(lean_object* v_00_u03b1_3960_, lean_object* v_root_3961_, lean_object* v_a_3962_, lean_object* v_a_3963_, lean_object* v_a_3964_, lean_object* v_a_3965_, lean_object* v_a_3966_){
_start:
{
lean_object* v___x_3968_; 
v___x_3968_ = l_Lean_Meta_LazyDiscrTree_getStarResult___redArg(v_root_3961_, v_a_3962_, v_a_3963_, v_a_3964_, v_a_3965_, v_a_3966_);
return v___x_3968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult___boxed(lean_object* v_00_u03b1_3969_, lean_object* v_root_3970_, lean_object* v_a_3971_, lean_object* v_a_3972_, lean_object* v_a_3973_, lean_object* v_a_3974_, lean_object* v_a_3975_, lean_object* v_a_3976_){
_start:
{
lean_object* v_res_3977_; 
v_res_3977_ = l_Lean_Meta_LazyDiscrTree_getStarResult(v_00_u03b1_3969_, v_root_3970_, v_a_3971_, v_a_3972_, v_a_3973_, v_a_3974_, v_a_3975_);
lean_dec(v_a_3975_);
lean_dec_ref(v_a_3974_);
lean_dec(v_a_3973_);
lean_dec_ref(v_a_3972_);
lean_dec(v_a_3971_);
lean_dec_ref(v_root_3970_);
return v_res_3977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushRootCase(lean_object* v_r_3978_, lean_object* v_k_3979_, lean_object* v_args_3980_, lean_object* v_cases_3981_){
_start:
{
lean_object* v___x_3982_; 
v___x_3982_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_r_3978_, v_k_3979_);
if (lean_obj_tag(v___x_3982_) == 0)
{
lean_dec_ref(v_args_3980_);
return v_cases_3981_;
}
else
{
lean_object* v_val_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; 
v_val_3983_ = lean_ctor_get(v___x_3982_, 0);
lean_inc(v_val_3983_);
lean_dec_ref_known(v___x_3982_, 1);
v___x_3984_ = lean_unsigned_to_nat(1u);
v___x_3985_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3985_, 0, v_args_3980_);
lean_ctor_set(v___x_3985_, 1, v___x_3984_);
lean_ctor_set(v___x_3985_, 2, v_val_3983_);
v___x_3986_ = lean_array_push(v_cases_3981_, v___x_3985_);
return v___x_3986_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushRootCase___boxed(lean_object* v_r_3987_, lean_object* v_k_3988_, lean_object* v_args_3989_, lean_object* v_cases_3990_){
_start:
{
lean_object* v_res_3991_; 
v_res_3991_ = l_Lean_Meta_LazyDiscrTree_pushRootCase(v_r_3987_, v_k_3988_, v_args_3989_, v_cases_3990_);
lean_dec(v_k_3988_);
lean_dec_ref(v_r_3987_);
return v_res_3991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg(lean_object* v_root_3994_, lean_object* v_e_3995_, lean_object* v_a_3996_, lean_object* v_a_3997_, lean_object* v_a_3998_, lean_object* v_a_3999_, lean_object* v_a_4000_){
_start:
{
lean_object* v___x_4002_; 
v___x_4002_ = l_Lean_Meta_LazyDiscrTree_getStarResult___redArg(v_root_3994_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_, v_a_4000_);
if (lean_obj_tag(v___x_4002_) == 0)
{
lean_object* v_a_4003_; uint8_t v___x_4004_; lean_object* v___x_4005_; 
v_a_4003_ = lean_ctor_get(v___x_4002_, 0);
lean_inc(v_a_4003_);
lean_dec_ref_known(v___x_4002_, 1);
v___x_4004_ = 1;
v___x_4005_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_3995_, v___x_4004_, v___x_4004_, v_a_3997_, v_a_3998_, v_a_3999_, v_a_4000_);
if (lean_obj_tag(v___x_4005_) == 0)
{
lean_object* v_a_4006_; lean_object* v_fst_4007_; 
v_a_4006_ = lean_ctor_get(v___x_4005_, 0);
lean_inc(v_a_4006_);
lean_dec_ref_known(v___x_4005_, 1);
v_fst_4007_ = lean_ctor_get(v_a_4006_, 0);
lean_inc(v_fst_4007_);
switch(lean_obj_tag(v_fst_4007_))
{
case 3:
{
lean_object* v___x_4008_; lean_object* v___x_4009_; 
lean_dec(v_a_4006_);
v___x_4008_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg___closed__0));
v___x_4009_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v___x_4008_, v_a_4003_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_, v_a_4000_);
return v___x_4009_;
}
case 5:
{
lean_object* v_snd_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; 
v_snd_4010_ = lean_ctor_get(v_a_4006_, 1);
lean_inc(v_snd_4010_);
lean_dec(v_a_4006_);
v___x_4011_ = lean_box(4);
v___x_4012_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
v___x_4013_ = l_Lean_Meta_LazyDiscrTree_pushRootCase(v_root_3994_, v___x_4011_, v___x_4012_, v___x_4012_);
v___x_4014_ = l_Lean_Meta_LazyDiscrTree_pushRootCase(v_root_3994_, v_fst_4007_, v_snd_4010_, v___x_4013_);
v___x_4015_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v___x_4014_, v_a_4003_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_, v_a_4000_);
return v___x_4015_;
}
default: 
{
lean_object* v_snd_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; 
v_snd_4016_ = lean_ctor_get(v_a_4006_, 1);
lean_inc(v_snd_4016_);
lean_dec(v_a_4006_);
v___x_4017_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg___closed__0));
v___x_4018_ = l_Lean_Meta_LazyDiscrTree_pushRootCase(v_root_3994_, v_fst_4007_, v_snd_4016_, v___x_4017_);
lean_dec(v_fst_4007_);
v___x_4019_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v___x_4018_, v_a_4003_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_, v_a_4000_);
return v___x_4019_;
}
}
}
else
{
lean_object* v_a_4020_; lean_object* v___x_4022_; uint8_t v_isShared_4023_; uint8_t v_isSharedCheck_4027_; 
lean_dec(v_a_4003_);
v_a_4020_ = lean_ctor_get(v___x_4005_, 0);
v_isSharedCheck_4027_ = !lean_is_exclusive(v___x_4005_);
if (v_isSharedCheck_4027_ == 0)
{
v___x_4022_ = v___x_4005_;
v_isShared_4023_ = v_isSharedCheck_4027_;
goto v_resetjp_4021_;
}
else
{
lean_inc(v_a_4020_);
lean_dec(v___x_4005_);
v___x_4022_ = lean_box(0);
v_isShared_4023_ = v_isSharedCheck_4027_;
goto v_resetjp_4021_;
}
v_resetjp_4021_:
{
lean_object* v___x_4025_; 
if (v_isShared_4023_ == 0)
{
v___x_4025_ = v___x_4022_;
goto v_reusejp_4024_;
}
else
{
lean_object* v_reuseFailAlloc_4026_; 
v_reuseFailAlloc_4026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4026_, 0, v_a_4020_);
v___x_4025_ = v_reuseFailAlloc_4026_;
goto v_reusejp_4024_;
}
v_reusejp_4024_:
{
return v___x_4025_;
}
}
}
}
else
{
lean_dec_ref(v_e_3995_);
return v___x_4002_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg___boxed(lean_object* v_root_4028_, lean_object* v_e_4029_, lean_object* v_a_4030_, lean_object* v_a_4031_, lean_object* v_a_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_, lean_object* v_a_4035_){
_start:
{
lean_object* v_res_4036_; 
v_res_4036_ = l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg(v_root_4028_, v_e_4029_, v_a_4030_, v_a_4031_, v_a_4032_, v_a_4033_, v_a_4034_);
lean_dec(v_a_4034_);
lean_dec_ref(v_a_4033_);
lean_dec(v_a_4032_);
lean_dec_ref(v_a_4031_);
lean_dec(v_a_4030_);
lean_dec_ref(v_root_4028_);
return v_res_4036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore(lean_object* v_00_u03b1_4037_, lean_object* v_root_4038_, lean_object* v_e_4039_, lean_object* v_a_4040_, lean_object* v_a_4041_, lean_object* v_a_4042_, lean_object* v_a_4043_, lean_object* v_a_4044_){
_start:
{
lean_object* v___x_4046_; 
v___x_4046_ = l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg(v_root_4038_, v_e_4039_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_, v_a_4044_);
return v___x_4046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore___boxed(lean_object* v_00_u03b1_4047_, lean_object* v_root_4048_, lean_object* v_e_4049_, lean_object* v_a_4050_, lean_object* v_a_4051_, lean_object* v_a_4052_, lean_object* v_a_4053_, lean_object* v_a_4054_, lean_object* v_a_4055_){
_start:
{
lean_object* v_res_4056_; 
v_res_4056_ = l_Lean_Meta_LazyDiscrTree_getMatchCore(v_00_u03b1_4047_, v_root_4048_, v_e_4049_, v_a_4050_, v_a_4051_, v_a_4052_, v_a_4053_, v_a_4054_);
lean_dec(v_a_4054_);
lean_dec_ref(v_a_4053_);
lean_dec(v_a_4052_);
lean_dec_ref(v_a_4051_);
lean_dec(v_a_4050_);
lean_dec_ref(v_root_4048_);
return v_res_4056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch___redArg(lean_object* v_d_4057_, lean_object* v_e_4058_, lean_object* v_a_4059_, lean_object* v_a_4060_, lean_object* v_a_4061_, lean_object* v_a_4062_){
_start:
{
lean_object* v___y_4065_; lean_object* v_roots_4082_; lean_object* v___x_4083_; uint8_t v_transparency_4084_; lean_object* v___x_4085_; uint8_t v___x_4086_; uint8_t v___x_4087_; 
v_roots_4082_ = lean_ctor_get(v_d_4057_, 1);
v___x_4083_ = l_Lean_Meta_Context_config(v_a_4059_);
v_transparency_4084_ = lean_ctor_get_uint8(v___x_4083_, 9);
lean_dec_ref(v___x_4083_);
lean_inc_ref(v_roots_4082_);
v___x_4085_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getMatchCore___boxed), 9, 3);
lean_closure_set(v___x_4085_, 0, lean_box(0));
lean_closure_set(v___x_4085_, 1, v_roots_4082_);
lean_closure_set(v___x_4085_, 2, v_e_4058_);
v___x_4086_ = 2;
v___x_4087_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_4084_, v___x_4086_);
if (v___x_4087_ == 0)
{
lean_object* v_keyedConfig_4088_; uint8_t v_trackZetaDelta_4089_; lean_object* v_zetaDeltaSet_4090_; lean_object* v_lctx_4091_; lean_object* v_localInstances_4092_; lean_object* v_defEqCtx_x3f_4093_; lean_object* v_synthPendingDepth_4094_; lean_object* v_customCanUnfoldPredicate_x3f_4095_; uint8_t v_univApprox_4096_; uint8_t v_inTypeClassResolution_4097_; uint8_t v_cacheInferType_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; 
v_keyedConfig_4088_ = lean_ctor_get(v_a_4059_, 0);
v_trackZetaDelta_4089_ = lean_ctor_get_uint8(v_a_4059_, sizeof(void*)*7);
v_zetaDeltaSet_4090_ = lean_ctor_get(v_a_4059_, 1);
v_lctx_4091_ = lean_ctor_get(v_a_4059_, 2);
v_localInstances_4092_ = lean_ctor_get(v_a_4059_, 3);
v_defEqCtx_x3f_4093_ = lean_ctor_get(v_a_4059_, 4);
v_synthPendingDepth_4094_ = lean_ctor_get(v_a_4059_, 5);
v_customCanUnfoldPredicate_x3f_4095_ = lean_ctor_get(v_a_4059_, 6);
v_univApprox_4096_ = lean_ctor_get_uint8(v_a_4059_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4097_ = lean_ctor_get_uint8(v_a_4059_, sizeof(void*)*7 + 2);
v_cacheInferType_4098_ = lean_ctor_get_uint8(v_a_4059_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_4088_);
v___x_4099_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4086_, v_keyedConfig_4088_);
lean_inc(v_customCanUnfoldPredicate_x3f_4095_);
lean_inc(v_synthPendingDepth_4094_);
lean_inc(v_defEqCtx_x3f_4093_);
lean_inc_ref(v_localInstances_4092_);
lean_inc_ref(v_lctx_4091_);
lean_inc(v_zetaDeltaSet_4090_);
v___x_4100_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4100_, 0, v___x_4099_);
lean_ctor_set(v___x_4100_, 1, v_zetaDeltaSet_4090_);
lean_ctor_set(v___x_4100_, 2, v_lctx_4091_);
lean_ctor_set(v___x_4100_, 3, v_localInstances_4092_);
lean_ctor_set(v___x_4100_, 4, v_defEqCtx_x3f_4093_);
lean_ctor_set(v___x_4100_, 5, v_synthPendingDepth_4094_);
lean_ctor_set(v___x_4100_, 6, v_customCanUnfoldPredicate_x3f_4095_);
lean_ctor_set_uint8(v___x_4100_, sizeof(void*)*7, v_trackZetaDelta_4089_);
lean_ctor_set_uint8(v___x_4100_, sizeof(void*)*7 + 1, v_univApprox_4096_);
lean_ctor_set_uint8(v___x_4100_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4097_);
lean_ctor_set_uint8(v___x_4100_, sizeof(void*)*7 + 3, v_cacheInferType_4098_);
v___x_4101_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_d_4057_, v___x_4085_, v___x_4100_, v_a_4060_, v_a_4061_, v_a_4062_);
lean_dec_ref_known(v___x_4100_, 7);
v___y_4065_ = v___x_4101_;
goto v___jp_4064_;
}
else
{
lean_object* v___x_4102_; 
v___x_4102_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_d_4057_, v___x_4085_, v_a_4059_, v_a_4060_, v_a_4061_, v_a_4062_);
v___y_4065_ = v___x_4102_;
goto v___jp_4064_;
}
v___jp_4064_:
{
if (lean_obj_tag(v___y_4065_) == 0)
{
lean_object* v_a_4066_; lean_object* v___x_4068_; uint8_t v_isShared_4069_; uint8_t v_isSharedCheck_4073_; 
v_a_4066_ = lean_ctor_get(v___y_4065_, 0);
v_isSharedCheck_4073_ = !lean_is_exclusive(v___y_4065_);
if (v_isSharedCheck_4073_ == 0)
{
v___x_4068_ = v___y_4065_;
v_isShared_4069_ = v_isSharedCheck_4073_;
goto v_resetjp_4067_;
}
else
{
lean_inc(v_a_4066_);
lean_dec(v___y_4065_);
v___x_4068_ = lean_box(0);
v_isShared_4069_ = v_isSharedCheck_4073_;
goto v_resetjp_4067_;
}
v_resetjp_4067_:
{
lean_object* v___x_4071_; 
if (v_isShared_4069_ == 0)
{
v___x_4071_ = v___x_4068_;
goto v_reusejp_4070_;
}
else
{
lean_object* v_reuseFailAlloc_4072_; 
v_reuseFailAlloc_4072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4072_, 0, v_a_4066_);
v___x_4071_ = v_reuseFailAlloc_4072_;
goto v_reusejp_4070_;
}
v_reusejp_4070_:
{
return v___x_4071_;
}
}
}
else
{
lean_object* v_a_4074_; lean_object* v___x_4076_; uint8_t v_isShared_4077_; uint8_t v_isSharedCheck_4081_; 
v_a_4074_ = lean_ctor_get(v___y_4065_, 0);
v_isSharedCheck_4081_ = !lean_is_exclusive(v___y_4065_);
if (v_isSharedCheck_4081_ == 0)
{
v___x_4076_ = v___y_4065_;
v_isShared_4077_ = v_isSharedCheck_4081_;
goto v_resetjp_4075_;
}
else
{
lean_inc(v_a_4074_);
lean_dec(v___y_4065_);
v___x_4076_ = lean_box(0);
v_isShared_4077_ = v_isSharedCheck_4081_;
goto v_resetjp_4075_;
}
v_resetjp_4075_:
{
lean_object* v___x_4079_; 
if (v_isShared_4077_ == 0)
{
v___x_4079_ = v___x_4076_;
goto v_reusejp_4078_;
}
else
{
lean_object* v_reuseFailAlloc_4080_; 
v_reuseFailAlloc_4080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4080_, 0, v_a_4074_);
v___x_4079_ = v_reuseFailAlloc_4080_;
goto v_reusejp_4078_;
}
v_reusejp_4078_:
{
return v___x_4079_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch___redArg___boxed(lean_object* v_d_4103_, lean_object* v_e_4104_, lean_object* v_a_4105_, lean_object* v_a_4106_, lean_object* v_a_4107_, lean_object* v_a_4108_, lean_object* v_a_4109_){
_start:
{
lean_object* v_res_4110_; 
v_res_4110_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v_d_4103_, v_e_4104_, v_a_4105_, v_a_4106_, v_a_4107_, v_a_4108_);
lean_dec(v_a_4108_);
lean_dec_ref(v_a_4107_);
lean_dec(v_a_4106_);
lean_dec_ref(v_a_4105_);
return v_res_4110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch(lean_object* v_00_u03b1_4111_, lean_object* v_d_4112_, lean_object* v_e_4113_, lean_object* v_a_4114_, lean_object* v_a_4115_, lean_object* v_a_4116_, lean_object* v_a_4117_){
_start:
{
lean_object* v___x_4119_; 
v___x_4119_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v_d_4112_, v_e_4113_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_);
return v___x_4119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch___boxed(lean_object* v_00_u03b1_4120_, lean_object* v_d_4121_, lean_object* v_e_4122_, lean_object* v_a_4123_, lean_object* v_a_4124_, lean_object* v_a_4125_, lean_object* v_a_4126_, lean_object* v_a_4127_){
_start:
{
lean_object* v_res_4128_; 
v_res_4128_ = l_Lean_Meta_LazyDiscrTree_getMatch(v_00_u03b1_4120_, v_d_4121_, v_e_4122_, v_a_4123_, v_a_4124_, v_a_4125_, v_a_4126_);
lean_dec(v_a_4126_);
lean_dec_ref(v_a_4125_);
lean_dec(v_a_4124_);
lean_dec_ref(v_a_4123_);
return v_res_4128_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1(void){
_start:
{
lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; 
v___x_4131_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__0));
v___x_4132_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2);
v___x_4133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4133_, 0, v___x_4132_);
lean_ctor_set(v___x_4133_, 1, v___x_4131_);
return v___x_4133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg(){
_start:
{
lean_object* v___x_4135_; 
v___x_4135_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1);
return v___x_4135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___boxed(lean_object* v___dummy_4136_){
_start:
{
lean_object* v_res_4137_; 
v_res_4137_ = l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg();
return v_res_4137_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0(void){
_start:
{
lean_object* v___x_4138_; 
v___x_4138_ = l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg();
return v___x_4138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default(lean_object* v_00_u03b1_4139_){
_start:
{
lean_object* v___x_4140_; 
v___x_4140_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0);
return v___x_4140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___redArg(){
_start:
{
lean_object* v___x_4142_; 
v___x_4142_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0);
return v___x_4142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___redArg___boxed(lean_object* v___dummy_4143_){
_start:
{
lean_object* v_res_4144_; 
v_res_4144_ = l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___redArg();
return v_res_4144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree(lean_object* v_a_4145_){
_start:
{
lean_object* v___x_4146_; 
v___x_4146_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0);
return v___x_4146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(lean_object* v_d_4147_, lean_object* v_k_4148_, lean_object* v_f_4149_){
_start:
{
lean_object* v_roots_4150_; lean_object* v_tries_4151_; lean_object* v___x_4152_; 
v_roots_4150_ = lean_ctor_get(v_d_4147_, 0);
v_tries_4151_ = lean_ctor_get(v_d_4147_, 1);
v___x_4152_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_roots_4150_, v_k_4148_);
if (lean_obj_tag(v___x_4152_) == 0)
{
lean_object* v___x_4154_; uint8_t v_isShared_4155_; uint8_t v_isSharedCheck_4164_; 
lean_inc_ref(v_tries_4151_);
lean_inc_ref(v_roots_4150_);
v_isSharedCheck_4164_ = !lean_is_exclusive(v_d_4147_);
if (v_isSharedCheck_4164_ == 0)
{
lean_object* v_unused_4165_; lean_object* v_unused_4166_; 
v_unused_4165_ = lean_ctor_get(v_d_4147_, 1);
lean_dec(v_unused_4165_);
v_unused_4166_ = lean_ctor_get(v_d_4147_, 0);
lean_dec(v_unused_4166_);
v___x_4154_ = v_d_4147_;
v_isShared_4155_ = v_isSharedCheck_4164_;
goto v_resetjp_4153_;
}
else
{
lean_dec(v_d_4147_);
v___x_4154_ = lean_box(0);
v_isShared_4155_ = v_isSharedCheck_4164_;
goto v_resetjp_4153_;
}
v_resetjp_4153_:
{
lean_object* v___x_4156_; lean_object* v_roots_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4162_; 
v___x_4156_ = lean_array_get_size(v_tries_4151_);
v_roots_4157_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_roots_4150_, v_k_4148_, v___x_4156_);
v___x_4158_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__3));
v___x_4159_ = lean_apply_1(v_f_4149_, v___x_4158_);
v___x_4160_ = lean_array_push(v_tries_4151_, v___x_4159_);
if (v_isShared_4155_ == 0)
{
lean_ctor_set(v___x_4154_, 1, v___x_4160_);
lean_ctor_set(v___x_4154_, 0, v_roots_4157_);
v___x_4162_ = v___x_4154_;
goto v_reusejp_4161_;
}
else
{
lean_object* v_reuseFailAlloc_4163_; 
v_reuseFailAlloc_4163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4163_, 0, v_roots_4157_);
lean_ctor_set(v_reuseFailAlloc_4163_, 1, v___x_4160_);
v___x_4162_ = v_reuseFailAlloc_4163_;
goto v_reusejp_4161_;
}
v_reusejp_4161_:
{
return v___x_4162_;
}
}
}
else
{
lean_object* v_val_4167_; lean_object* v___x_4168_; uint8_t v___x_4169_; 
lean_dec(v_k_4148_);
v_val_4167_ = lean_ctor_get(v___x_4152_, 0);
lean_inc(v_val_4167_);
lean_dec_ref_known(v___x_4152_, 1);
v___x_4168_ = lean_array_get_size(v_tries_4151_);
v___x_4169_ = lean_nat_dec_lt(v_val_4167_, v___x_4168_);
if (v___x_4169_ == 0)
{
lean_dec(v_val_4167_);
lean_dec_ref(v_f_4149_);
return v_d_4147_;
}
else
{
lean_object* v___x_4171_; uint8_t v_isShared_4172_; uint8_t v_isSharedCheck_4181_; 
lean_inc_ref(v_tries_4151_);
lean_inc_ref(v_roots_4150_);
v_isSharedCheck_4181_ = !lean_is_exclusive(v_d_4147_);
if (v_isSharedCheck_4181_ == 0)
{
lean_object* v_unused_4182_; lean_object* v_unused_4183_; 
v_unused_4182_ = lean_ctor_get(v_d_4147_, 1);
lean_dec(v_unused_4182_);
v_unused_4183_ = lean_ctor_get(v_d_4147_, 0);
lean_dec(v_unused_4183_);
v___x_4171_ = v_d_4147_;
v_isShared_4172_ = v_isSharedCheck_4181_;
goto v_resetjp_4170_;
}
else
{
lean_dec(v_d_4147_);
v___x_4171_ = lean_box(0);
v_isShared_4172_ = v_isSharedCheck_4181_;
goto v_resetjp_4170_;
}
v_resetjp_4170_:
{
lean_object* v_v_4173_; lean_object* v___x_4174_; lean_object* v_xs_x27_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4179_; 
v_v_4173_ = lean_array_fget(v_tries_4151_, v_val_4167_);
v___x_4174_ = lean_box(0);
v_xs_x27_4175_ = lean_array_fset(v_tries_4151_, v_val_4167_, v___x_4174_);
v___x_4176_ = lean_apply_1(v_f_4149_, v_v_4173_);
v___x_4177_ = lean_array_fset(v_xs_x27_4175_, v_val_4167_, v___x_4176_);
lean_dec(v_val_4167_);
if (v_isShared_4172_ == 0)
{
lean_ctor_set(v___x_4171_, 1, v___x_4177_);
v___x_4179_ = v___x_4171_;
goto v_reusejp_4178_;
}
else
{
lean_object* v_reuseFailAlloc_4180_; 
v_reuseFailAlloc_4180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4180_, 0, v_roots_4150_);
lean_ctor_set(v_reuseFailAlloc_4180_, 1, v___x_4177_);
v___x_4179_ = v_reuseFailAlloc_4180_;
goto v_reusejp_4178_;
}
v_reusejp_4178_:
{
return v___x_4179_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt(lean_object* v_00_u03b1_4184_, lean_object* v_d_4185_, lean_object* v_k_4186_, lean_object* v_f_4187_){
_start:
{
lean_object* v___x_4188_; 
v___x_4188_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(v_d_4185_, v_k_4186_, v_f_4187_);
return v___x_4188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg___lam__0(lean_object* v_e_4189_, lean_object* v_x_4190_){
_start:
{
lean_object* v___x_4191_; 
v___x_4191_ = lean_array_push(v_x_4190_, v_e_4189_);
return v___x_4191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg(lean_object* v_d_4192_, lean_object* v_k_4193_, lean_object* v_e_4194_){
_start:
{
lean_object* v___f_4195_; lean_object* v___x_4196_; 
v___f_4195_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4195_, 0, v_e_4194_);
v___x_4196_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(v_d_4192_, v_k_4193_, v___f_4195_);
return v___x_4196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push(lean_object* v_00_u03b1_4197_, lean_object* v_d_4198_, lean_object* v_k_4199_, lean_object* v_e_4200_){
_start:
{
lean_object* v___x_4201_; 
v___x_4201_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg(v_d_4198_, v_k_4199_, v_e_4200_);
return v___x_4201_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(size_t v_sz_4202_, size_t v_i_4203_, lean_object* v_bs_4204_){
_start:
{
uint8_t v___x_4205_; 
v___x_4205_ = lean_usize_dec_lt(v_i_4203_, v_sz_4202_);
if (v___x_4205_ == 0)
{
return v_bs_4204_;
}
else
{
lean_object* v_v_4206_; lean_object* v___x_4207_; lean_object* v_bs_x27_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; size_t v___x_4212_; size_t v___x_4213_; lean_object* v___x_4214_; 
v_v_4206_ = lean_array_uget(v_bs_4204_, v_i_4203_);
v___x_4207_ = lean_unsigned_to_nat(0u);
v_bs_x27_4208_ = lean_array_uset(v_bs_4204_, v_i_4203_, v___x_4207_);
v___x_4209_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__0));
v___x_4210_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2);
v___x_4211_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4211_, 0, v___x_4209_);
lean_ctor_set(v___x_4211_, 1, v___x_4207_);
lean_ctor_set(v___x_4211_, 2, v___x_4210_);
lean_ctor_set(v___x_4211_, 3, v_v_4206_);
v___x_4212_ = ((size_t)1ULL);
v___x_4213_ = lean_usize_add(v_i_4203_, v___x_4212_);
v___x_4214_ = lean_array_uset(v_bs_x27_4208_, v_i_4203_, v___x_4211_);
v_i_4203_ = v___x_4213_;
v_bs_4204_ = v___x_4214_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg___boxed(lean_object* v_sz_4216_, lean_object* v_i_4217_, lean_object* v_bs_4218_){
_start:
{
size_t v_sz_boxed_4219_; size_t v_i_boxed_4220_; lean_object* v_res_4221_; 
v_sz_boxed_4219_ = lean_unbox_usize(v_sz_4216_);
lean_dec(v_sz_4216_);
v_i_boxed_4220_ = lean_unbox_usize(v_i_4217_);
lean_dec(v_i_4217_);
v_res_4221_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(v_sz_boxed_4219_, v_i_boxed_4220_, v_bs_4218_);
return v_res_4221_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__1(lean_object* v_x_4222_, lean_object* v_x_4223_){
_start:
{
if (lean_obj_tag(v_x_4223_) == 0)
{
return v_x_4222_;
}
else
{
lean_object* v_key_4224_; lean_object* v_value_4225_; lean_object* v_tail_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; 
v_key_4224_ = lean_ctor_get(v_x_4223_, 0);
lean_inc(v_key_4224_);
v_value_4225_ = lean_ctor_get(v_x_4223_, 1);
lean_inc(v_value_4225_);
v_tail_4226_ = lean_ctor_get(v_x_4223_, 2);
lean_inc(v_tail_4226_);
lean_dec_ref_known(v_x_4223_, 3);
v___x_4227_ = lean_unsigned_to_nat(1u);
v___x_4228_ = lean_nat_add(v_value_4225_, v___x_4227_);
lean_dec(v_value_4225_);
v___x_4229_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_x_4222_, v_key_4224_, v___x_4228_);
v_x_4222_ = v___x_4229_;
v_x_4223_ = v_tail_4226_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(lean_object* v_as_4231_, size_t v_i_4232_, size_t v_stop_4233_, lean_object* v_b_4234_){
_start:
{
uint8_t v___x_4235_; 
v___x_4235_ = lean_usize_dec_eq(v_i_4232_, v_stop_4233_);
if (v___x_4235_ == 0)
{
lean_object* v___x_4236_; lean_object* v___x_4237_; size_t v___x_4238_; size_t v___x_4239_; 
v___x_4236_ = lean_array_uget_borrowed(v_as_4231_, v_i_4232_);
lean_inc(v___x_4236_);
v___x_4237_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__1(v_b_4234_, v___x_4236_);
v___x_4238_ = ((size_t)1ULL);
v___x_4239_ = lean_usize_add(v_i_4232_, v___x_4238_);
v_i_4232_ = v___x_4239_;
v_b_4234_ = v___x_4237_;
goto _start;
}
else
{
return v_b_4234_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2___boxed(lean_object* v_as_4241_, lean_object* v_i_4242_, lean_object* v_stop_4243_, lean_object* v_b_4244_){
_start:
{
size_t v_i_boxed_4245_; size_t v_stop_boxed_4246_; lean_object* v_res_4247_; 
v_i_boxed_4245_ = lean_unbox_usize(v_i_4242_);
lean_dec(v_i_4242_);
v_stop_boxed_4246_ = lean_unbox_usize(v_stop_4243_);
lean_dec(v_stop_4243_);
v_res_4247_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(v_as_4241_, v_i_boxed_4245_, v_stop_boxed_4246_, v_b_4244_);
lean_dec_ref(v_as_4241_);
return v_res_4247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(lean_object* v_d_4248_){
_start:
{
lean_object* v_roots_4249_; lean_object* v_tries_4250_; lean_object* v___x_4252_; uint8_t v_isShared_4253_; uint8_t v_isSharedCheck_4273_; 
v_roots_4249_ = lean_ctor_get(v_d_4248_, 0);
v_tries_4250_ = lean_ctor_get(v_d_4248_, 1);
v_isSharedCheck_4273_ = !lean_is_exclusive(v_d_4248_);
if (v_isSharedCheck_4273_ == 0)
{
v___x_4252_ = v_d_4248_;
v_isShared_4253_ = v_isSharedCheck_4273_;
goto v_resetjp_4251_;
}
else
{
lean_inc(v_tries_4250_);
lean_inc(v_roots_4249_);
lean_dec(v_d_4248_);
v___x_4252_ = lean_box(0);
v_isShared_4253_ = v_isSharedCheck_4273_;
goto v_resetjp_4251_;
}
v_resetjp_4251_:
{
lean_object* v___y_4255_; lean_object* v_buckets_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; uint8_t v___x_4269_; 
v_buckets_4266_ = lean_ctor_get(v_roots_4249_, 1);
v___x_4267_ = lean_unsigned_to_nat(0u);
v___x_4268_ = lean_array_get_size(v_buckets_4266_);
v___x_4269_ = lean_nat_dec_lt(v___x_4267_, v___x_4268_);
if (v___x_4269_ == 0)
{
v___y_4255_ = v_roots_4249_;
goto v___jp_4254_;
}
else
{
size_t v___x_4270_; size_t v___x_4271_; lean_object* v___x_4272_; 
lean_inc_ref(v_buckets_4266_);
v___x_4270_ = ((size_t)0ULL);
v___x_4271_ = lean_usize_of_nat(v___x_4268_);
v___x_4272_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(v_buckets_4266_, v___x_4270_, v___x_4271_, v_roots_4249_);
lean_dec_ref(v_buckets_4266_);
v___y_4255_ = v___x_4272_;
goto v___jp_4254_;
}
v___jp_4254_:
{
lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; size_t v_sz_4259_; size_t v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4264_; 
v___x_4256_ = lean_unsigned_to_nat(1u);
v___x_4257_ = lean_mk_empty_array_with_capacity(v___x_4256_);
lean_dec_ref(v___x_4257_);
v___x_4258_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__0);
v_sz_4259_ = lean_array_size(v_tries_4250_);
v___x_4260_ = ((size_t)0ULL);
v___x_4261_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(v_sz_4259_, v___x_4260_, v_tries_4250_);
v___x_4262_ = l_Array_append___redArg(v___x_4258_, v___x_4261_);
lean_dec_ref(v___x_4261_);
if (v_isShared_4253_ == 0)
{
lean_ctor_set(v___x_4252_, 1, v___y_4255_);
lean_ctor_set(v___x_4252_, 0, v___x_4262_);
v___x_4264_ = v___x_4252_;
goto v_reusejp_4263_;
}
else
{
lean_object* v_reuseFailAlloc_4265_; 
v_reuseFailAlloc_4265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4265_, 0, v___x_4262_);
lean_ctor_set(v_reuseFailAlloc_4265_, 1, v___y_4255_);
v___x_4264_ = v_reuseFailAlloc_4265_;
goto v_reusejp_4263_;
}
v_reusejp_4263_:
{
return v___x_4264_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy(lean_object* v_00_u03b1_4274_, lean_object* v_d_4275_){
_start:
{
lean_object* v___x_4276_; 
v___x_4276_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_d_4275_);
return v___x_4276_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0(lean_object* v_00_u03b1_4277_, size_t v_sz_4278_, size_t v_i_4279_, lean_object* v_bs_4280_){
_start:
{
lean_object* v___x_4281_; 
v___x_4281_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(v_sz_4278_, v_i_4279_, v_bs_4280_);
return v___x_4281_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___boxed(lean_object* v_00_u03b1_4282_, lean_object* v_sz_4283_, lean_object* v_i_4284_, lean_object* v_bs_4285_){
_start:
{
size_t v_sz_boxed_4286_; size_t v_i_boxed_4287_; lean_object* v_res_4288_; 
v_sz_boxed_4286_ = lean_unbox_usize(v_sz_4283_);
lean_dec(v_sz_4283_);
v_i_boxed_4287_ = lean_unbox_usize(v_i_4284_);
lean_dec(v_i_4284_);
v_res_4288_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0(v_00_u03b1_4282_, v_sz_boxed_4286_, v_i_boxed_4287_, v_bs_4285_);
return v_res_4288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___lam__0(lean_object* v_y_4289_, lean_object* v_x_4290_){
_start:
{
lean_object* v___x_4291_; 
v___x_4291_ = l_Array_append___redArg(v_x_4290_, v_y_4289_);
return v___x_4291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___lam__0___boxed(lean_object* v_y_4292_, lean_object* v_x_4293_){
_start:
{
lean_object* v_res_4294_; 
v_res_4294_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___lam__0(v_y_4292_, v_x_4293_);
lean_dec_ref(v_y_4292_);
return v_res_4294_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4295_; 
v___x_4295_ = l_Array_instInhabited___redArg();
return v___x_4295_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(lean_object* v_tries_4296_, lean_object* v_snd_4297_, lean_object* v_x_4298_, lean_object* v_x_4299_){
_start:
{
if (lean_obj_tag(v_x_4299_) == 0)
{
lean_dec_ref(v_snd_4297_);
return v_x_4298_;
}
else
{
lean_object* v_key_4300_; lean_object* v_value_4301_; lean_object* v_tail_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; 
v_key_4300_ = lean_ctor_get(v_x_4299_, 0);
lean_inc(v_key_4300_);
v_value_4301_ = lean_ctor_get(v_x_4299_, 1);
lean_inc(v_value_4301_);
v_tail_4302_ = lean_ctor_get(v_x_4299_, 2);
lean_inc(v_tail_4302_);
lean_dec_ref_known(v_x_4299_, 3);
v___x_4303_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0);
v___x_4304_ = lean_array_get_borrowed(v___x_4303_, v_tries_4296_, v_value_4301_);
lean_dec(v_value_4301_);
lean_inc_ref(v_snd_4297_);
lean_inc(v___x_4304_);
v___x_4305_ = lean_apply_1(v_snd_4297_, v___x_4304_);
v___x_4306_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(v_x_4298_, v_key_4300_, v___x_4305_);
v_x_4298_ = v___x_4306_;
v_x_4299_ = v_tail_4302_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___boxed(lean_object* v_tries_4308_, lean_object* v_snd_4309_, lean_object* v_x_4310_, lean_object* v_x_4311_){
_start:
{
lean_object* v_res_4312_; 
v_res_4312_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(v_tries_4308_, v_snd_4309_, v_x_4310_, v_x_4311_);
lean_dec_ref(v_tries_4308_);
return v_res_4312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(lean_object* v_tries_4313_, lean_object* v_snd_4314_, lean_object* v_as_4315_, size_t v_i_4316_, size_t v_stop_4317_, lean_object* v_b_4318_){
_start:
{
uint8_t v___x_4319_; 
v___x_4319_ = lean_usize_dec_eq(v_i_4316_, v_stop_4317_);
if (v___x_4319_ == 0)
{
lean_object* v___x_4320_; lean_object* v___x_4321_; size_t v___x_4322_; size_t v___x_4323_; 
v___x_4320_ = lean_array_uget_borrowed(v_as_4315_, v_i_4316_);
lean_inc(v___x_4320_);
lean_inc_ref(v_snd_4314_);
v___x_4321_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(v_tries_4313_, v_snd_4314_, v_b_4318_, v___x_4320_);
v___x_4322_ = ((size_t)1ULL);
v___x_4323_ = lean_usize_add(v_i_4316_, v___x_4322_);
v_i_4316_ = v___x_4323_;
v_b_4318_ = v___x_4321_;
goto _start;
}
else
{
lean_dec_ref(v_snd_4314_);
return v_b_4318_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg___boxed(lean_object* v_tries_4325_, lean_object* v_snd_4326_, lean_object* v_as_4327_, lean_object* v_i_4328_, lean_object* v_stop_4329_, lean_object* v_b_4330_){
_start:
{
size_t v_i_boxed_4331_; size_t v_stop_boxed_4332_; lean_object* v_res_4333_; 
v_i_boxed_4331_ = lean_unbox_usize(v_i_4328_);
lean_dec(v_i_4328_);
v_stop_boxed_4332_ = lean_unbox_usize(v_stop_4329_);
lean_dec(v_stop_4329_);
v_res_4333_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(v_tries_4325_, v_snd_4326_, v_as_4327_, v_i_boxed_4331_, v_stop_boxed_4332_, v_b_4330_);
lean_dec_ref(v_as_4327_);
lean_dec_ref(v_tries_4325_);
return v_res_4333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg(lean_object* v_x_4336_, lean_object* v_y_4337_){
_start:
{
lean_object* v_fst_4339_; lean_object* v_buckets_4340_; lean_object* v_tries_4341_; lean_object* v_snd_4342_; lean_object* v_roots_4349_; lean_object* v_roots_4350_; lean_object* v_tries_4351_; lean_object* v_size_4352_; lean_object* v_buckets_4353_; lean_object* v_tries_4354_; lean_object* v_size_4355_; lean_object* v_buckets_4356_; uint8_t v___x_4357_; 
v_roots_4349_ = lean_ctor_get(v_y_4337_, 0);
v_roots_4350_ = lean_ctor_get(v_x_4336_, 0);
v_tries_4351_ = lean_ctor_get(v_y_4337_, 1);
v_size_4352_ = lean_ctor_get(v_roots_4349_, 0);
v_buckets_4353_ = lean_ctor_get(v_roots_4349_, 1);
v_tries_4354_ = lean_ctor_get(v_x_4336_, 1);
v_size_4355_ = lean_ctor_get(v_roots_4350_, 0);
v_buckets_4356_ = lean_ctor_get(v_roots_4350_, 1);
v___x_4357_ = lean_nat_dec_le(v_size_4352_, v_size_4355_);
if (v___x_4357_ == 0)
{
lean_object* v___f_4358_; 
lean_inc_ref(v_buckets_4356_);
lean_inc_ref(v_tries_4354_);
lean_dec_ref(v_x_4336_);
v___f_4358_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___closed__0));
v_fst_4339_ = v_y_4337_;
v_buckets_4340_ = v_buckets_4356_;
v_tries_4341_ = v_tries_4354_;
v_snd_4342_ = v___f_4358_;
goto v___jp_4338_;
}
else
{
lean_object* v___f_4359_; 
lean_inc_ref(v_buckets_4353_);
lean_inc_ref(v_tries_4351_);
lean_dec_ref(v_y_4337_);
v___f_4359_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___closed__1));
v_fst_4339_ = v_x_4336_;
v_buckets_4340_ = v_buckets_4353_;
v_tries_4341_ = v_tries_4351_;
v_snd_4342_ = v___f_4359_;
goto v___jp_4338_;
}
v___jp_4338_:
{
lean_object* v___x_4343_; lean_object* v___x_4344_; uint8_t v___x_4345_; 
v___x_4343_ = lean_unsigned_to_nat(0u);
v___x_4344_ = lean_array_get_size(v_buckets_4340_);
v___x_4345_ = lean_nat_dec_lt(v___x_4343_, v___x_4344_);
if (v___x_4345_ == 0)
{
lean_dec_ref(v_tries_4341_);
lean_dec_ref(v_buckets_4340_);
return v_fst_4339_;
}
else
{
size_t v___x_4346_; size_t v___x_4347_; lean_object* v___x_4348_; 
v___x_4346_ = ((size_t)0ULL);
v___x_4347_ = lean_usize_of_nat(v___x_4344_);
lean_inc_ref(v_snd_4342_);
v___x_4348_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(v_tries_4341_, v_snd_4342_, v_buckets_4340_, v___x_4346_, v___x_4347_, v_fst_4339_);
lean_dec_ref(v_buckets_4340_);
lean_dec_ref(v_tries_4341_);
return v___x_4348_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append(lean_object* v_00_u03b1_4360_, lean_object* v_x_4361_, lean_object* v_y_4362_){
_start:
{
lean_object* v___x_4363_; 
v___x_4363_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg(v_x_4361_, v_y_4362_);
return v___x_4363_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0(lean_object* v_00_u03b1_4364_, lean_object* v_tries_4365_, lean_object* v_snd_4366_, lean_object* v_x_4367_, lean_object* v_x_4368_){
_start:
{
lean_object* v___x_4369_; 
v___x_4369_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(v_tries_4365_, v_snd_4366_, v_x_4367_, v_x_4368_);
return v___x_4369_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___boxed(lean_object* v_00_u03b1_4370_, lean_object* v_tries_4371_, lean_object* v_snd_4372_, lean_object* v_x_4373_, lean_object* v_x_4374_){
_start:
{
lean_object* v_res_4375_; 
v_res_4375_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0(v_00_u03b1_4370_, v_tries_4371_, v_snd_4372_, v_x_4373_, v_x_4374_);
lean_dec_ref(v_tries_4371_);
return v_res_4375_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1(lean_object* v_00_u03b1_4376_, lean_object* v_tries_4377_, lean_object* v_snd_4378_, lean_object* v_as_4379_, size_t v_i_4380_, size_t v_stop_4381_, lean_object* v_b_4382_){
_start:
{
lean_object* v___x_4383_; 
v___x_4383_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(v_tries_4377_, v_snd_4378_, v_as_4379_, v_i_4380_, v_stop_4381_, v_b_4382_);
return v___x_4383_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___boxed(lean_object* v_00_u03b1_4384_, lean_object* v_tries_4385_, lean_object* v_snd_4386_, lean_object* v_as_4387_, lean_object* v_i_4388_, lean_object* v_stop_4389_, lean_object* v_b_4390_){
_start:
{
size_t v_i_boxed_4391_; size_t v_stop_boxed_4392_; lean_object* v_res_4393_; 
v_i_boxed_4391_ = lean_unbox_usize(v_i_4388_);
lean_dec(v_i_4388_);
v_stop_boxed_4392_ = lean_unbox_usize(v_stop_4389_);
lean_dec(v_stop_4389_);
v_res_4393_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1(v_00_u03b1_4384_, v_tries_4385_, v_snd_4386_, v_as_4387_, v_i_boxed_4391_, v_stop_boxed_4392_, v_b_4390_);
lean_dec_ref(v_as_4387_);
lean_dec_ref(v_tries_4385_);
return v_res_4393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend___redArg(){
_start:
{
lean_object* v___x_4396_; 
v___x_4396_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend___redArg___closed__0));
return v___x_4396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend___redArg___boxed(lean_object* v___dummy_4397_){
_start:
{
lean_object* v_res_4398_; 
v_res_4398_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend___redArg();
return v_res_4398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend(lean_object* v_00_u03b1_4399_){
_start:
{
lean_object* v___x_4400_; 
v___x_4400_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend___redArg___closed__0));
return v___x_4400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(lean_object* v_expr_4401_, lean_object* v_value_4402_, lean_object* v_a_4403_, lean_object* v_a_4404_, lean_object* v_a_4405_, lean_object* v_a_4406_){
_start:
{
lean_object* v_lctx_4408_; lean_object* v_localInstances_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; 
v_lctx_4408_ = lean_ctor_get(v_a_4403_, 2);
v_localInstances_4409_ = lean_ctor_get(v_a_4403_, 3);
lean_inc_ref(v_localInstances_4409_);
lean_inc_ref(v_lctx_4408_);
v___x_4410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4410_, 0, v_lctx_4408_);
lean_ctor_set(v___x_4410_, 1, v_localInstances_4409_);
v___x_4411_ = l_Lean_Meta_LazyDiscrTree_rootKey(v_expr_4401_, v_a_4403_, v_a_4404_, v_a_4405_, v_a_4406_);
if (lean_obj_tag(v___x_4411_) == 0)
{
lean_object* v_a_4412_; lean_object* v___x_4414_; uint8_t v_isShared_4415_; uint8_t v_isSharedCheck_4430_; 
v_a_4412_ = lean_ctor_get(v___x_4411_, 0);
v_isSharedCheck_4430_ = !lean_is_exclusive(v___x_4411_);
if (v_isSharedCheck_4430_ == 0)
{
v___x_4414_ = v___x_4411_;
v_isShared_4415_ = v_isSharedCheck_4430_;
goto v_resetjp_4413_;
}
else
{
lean_inc(v_a_4412_);
lean_dec(v___x_4411_);
v___x_4414_ = lean_box(0);
v_isShared_4415_ = v_isSharedCheck_4430_;
goto v_resetjp_4413_;
}
v_resetjp_4413_:
{
lean_object* v_fst_4416_; lean_object* v_snd_4417_; lean_object* v___x_4419_; uint8_t v_isShared_4420_; uint8_t v_isSharedCheck_4429_; 
v_fst_4416_ = lean_ctor_get(v_a_4412_, 0);
v_snd_4417_ = lean_ctor_get(v_a_4412_, 1);
v_isSharedCheck_4429_ = !lean_is_exclusive(v_a_4412_);
if (v_isSharedCheck_4429_ == 0)
{
v___x_4419_ = v_a_4412_;
v_isShared_4420_ = v_isSharedCheck_4429_;
goto v_resetjp_4418_;
}
else
{
lean_inc(v_snd_4417_);
lean_inc(v_fst_4416_);
lean_dec(v_a_4412_);
v___x_4419_ = lean_box(0);
v_isShared_4420_ = v_isSharedCheck_4429_;
goto v_resetjp_4418_;
}
v_resetjp_4418_:
{
lean_object* v___x_4422_; 
if (v_isShared_4420_ == 0)
{
lean_ctor_set(v___x_4419_, 1, v_value_4402_);
lean_ctor_set(v___x_4419_, 0, v___x_4410_);
v___x_4422_ = v___x_4419_;
goto v_reusejp_4421_;
}
else
{
lean_object* v_reuseFailAlloc_4428_; 
v_reuseFailAlloc_4428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4428_, 0, v___x_4410_);
lean_ctor_set(v_reuseFailAlloc_4428_, 1, v_value_4402_);
v___x_4422_ = v_reuseFailAlloc_4428_;
goto v_reusejp_4421_;
}
v_reusejp_4421_:
{
lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4426_; 
v___x_4423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4423_, 0, v_snd_4417_);
lean_ctor_set(v___x_4423_, 1, v___x_4422_);
v___x_4424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4424_, 0, v_fst_4416_);
lean_ctor_set(v___x_4424_, 1, v___x_4423_);
if (v_isShared_4415_ == 0)
{
lean_ctor_set(v___x_4414_, 0, v___x_4424_);
v___x_4426_ = v___x_4414_;
goto v_reusejp_4425_;
}
else
{
lean_object* v_reuseFailAlloc_4427_; 
v_reuseFailAlloc_4427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4427_, 0, v___x_4424_);
v___x_4426_ = v_reuseFailAlloc_4427_;
goto v_reusejp_4425_;
}
v_reusejp_4425_:
{
return v___x_4426_;
}
}
}
}
}
else
{
lean_object* v_a_4431_; lean_object* v___x_4433_; uint8_t v_isShared_4434_; uint8_t v_isSharedCheck_4438_; 
lean_dec_ref_known(v___x_4410_, 2);
lean_dec(v_value_4402_);
v_a_4431_ = lean_ctor_get(v___x_4411_, 0);
v_isSharedCheck_4438_ = !lean_is_exclusive(v___x_4411_);
if (v_isSharedCheck_4438_ == 0)
{
v___x_4433_ = v___x_4411_;
v_isShared_4434_ = v_isSharedCheck_4438_;
goto v_resetjp_4432_;
}
else
{
lean_inc(v_a_4431_);
lean_dec(v___x_4411_);
v___x_4433_ = lean_box(0);
v_isShared_4434_ = v_isSharedCheck_4438_;
goto v_resetjp_4432_;
}
v_resetjp_4432_:
{
lean_object* v___x_4436_; 
if (v_isShared_4434_ == 0)
{
v___x_4436_ = v___x_4433_;
goto v_reusejp_4435_;
}
else
{
lean_object* v_reuseFailAlloc_4437_; 
v_reuseFailAlloc_4437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4437_, 0, v_a_4431_);
v___x_4436_ = v_reuseFailAlloc_4437_;
goto v_reusejp_4435_;
}
v_reusejp_4435_:
{
return v___x_4436_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg___boxed(lean_object* v_expr_4439_, lean_object* v_value_4440_, lean_object* v_a_4441_, lean_object* v_a_4442_, lean_object* v_a_4443_, lean_object* v_a_4444_, lean_object* v_a_4445_){
_start:
{
lean_object* v_res_4446_; 
v_res_4446_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(v_expr_4439_, v_value_4440_, v_a_4441_, v_a_4442_, v_a_4443_, v_a_4444_);
lean_dec(v_a_4444_);
lean_dec_ref(v_a_4443_);
lean_dec(v_a_4442_);
lean_dec_ref(v_a_4441_);
return v_res_4446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr(lean_object* v_00_u03b1_4447_, lean_object* v_expr_4448_, lean_object* v_value_4449_, lean_object* v_a_4450_, lean_object* v_a_4451_, lean_object* v_a_4452_, lean_object* v_a_4453_){
_start:
{
lean_object* v___x_4455_; 
v___x_4455_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(v_expr_4448_, v_value_4449_, v_a_4450_, v_a_4451_, v_a_4452_, v_a_4453_);
return v___x_4455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___boxed(lean_object* v_00_u03b1_4456_, lean_object* v_expr_4457_, lean_object* v_value_4458_, lean_object* v_a_4459_, lean_object* v_a_4460_, lean_object* v_a_4461_, lean_object* v_a_4462_, lean_object* v_a_4463_){
_start:
{
lean_object* v_res_4464_; 
v_res_4464_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr(v_00_u03b1_4456_, v_expr_4457_, v_value_4458_, v_a_4459_, v_a_4460_, v_a_4461_, v_a_4462_);
lean_dec(v_a_4462_);
lean_dec_ref(v_a_4461_);
lean_dec(v_a_4460_);
lean_dec_ref(v_a_4459_);
return v_res_4464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(lean_object* v_e_4465_, lean_object* v_idx_4466_, lean_object* v_value_4467_, lean_object* v_a_4468_, lean_object* v_a_4469_, lean_object* v_a_4470_, lean_object* v_a_4471_){
_start:
{
lean_object* v_entry_4473_; lean_object* v___x_4475_; uint8_t v_isShared_4476_; uint8_t v_isSharedCheck_4519_; 
v_entry_4473_ = lean_ctor_get(v_e_4465_, 1);
v_isSharedCheck_4519_ = !lean_is_exclusive(v_e_4465_);
if (v_isSharedCheck_4519_ == 0)
{
lean_object* v_unused_4520_; 
v_unused_4520_ = lean_ctor_get(v_e_4465_, 0);
lean_dec(v_unused_4520_);
v___x_4475_ = v_e_4465_;
v_isShared_4476_ = v_isSharedCheck_4519_;
goto v_resetjp_4474_;
}
else
{
lean_inc(v_entry_4473_);
lean_dec(v_e_4465_);
v___x_4475_ = lean_box(0);
v_isShared_4476_ = v_isSharedCheck_4519_;
goto v_resetjp_4474_;
}
v_resetjp_4474_:
{
lean_object* v_snd_4477_; lean_object* v_fst_4478_; lean_object* v_fst_4479_; lean_object* v___x_4481_; uint8_t v_isShared_4482_; uint8_t v_isSharedCheck_4517_; 
v_snd_4477_ = lean_ctor_get(v_entry_4473_, 1);
lean_inc(v_snd_4477_);
v_fst_4478_ = lean_ctor_get(v_entry_4473_, 0);
lean_inc(v_fst_4478_);
lean_dec_ref(v_entry_4473_);
v_fst_4479_ = lean_ctor_get(v_snd_4477_, 0);
v_isSharedCheck_4517_ = !lean_is_exclusive(v_snd_4477_);
if (v_isSharedCheck_4517_ == 0)
{
lean_object* v_unused_4518_; 
v_unused_4518_ = lean_ctor_get(v_snd_4477_, 1);
lean_dec(v_unused_4518_);
v___x_4481_ = v_snd_4477_;
v_isShared_4482_ = v_isSharedCheck_4517_;
goto v_resetjp_4480_;
}
else
{
lean_inc(v_fst_4479_);
lean_dec(v_snd_4477_);
v___x_4481_ = lean_box(0);
v_isShared_4482_ = v_isSharedCheck_4517_;
goto v_resetjp_4480_;
}
v_resetjp_4480_:
{
lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; 
v___x_4483_ = l_Lean_instInhabitedExpr;
v___x_4484_ = lean_array_get(v___x_4483_, v_fst_4478_, v_idx_4466_);
lean_dec(v_fst_4478_);
v___x_4485_ = l_Lean_Meta_LazyDiscrTree_rootKey(v___x_4484_, v_a_4468_, v_a_4469_, v_a_4470_, v_a_4471_);
if (lean_obj_tag(v___x_4485_) == 0)
{
lean_object* v_a_4486_; lean_object* v___x_4488_; uint8_t v_isShared_4489_; uint8_t v_isSharedCheck_4508_; 
v_a_4486_ = lean_ctor_get(v___x_4485_, 0);
v_isSharedCheck_4508_ = !lean_is_exclusive(v___x_4485_);
if (v_isSharedCheck_4508_ == 0)
{
v___x_4488_ = v___x_4485_;
v_isShared_4489_ = v_isSharedCheck_4508_;
goto v_resetjp_4487_;
}
else
{
lean_inc(v_a_4486_);
lean_dec(v___x_4485_);
v___x_4488_ = lean_box(0);
v_isShared_4489_ = v_isSharedCheck_4508_;
goto v_resetjp_4487_;
}
v_resetjp_4487_:
{
lean_object* v_fst_4490_; lean_object* v_snd_4491_; lean_object* v___x_4493_; uint8_t v_isShared_4494_; uint8_t v_isSharedCheck_4507_; 
v_fst_4490_ = lean_ctor_get(v_a_4486_, 0);
v_snd_4491_ = lean_ctor_get(v_a_4486_, 1);
v_isSharedCheck_4507_ = !lean_is_exclusive(v_a_4486_);
if (v_isSharedCheck_4507_ == 0)
{
v___x_4493_ = v_a_4486_;
v_isShared_4494_ = v_isSharedCheck_4507_;
goto v_resetjp_4492_;
}
else
{
lean_inc(v_snd_4491_);
lean_inc(v_fst_4490_);
lean_dec(v_a_4486_);
v___x_4493_ = lean_box(0);
v_isShared_4494_ = v_isSharedCheck_4507_;
goto v_resetjp_4492_;
}
v_resetjp_4492_:
{
lean_object* v___x_4496_; 
if (v_isShared_4494_ == 0)
{
lean_ctor_set(v___x_4493_, 1, v_value_4467_);
lean_ctor_set(v___x_4493_, 0, v_fst_4479_);
v___x_4496_ = v___x_4493_;
goto v_reusejp_4495_;
}
else
{
lean_object* v_reuseFailAlloc_4506_; 
v_reuseFailAlloc_4506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4506_, 0, v_fst_4479_);
lean_ctor_set(v_reuseFailAlloc_4506_, 1, v_value_4467_);
v___x_4496_ = v_reuseFailAlloc_4506_;
goto v_reusejp_4495_;
}
v_reusejp_4495_:
{
lean_object* v___x_4498_; 
if (v_isShared_4482_ == 0)
{
lean_ctor_set(v___x_4481_, 1, v___x_4496_);
lean_ctor_set(v___x_4481_, 0, v_snd_4491_);
v___x_4498_ = v___x_4481_;
goto v_reusejp_4497_;
}
else
{
lean_object* v_reuseFailAlloc_4505_; 
v_reuseFailAlloc_4505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4505_, 0, v_snd_4491_);
lean_ctor_set(v_reuseFailAlloc_4505_, 1, v___x_4496_);
v___x_4498_ = v_reuseFailAlloc_4505_;
goto v_reusejp_4497_;
}
v_reusejp_4497_:
{
lean_object* v___x_4500_; 
if (v_isShared_4476_ == 0)
{
lean_ctor_set(v___x_4475_, 1, v___x_4498_);
lean_ctor_set(v___x_4475_, 0, v_fst_4490_);
v___x_4500_ = v___x_4475_;
goto v_reusejp_4499_;
}
else
{
lean_object* v_reuseFailAlloc_4504_; 
v_reuseFailAlloc_4504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4504_, 0, v_fst_4490_);
lean_ctor_set(v_reuseFailAlloc_4504_, 1, v___x_4498_);
v___x_4500_ = v_reuseFailAlloc_4504_;
goto v_reusejp_4499_;
}
v_reusejp_4499_:
{
lean_object* v___x_4502_; 
if (v_isShared_4489_ == 0)
{
lean_ctor_set(v___x_4488_, 0, v___x_4500_);
v___x_4502_ = v___x_4488_;
goto v_reusejp_4501_;
}
else
{
lean_object* v_reuseFailAlloc_4503_; 
v_reuseFailAlloc_4503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4503_, 0, v___x_4500_);
v___x_4502_ = v_reuseFailAlloc_4503_;
goto v_reusejp_4501_;
}
v_reusejp_4501_:
{
return v___x_4502_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4509_; lean_object* v___x_4511_; uint8_t v_isShared_4512_; uint8_t v_isSharedCheck_4516_; 
lean_del_object(v___x_4481_);
lean_dec(v_fst_4479_);
lean_del_object(v___x_4475_);
lean_dec(v_value_4467_);
v_a_4509_ = lean_ctor_get(v___x_4485_, 0);
v_isSharedCheck_4516_ = !lean_is_exclusive(v___x_4485_);
if (v_isSharedCheck_4516_ == 0)
{
v___x_4511_ = v___x_4485_;
v_isShared_4512_ = v_isSharedCheck_4516_;
goto v_resetjp_4510_;
}
else
{
lean_inc(v_a_4509_);
lean_dec(v___x_4485_);
v___x_4511_ = lean_box(0);
v_isShared_4512_ = v_isSharedCheck_4516_;
goto v_resetjp_4510_;
}
v_resetjp_4510_:
{
lean_object* v___x_4514_; 
if (v_isShared_4512_ == 0)
{
v___x_4514_ = v___x_4511_;
goto v_reusejp_4513_;
}
else
{
lean_object* v_reuseFailAlloc_4515_; 
v_reuseFailAlloc_4515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4515_, 0, v_a_4509_);
v___x_4514_ = v_reuseFailAlloc_4515_;
goto v_reusejp_4513_;
}
v_reusejp_4513_:
{
return v___x_4514_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg___boxed(lean_object* v_e_4521_, lean_object* v_idx_4522_, lean_object* v_value_4523_, lean_object* v_a_4524_, lean_object* v_a_4525_, lean_object* v_a_4526_, lean_object* v_a_4527_, lean_object* v_a_4528_){
_start:
{
lean_object* v_res_4529_; 
v_res_4529_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(v_e_4521_, v_idx_4522_, v_value_4523_, v_a_4524_, v_a_4525_, v_a_4526_, v_a_4527_);
lean_dec(v_a_4527_);
lean_dec_ref(v_a_4526_);
lean_dec(v_a_4525_);
lean_dec_ref(v_a_4524_);
lean_dec(v_idx_4522_);
return v_res_4529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry(lean_object* v_00_u03b1_4530_, lean_object* v_e_4531_, lean_object* v_idx_4532_, lean_object* v_value_4533_, lean_object* v_a_4534_, lean_object* v_a_4535_, lean_object* v_a_4536_, lean_object* v_a_4537_){
_start:
{
lean_object* v___x_4539_; 
v___x_4539_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(v_e_4531_, v_idx_4532_, v_value_4533_, v_a_4534_, v_a_4535_, v_a_4536_, v_a_4537_);
return v___x_4539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___boxed(lean_object* v_00_u03b1_4540_, lean_object* v_e_4541_, lean_object* v_idx_4542_, lean_object* v_value_4543_, lean_object* v_a_4544_, lean_object* v_a_4545_, lean_object* v_a_4546_, lean_object* v_a_4547_, lean_object* v_a_4548_){
_start:
{
lean_object* v_res_4549_; 
v_res_4549_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry(v_00_u03b1_4540_, v_e_4541_, v_idx_4542_, v_value_4543_, v_a_4544_, v_a_4545_, v_a_4546_, v_a_4547_);
lean_dec(v_a_4547_);
lean_dec_ref(v_a_4546_);
lean_dec(v_a_4545_);
lean_dec_ref(v_a_4544_);
lean_dec(v_idx_4542_);
return v_res_4549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_ImportData_new(){
_start:
{
lean_object* v___x_4553_; lean_object* v___x_4554_; 
v___x_4553_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_ImportData_new___closed__0));
v___x_4554_ = lean_st_mk_ref(v___x_4553_);
return v___x_4554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_ImportData_new___boxed(lean_object* v_a_4555_){
_start:
{
lean_object* v_res_4556_; 
v_res_4556_ = l_Lean_Meta_LazyDiscrTree_ImportData_new();
return v_res_4556_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0(void){
_start:
{
lean_object* v___x_4557_; 
v___x_4557_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_4557_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1(void){
_start:
{
lean_object* v___x_4558_; lean_object* v___x_4559_; 
v___x_4558_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0);
v___x_4559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4559_, 0, v___x_4558_);
return v___x_4559_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2(void){
_start:
{
lean_object* v___x_4560_; lean_object* v___x_4561_; 
v___x_4560_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1);
v___x_4561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4561_, 0, v___x_4560_);
lean_ctor_set(v___x_4561_, 1, v___x_4560_);
return v___x_4561_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3(void){
_start:
{
lean_object* v___x_4562_; lean_object* v___x_4563_; 
v___x_4562_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1);
v___x_4563_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4563_, 0, v___x_4562_);
lean_ctor_set(v___x_4563_, 1, v___x_4562_);
lean_ctor_set(v___x_4563_, 2, v___x_4562_);
lean_ctor_set(v___x_4563_, 3, v___x_4562_);
lean_ctor_set(v___x_4563_, 4, v___x_4562_);
lean_ctor_set(v___x_4563_, 5, v___x_4562_);
return v___x_4563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Cache_empty(lean_object* v_ngen_4564_){
_start:
{
lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; 
v___x_4565_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2);
v___x_4566_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3);
v___x_4567_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4567_, 0, v_ngen_4564_);
lean_ctor_set(v___x_4567_, 1, v___x_4565_);
lean_ctor_set(v___x_4567_, 2, v___x_4566_);
return v___x_4567_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName(lean_object* v_env_4568_, lean_object* v_declName_4569_){
_start:
{
uint8_t v___x_4570_; 
v___x_4570_ = l_Lean_isPrivateName(v_declName_4569_);
if (v___x_4570_ == 0)
{
return v___x_4570_;
}
else
{
lean_object* v___x_4571_; 
v___x_4571_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4568_, v_declName_4569_);
if (lean_obj_tag(v___x_4571_) == 0)
{
return v___x_4570_;
}
else
{
lean_object* v_val_4572_; lean_object* v___x_4573_; uint8_t v_isModule_4574_; lean_object* v_modules_4575_; uint8_t v___x_4576_; 
v_val_4572_ = lean_ctor_get(v___x_4571_, 0);
lean_inc(v_val_4572_);
lean_dec_ref_known(v___x_4571_, 1);
v___x_4573_ = l_Lean_Environment_header(v_env_4568_);
v_isModule_4574_ = lean_ctor_get_uint8(v___x_4573_, sizeof(void*)*7 + 4);
v_modules_4575_ = lean_ctor_get(v___x_4573_, 3);
lean_inc_ref(v_modules_4575_);
lean_dec_ref(v___x_4573_);
v___x_4576_ = 0;
if (v_isModule_4574_ == 0)
{
lean_dec_ref(v_modules_4575_);
lean_dec(v_val_4572_);
return v___x_4576_;
}
else
{
lean_object* v___x_4577_; uint8_t v___x_4578_; 
v___x_4577_ = lean_array_get_size(v_modules_4575_);
v___x_4578_ = lean_nat_dec_lt(v_val_4572_, v___x_4577_);
if (v___x_4578_ == 0)
{
lean_dec_ref(v_modules_4575_);
lean_dec(v_val_4572_);
return v___x_4576_;
}
else
{
lean_object* v___x_4579_; lean_object* v_toImport_4580_; uint8_t v_importAll_4581_; 
v___x_4579_ = lean_array_fget(v_modules_4575_, v_val_4572_);
lean_dec(v_val_4572_);
lean_dec_ref(v_modules_4575_);
v_toImport_4580_ = lean_ctor_get(v___x_4579_, 0);
lean_inc_ref(v_toImport_4580_);
lean_dec(v___x_4579_);
v_importAll_4581_ = lean_ctor_get_uint8(v_toImport_4580_, sizeof(void*)*1);
lean_dec_ref(v_toImport_4580_);
return v_importAll_4581_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName___boxed(lean_object* v_env_4582_, lean_object* v_declName_4583_){
_start:
{
uint8_t v_res_4584_; lean_object* v_r_4585_; 
v_res_4584_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName(v_env_4582_, v_declName_4583_);
lean_dec(v_declName_4583_);
lean_dec_ref(v_env_4582_);
v_r_4585_ = lean_box(v_res_4584_);
return v_r_4585_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_LazyDiscrTree_blacklistInsertion(lean_object* v_env_4591_, lean_object* v_declName_4592_){
_start:
{
uint8_t v___x_4593_; 
lean_inc(v_declName_4592_);
lean_inc_ref(v_env_4591_);
v___x_4593_ = l_Lean_Meta_allowCompletion(v_env_4591_, v_declName_4592_);
if (v___x_4593_ == 0)
{
uint8_t v___x_4594_; 
lean_dec(v_declName_4592_);
lean_dec_ref(v_env_4591_);
v___x_4594_ = 1;
return v___x_4594_;
}
else
{
lean_object* v___x_4595_; uint8_t v___x_4596_; uint8_t v___y_4606_; 
v___x_4595_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__1));
v___x_4596_ = lean_name_eq(v_declName_4592_, v___x_4595_);
if (v___x_4596_ == 0)
{
uint8_t v___x_4607_; 
lean_inc(v_declName_4592_);
v___x_4607_ = l_Lean_Name_isInternalDetail(v_declName_4592_);
if (v___x_4607_ == 0)
{
lean_dec_ref(v_env_4591_);
v___y_4606_ = v___x_4607_;
goto v___jp_4605_;
}
else
{
uint8_t v___x_4608_; 
v___x_4608_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName(v_env_4591_, v_declName_4592_);
lean_dec_ref(v_env_4591_);
if (v___x_4608_ == 0)
{
v___y_4606_ = v___x_4607_;
goto v___jp_4605_;
}
else
{
goto v___jp_4601_;
}
}
}
else
{
lean_dec(v_declName_4592_);
lean_dec_ref(v_env_4591_);
return v___x_4596_;
}
v___jp_4597_:
{
if (lean_obj_tag(v_declName_4592_) == 1)
{
lean_object* v_str_4598_; lean_object* v___x_4599_; uint8_t v___x_4600_; 
v_str_4598_ = lean_ctor_get(v_declName_4592_, 1);
lean_inc_ref(v_str_4598_);
lean_dec_ref_known(v_declName_4592_, 2);
v___x_4599_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__2));
v___x_4600_ = lean_string_dec_eq(v_str_4598_, v___x_4599_);
lean_dec_ref(v_str_4598_);
return v___x_4600_;
}
else
{
lean_dec(v_declName_4592_);
return v___x_4596_;
}
}
v___jp_4601_:
{
if (lean_obj_tag(v_declName_4592_) == 1)
{
lean_object* v_str_4602_; lean_object* v___x_4603_; uint8_t v___x_4604_; 
v_str_4602_ = lean_ctor_get(v_declName_4592_, 1);
v___x_4603_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__3));
v___x_4604_ = lean_string_dec_eq(v_str_4602_, v___x_4603_);
if (v___x_4604_ == 0)
{
goto v___jp_4597_;
}
else
{
lean_dec_ref_known(v_declName_4592_, 2);
return v___x_4604_;
}
}
else
{
goto v___jp_4597_;
}
}
v___jp_4605_:
{
if (v___y_4606_ == 0)
{
goto v___jp_4601_;
}
else
{
lean_dec(v_declName_4592_);
return v___y_4606_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_blacklistInsertion___boxed(lean_object* v_env_4609_, lean_object* v_declName_4610_){
_start:
{
uint8_t v_res_4611_; lean_object* v_r_4612_; 
v_res_4611_ = l_Lean_Meta_LazyDiscrTree_blacklistInsertion(v_env_4609_, v_declName_4610_);
v_r_4612_ = lean_box(v_res_4611_);
return v_r_4612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(lean_object* v_opts_4613_, lean_object* v_opt_4614_){
_start:
{
lean_object* v_name_4615_; lean_object* v_defValue_4616_; lean_object* v_map_4617_; lean_object* v___x_4618_; 
v_name_4615_ = lean_ctor_get(v_opt_4614_, 0);
v_defValue_4616_ = lean_ctor_get(v_opt_4614_, 1);
v_map_4617_ = lean_ctor_get(v_opts_4613_, 0);
v___x_4618_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4617_, v_name_4615_);
if (lean_obj_tag(v___x_4618_) == 0)
{
lean_inc(v_defValue_4616_);
return v_defValue_4616_;
}
else
{
lean_object* v_val_4619_; 
v_val_4619_ = lean_ctor_get(v___x_4618_, 0);
lean_inc(v_val_4619_);
lean_dec_ref_known(v___x_4618_, 1);
if (lean_obj_tag(v_val_4619_) == 3)
{
lean_object* v_v_4620_; 
v_v_4620_ = lean_ctor_get(v_val_4619_, 0);
lean_inc(v_v_4620_);
lean_dec_ref_known(v_val_4619_, 1);
return v_v_4620_;
}
else
{
lean_dec(v_val_4619_);
lean_inc(v_defValue_4616_);
return v_defValue_4616_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0___boxed(lean_object* v_opts_4621_, lean_object* v_opt_4622_){
_start:
{
lean_object* v_res_4623_; 
v_res_4623_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(v_opts_4621_, v_opt_4622_);
lean_dec_ref(v_opt_4622_);
lean_dec_ref(v_opts_4621_);
return v_res_4623_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1___redArg(lean_object* v_as_4624_, size_t v_i_4625_, size_t v_stop_4626_, lean_object* v_b_4627_){
_start:
{
uint8_t v___x_4628_; 
v___x_4628_ = lean_usize_dec_eq(v_i_4625_, v_stop_4626_);
if (v___x_4628_ == 0)
{
lean_object* v___x_4629_; lean_object* v_key_4630_; lean_object* v_entry_4631_; lean_object* v___x_4632_; size_t v___x_4633_; size_t v___x_4634_; 
v___x_4629_ = lean_array_uget_borrowed(v_as_4624_, v_i_4625_);
v_key_4630_ = lean_ctor_get(v___x_4629_, 0);
v_entry_4631_ = lean_ctor_get(v___x_4629_, 1);
lean_inc_ref(v_entry_4631_);
lean_inc(v_key_4630_);
v___x_4632_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg(v_b_4627_, v_key_4630_, v_entry_4631_);
v___x_4633_ = ((size_t)1ULL);
v___x_4634_ = lean_usize_add(v_i_4625_, v___x_4633_);
v_i_4625_ = v___x_4634_;
v_b_4627_ = v___x_4632_;
goto _start;
}
else
{
return v_b_4627_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1___redArg___boxed(lean_object* v_as_4636_, lean_object* v_i_4637_, lean_object* v_stop_4638_, lean_object* v_b_4639_){
_start:
{
size_t v_i_boxed_4640_; size_t v_stop_boxed_4641_; lean_object* v_res_4642_; 
v_i_boxed_4640_ = lean_unbox_usize(v_i_4637_);
lean_dec(v_i_4637_);
v_stop_boxed_4641_ = lean_unbox_usize(v_stop_4638_);
lean_dec(v_stop_4638_);
v_res_4642_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1___redArg(v_as_4636_, v_i_boxed_4640_, v_stop_boxed_4641_, v_b_4639_);
lean_dec_ref(v_as_4636_);
return v_res_4642_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0(void){
_start:
{
lean_object* v___x_4643_; lean_object* v___x_4644_; 
v___x_4643_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0);
v___x_4644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4644_, 0, v___x_4643_);
return v___x_4644_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1(void){
_start:
{
lean_object* v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; 
v___x_4645_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0);
v___x_4646_ = lean_unsigned_to_nat(0u);
v___x_4647_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_4647_, 0, v___x_4646_);
lean_ctor_set(v___x_4647_, 1, v___x_4646_);
lean_ctor_set(v___x_4647_, 2, v___x_4646_);
lean_ctor_set(v___x_4647_, 3, v___x_4646_);
lean_ctor_set(v___x_4647_, 4, v___x_4645_);
lean_ctor_set(v___x_4647_, 5, v___x_4645_);
lean_ctor_set(v___x_4647_, 6, v___x_4645_);
lean_ctor_set(v___x_4647_, 7, v___x_4645_);
lean_ctor_set(v___x_4647_, 8, v___x_4645_);
lean_ctor_set(v___x_4647_, 9, v___x_4645_);
lean_ctor_set(v___x_4647_, 10, v___x_4645_);
return v___x_4647_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2(void){
_start:
{
lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; 
v___x_4648_ = lean_unsigned_to_nat(32u);
v___x_4649_ = lean_mk_empty_array_with_capacity(v___x_4648_);
v___x_4650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4650_, 0, v___x_4649_);
return v___x_4650_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3(void){
_start:
{
size_t v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; lean_object* v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; 
v___x_4651_ = ((size_t)5ULL);
v___x_4652_ = lean_unsigned_to_nat(0u);
v___x_4653_ = lean_unsigned_to_nat(32u);
v___x_4654_ = lean_mk_empty_array_with_capacity(v___x_4653_);
v___x_4655_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2);
v___x_4656_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4656_, 0, v___x_4655_);
lean_ctor_set(v___x_4656_, 1, v___x_4654_);
lean_ctor_set(v___x_4656_, 2, v___x_4652_);
lean_ctor_set(v___x_4656_, 3, v___x_4652_);
lean_ctor_set_usize(v___x_4656_, 4, v___x_4651_);
return v___x_4656_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4(void){
_start:
{
lean_object* v___x_4657_; lean_object* v___x_4658_; 
v___x_4657_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0);
v___x_4658_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4658_, 0, v___x_4657_);
lean_ctor_set(v___x_4658_, 1, v___x_4657_);
lean_ctor_set(v___x_4658_, 2, v___x_4657_);
lean_ctor_set(v___x_4658_, 3, v___x_4657_);
lean_ctor_set(v___x_4658_, 4, v___x_4657_);
return v___x_4658_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5(void){
_start:
{
lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; 
v___x_4659_ = lean_box(1);
v___x_4660_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3);
v___x_4661_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0);
v___x_4662_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4662_, 0, v___x_4661_);
lean_ctor_set(v___x_4662_, 1, v___x_4660_);
lean_ctor_set(v___x_4662_, 2, v___x_4659_);
return v___x_4662_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__7(void){
_start:
{
lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; 
v___x_4665_ = lean_unsigned_to_nat(1u);
v___x_4666_ = l_Lean_firstFrontendMacroScope;
v___x_4667_ = lean_nat_add(v___x_4666_, v___x_4665_);
return v___x_4667_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__9(void){
_start:
{
lean_object* v___x_4672_; uint64_t v___x_4673_; lean_object* v___x_4674_; 
v___x_4672_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3);
v___x_4673_ = 0ULL;
v___x_4674_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4674_, 0, v___x_4672_);
lean_ctor_set_uint64(v___x_4674_, sizeof(void*)*1, v___x_4673_);
return v___x_4674_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10(void){
_start:
{
lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; 
v___x_4675_ = l_Lean_NameSet_empty;
v___x_4676_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3);
v___x_4677_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4677_, 0, v___x_4676_);
lean_ctor_set(v___x_4677_, 1, v___x_4676_);
lean_ctor_set(v___x_4677_, 2, v___x_4675_);
return v___x_4677_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11(void){
_start:
{
lean_object* v___x_4678_; lean_object* v___x_4679_; uint8_t v___x_4680_; lean_object* v___x_4681_; 
v___x_4678_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3);
v___x_4679_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0);
v___x_4680_ = 1;
v___x_4681_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4681_, 0, v___x_4679_);
lean_ctor_set(v___x_4681_, 1, v___x_4679_);
lean_ctor_set(v___x_4681_, 2, v___x_4678_);
lean_ctor_set_uint8(v___x_4681_, sizeof(void*)*3, v___x_4680_);
return v___x_4681_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12(void){
_start:
{
lean_object* v___x_4682_; lean_object* v___x_4683_; 
v___x_4682_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0);
v___x_4683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4683_, 0, v___x_4682_);
lean_ctor_set(v___x_4683_, 1, v___x_4682_);
return v___x_4683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(lean_object* v_cctx_4684_, lean_object* v_env_4685_, lean_object* v_modName_4686_, lean_object* v_d_4687_, lean_object* v_cacheRef_4688_, lean_object* v_tree_4689_, lean_object* v_act_4690_, lean_object* v_c_4691_){
_start:
{
uint8_t v___x_4693_; 
lean_inc_ref(v_c_4691_);
v___x_4693_ = l_Lean_AsyncConstantInfo_isUnsafe(v_c_4691_);
if (v___x_4693_ == 0)
{
lean_object* v_name_4694_; uint8_t v___x_4695_; 
v_name_4694_ = lean_ctor_get(v_c_4691_, 0);
lean_inc_n(v_name_4694_, 2);
lean_inc_ref(v_env_4685_);
v___x_4695_ = l_Lean_Meta_LazyDiscrTree_blacklistInsertion(v_env_4685_, v_name_4694_);
if (v___x_4695_ == 0)
{
lean_object* v___x_4696_; uint8_t v___x_4697_; lean_object* v___x_4698_; lean_object* v_ngen_4699_; lean_object* v_core_4700_; lean_object* v_meta_4701_; lean_object* v___x_4703_; uint8_t v_isShared_4704_; uint8_t v_isSharedCheck_4824_; 
v___x_4696_ = lean_box(1);
v___x_4697_ = 1;
v___x_4698_ = lean_st_ref_get(v_cacheRef_4688_);
v_ngen_4699_ = lean_ctor_get(v___x_4698_, 0);
v_core_4700_ = lean_ctor_get(v___x_4698_, 1);
v_meta_4701_ = lean_ctor_get(v___x_4698_, 2);
v_isSharedCheck_4824_ = !lean_is_exclusive(v___x_4698_);
if (v_isSharedCheck_4824_ == 0)
{
v___x_4703_ = v___x_4698_;
v_isShared_4704_ = v_isSharedCheck_4824_;
goto v_resetjp_4702_;
}
else
{
lean_inc(v_meta_4701_);
lean_inc(v_core_4700_);
lean_inc(v_ngen_4699_);
lean_dec(v___x_4698_);
v___x_4703_ = lean_box(0);
v_isShared_4704_ = v_isSharedCheck_4824_;
goto v_resetjp_4702_;
}
v_resetjp_4702_:
{
lean_object* v___x_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; uint8_t v___x_4712_; uint8_t v___x_4713_; uint8_t v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; lean_object* v___x_4729_; lean_object* v_toCold_4730_; lean_object* v_currRecDepth_4731_; lean_object* v_ref_4732_; uint8_t v_suppressElabErrors_4733_; uint8_t v_isRecordingDeps_4734_; lean_object* v___x_4736_; uint8_t v_isShared_4737_; uint8_t v_isSharedCheck_4823_; 
v___x_4705_ = lean_unsigned_to_nat(0u);
v___x_4706_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4707_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3);
v___x_4708_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4709_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4709_, 0, v___x_4706_);
lean_ctor_set(v___x_4709_, 1, v_meta_4701_);
lean_ctor_set(v___x_4709_, 2, v___x_4696_);
lean_ctor_set(v___x_4709_, 3, v___x_4707_);
lean_ctor_set(v___x_4709_, 4, v___x_4708_);
lean_inc_ref(v_ngen_4699_);
v___x_4710_ = l_Lean_Meta_LazyDiscrTree_Cache_empty(v_ngen_4699_);
v___x_4711_ = lean_st_ref_swap(v_cacheRef_4688_, v___x_4710_);
lean_dec(v___x_4711_);
v___x_4712_ = 2;
v___x_4713_ = 0;
v___x_4714_ = 2;
v___x_4715_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_4715_, 0, v___x_4695_);
lean_ctor_set_uint8(v___x_4715_, 1, v___x_4695_);
lean_ctor_set_uint8(v___x_4715_, 2, v___x_4695_);
lean_ctor_set_uint8(v___x_4715_, 3, v___x_4695_);
lean_ctor_set_uint8(v___x_4715_, 4, v___x_4695_);
lean_ctor_set_uint8(v___x_4715_, 5, v___x_4697_);
lean_ctor_set_uint8(v___x_4715_, 6, v___x_4697_);
lean_ctor_set_uint8(v___x_4715_, 7, v___x_4695_);
lean_ctor_set_uint8(v___x_4715_, 8, v___x_4697_);
lean_ctor_set_uint8(v___x_4715_, 9, v___x_4712_);
lean_ctor_set_uint8(v___x_4715_, 10, v___x_4713_);
lean_ctor_set_uint8(v___x_4715_, 11, v___x_4697_);
lean_ctor_set_uint8(v___x_4715_, 12, v___x_4697_);
lean_ctor_set_uint8(v___x_4715_, 13, v___x_4697_);
lean_ctor_set_uint8(v___x_4715_, 14, v___x_4714_);
lean_ctor_set_uint8(v___x_4715_, 15, v___x_4697_);
lean_ctor_set_uint8(v___x_4715_, 16, v___x_4697_);
lean_ctor_set_uint8(v___x_4715_, 17, v___x_4697_);
lean_ctor_set_uint8(v___x_4715_, 18, v___x_4697_);
lean_ctor_set_uint8(v___x_4715_, 19, v___x_4695_);
v___x_4716_ = l_Lean_Meta_Config_toConfigWithKey(v___x_4715_);
v___x_4717_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5);
v___x_4718_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6));
v___x_4719_ = lean_box(0);
v___x_4720_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4720_, 0, v___x_4716_);
lean_ctor_set(v___x_4720_, 1, v___x_4696_);
lean_ctor_set(v___x_4720_, 2, v___x_4717_);
lean_ctor_set(v___x_4720_, 3, v___x_4718_);
lean_ctor_set(v___x_4720_, 4, v___x_4719_);
lean_ctor_set(v___x_4720_, 5, v___x_4705_);
lean_ctor_set(v___x_4720_, 6, v___x_4719_);
lean_ctor_set_uint8(v___x_4720_, sizeof(void*)*7, v___x_4695_);
lean_ctor_set_uint8(v___x_4720_, sizeof(void*)*7 + 1, v___x_4695_);
lean_ctor_set_uint8(v___x_4720_, sizeof(void*)*7 + 2, v___x_4695_);
lean_ctor_set_uint8(v___x_4720_, sizeof(void*)*7 + 3, v___x_4697_);
v___x_4721_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__7, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__7_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__7);
v___x_4722_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__8));
v___x_4723_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__9, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__9_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__9);
v___x_4724_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10);
v___x_4725_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11);
v___x_4726_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4726_, 0, v_env_4685_);
lean_ctor_set(v___x_4726_, 1, v___x_4721_);
lean_ctor_set(v___x_4726_, 2, v_ngen_4699_);
lean_ctor_set(v___x_4726_, 3, v___x_4722_);
lean_ctor_set(v___x_4726_, 4, v___x_4723_);
lean_ctor_set(v___x_4726_, 5, v_core_4700_);
lean_ctor_set(v___x_4726_, 6, v___x_4718_);
lean_ctor_set(v___x_4726_, 7, v___x_4724_);
lean_ctor_set(v___x_4726_, 8, v___x_4725_);
lean_ctor_set(v___x_4726_, 9, v___x_4718_);
v___x_4727_ = lean_st_mk_ref(v___x_4726_);
v___x_4728_ = l_Lean_inheritedTraceOptions;
v___x_4729_ = lean_st_ref_get(v___x_4728_);
v_toCold_4730_ = lean_ctor_get(v_cctx_4684_, 0);
v_currRecDepth_4731_ = lean_ctor_get(v_cctx_4684_, 1);
v_ref_4732_ = lean_ctor_get(v_cctx_4684_, 2);
v_suppressElabErrors_4733_ = lean_ctor_get_uint8(v_cctx_4684_, sizeof(void*)*3 + 2);
v_isRecordingDeps_4734_ = lean_ctor_get_uint8(v_cctx_4684_, sizeof(void*)*3 + 3);
v_isSharedCheck_4823_ = !lean_is_exclusive(v_cctx_4684_);
if (v_isSharedCheck_4823_ == 0)
{
v___x_4736_ = v_cctx_4684_;
v_isShared_4737_ = v_isSharedCheck_4823_;
goto v_resetjp_4735_;
}
else
{
lean_inc(v_ref_4732_);
lean_inc(v_currRecDepth_4731_);
lean_inc(v_toCold_4730_);
lean_dec(v_cctx_4684_);
v___x_4736_ = lean_box(0);
v_isShared_4737_ = v_isSharedCheck_4823_;
goto v_resetjp_4735_;
}
v_resetjp_4735_:
{
lean_object* v_fileName_4738_; lean_object* v_fileMap_4739_; lean_object* v_options_4740_; lean_object* v_currNamespace_4741_; lean_object* v_openDecls_4742_; lean_object* v_initHeartbeats_4743_; lean_object* v_maxHeartbeats_4744_; lean_object* v_quotContext_4745_; lean_object* v_currMacroScope_4746_; lean_object* v_cancelTk_x3f_4747_; lean_object* v___x_4749_; uint8_t v_isShared_4750_; uint8_t v_isSharedCheck_4820_; 
v_fileName_4738_ = lean_ctor_get(v_toCold_4730_, 0);
v_fileMap_4739_ = lean_ctor_get(v_toCold_4730_, 1);
v_options_4740_ = lean_ctor_get(v_toCold_4730_, 2);
v_currNamespace_4741_ = lean_ctor_get(v_toCold_4730_, 4);
v_openDecls_4742_ = lean_ctor_get(v_toCold_4730_, 5);
v_initHeartbeats_4743_ = lean_ctor_get(v_toCold_4730_, 6);
v_maxHeartbeats_4744_ = lean_ctor_get(v_toCold_4730_, 7);
v_quotContext_4745_ = lean_ctor_get(v_toCold_4730_, 8);
v_currMacroScope_4746_ = lean_ctor_get(v_toCold_4730_, 9);
v_cancelTk_x3f_4747_ = lean_ctor_get(v_toCold_4730_, 10);
v_isSharedCheck_4820_ = !lean_is_exclusive(v_toCold_4730_);
if (v_isSharedCheck_4820_ == 0)
{
lean_object* v_unused_4821_; lean_object* v_unused_4822_; 
v_unused_4821_ = lean_ctor_get(v_toCold_4730_, 11);
lean_dec(v_unused_4821_);
v_unused_4822_ = lean_ctor_get(v_toCold_4730_, 3);
lean_dec(v_unused_4822_);
v___x_4749_ = v_toCold_4730_;
v_isShared_4750_ = v_isSharedCheck_4820_;
goto v_resetjp_4748_;
}
else
{
lean_inc(v_cancelTk_x3f_4747_);
lean_inc(v_currMacroScope_4746_);
lean_inc(v_quotContext_4745_);
lean_inc(v_maxHeartbeats_4744_);
lean_inc(v_initHeartbeats_4743_);
lean_inc(v_openDecls_4742_);
lean_inc(v_currNamespace_4741_);
lean_inc(v_options_4740_);
lean_inc(v_fileMap_4739_);
lean_inc(v_fileName_4738_);
lean_dec(v_toCold_4730_);
v___x_4749_ = lean_box(0);
v_isShared_4750_ = v_isSharedCheck_4820_;
goto v_resetjp_4748_;
}
v_resetjp_4748_:
{
uint16_t v___x_4751_; lean_object* v___y_4753_; lean_object* v___x_4788_; uint8_t v___y_4790_; lean_object* v_env_4812_; uint8_t v___x_4813_; uint8_t v___y_4815_; uint16_t v___x_4816_; uint16_t v___x_4817_; uint16_t v___x_4818_; uint8_t v___x_4819_; 
v___x_4751_ = l_Lean_OptionFlags_ofOptions(v_options_4740_);
v___x_4788_ = lean_st_ref_get(v___x_4727_);
v_env_4812_ = lean_ctor_get(v___x_4788_, 0);
lean_inc_ref(v_env_4812_);
lean_dec(v___x_4788_);
v___x_4813_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4812_);
lean_dec_ref(v_env_4812_);
v___x_4816_ = 512;
v___x_4817_ = lean_uint16_land(v___x_4751_, v___x_4816_);
v___x_4818_ = 0;
v___x_4819_ = lean_uint16_dec_eq(v___x_4817_, v___x_4818_);
if (v___x_4819_ == 0)
{
v___y_4815_ = v___x_4697_;
goto v___jp_4814_;
}
else
{
if (v___x_4695_ == 0)
{
if (v___x_4813_ == 0)
{
lean_inc(v___x_4727_);
v___y_4753_ = v___x_4727_;
goto v___jp_4752_;
}
else
{
v___y_4790_ = v___x_4695_;
goto v___jp_4789_;
}
}
else
{
v___y_4815_ = v___x_4695_;
goto v___jp_4814_;
}
}
v___jp_4752_:
{
lean_object* v___x_4754_; lean_object* v___x_4755_; lean_object* v___x_4757_; 
v___x_4754_ = l_Lean_maxRecDepth;
v___x_4755_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(v_options_4740_, v___x_4754_);
if (v_isShared_4750_ == 0)
{
lean_ctor_set(v___x_4749_, 11, v___x_4729_);
lean_ctor_set(v___x_4749_, 3, v___x_4755_);
v___x_4757_ = v___x_4749_;
goto v_reusejp_4756_;
}
else
{
lean_object* v_reuseFailAlloc_4787_; 
v_reuseFailAlloc_4787_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_4787_, 0, v_fileName_4738_);
lean_ctor_set(v_reuseFailAlloc_4787_, 1, v_fileMap_4739_);
lean_ctor_set(v_reuseFailAlloc_4787_, 2, v_options_4740_);
lean_ctor_set(v_reuseFailAlloc_4787_, 3, v___x_4755_);
lean_ctor_set(v_reuseFailAlloc_4787_, 4, v_currNamespace_4741_);
lean_ctor_set(v_reuseFailAlloc_4787_, 5, v_openDecls_4742_);
lean_ctor_set(v_reuseFailAlloc_4787_, 6, v_initHeartbeats_4743_);
lean_ctor_set(v_reuseFailAlloc_4787_, 7, v_maxHeartbeats_4744_);
lean_ctor_set(v_reuseFailAlloc_4787_, 8, v_quotContext_4745_);
lean_ctor_set(v_reuseFailAlloc_4787_, 9, v_currMacroScope_4746_);
lean_ctor_set(v_reuseFailAlloc_4787_, 10, v_cancelTk_x3f_4747_);
lean_ctor_set(v_reuseFailAlloc_4787_, 11, v___x_4729_);
v___x_4757_ = v_reuseFailAlloc_4787_;
goto v_reusejp_4756_;
}
v_reusejp_4756_:
{
lean_object* v___x_4759_; 
if (v_isShared_4737_ == 0)
{
lean_ctor_set(v___x_4736_, 0, v___x_4757_);
v___x_4759_ = v___x_4736_;
goto v_reusejp_4758_;
}
else
{
lean_object* v_reuseFailAlloc_4786_; 
v_reuseFailAlloc_4786_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v_reuseFailAlloc_4786_, 0, v___x_4757_);
lean_ctor_set(v_reuseFailAlloc_4786_, 1, v_currRecDepth_4731_);
lean_ctor_set(v_reuseFailAlloc_4786_, 2, v_ref_4732_);
lean_ctor_set_uint8(v_reuseFailAlloc_4786_, sizeof(void*)*3 + 2, v_suppressElabErrors_4733_);
lean_ctor_set_uint8(v_reuseFailAlloc_4786_, sizeof(void*)*3 + 3, v_isRecordingDeps_4734_);
v___x_4759_ = v_reuseFailAlloc_4786_;
goto v_reusejp_4758_;
}
v_reusejp_4758_:
{
lean_object* v___x_4760_; lean_object* v___x_4761_; 
lean_ctor_set_uint16(v___x_4759_, sizeof(void*)*3, v___x_4751_);
v___x_4760_ = lean_st_mk_ref(v___x_4709_);
lean_inc(v___x_4760_);
lean_inc(v_name_4694_);
v___x_4761_ = lean_apply_7(v_act_4690_, v_name_4694_, v_c_4691_, v___x_4720_, v___x_4760_, v___x_4759_, v___y_4753_, lean_box(0));
if (lean_obj_tag(v___x_4761_) == 0)
{
lean_object* v_a_4762_; lean_object* v___x_4763_; lean_object* v___x_4764_; lean_object* v_ngen_4765_; lean_object* v_cache_4766_; lean_object* v_cache_4767_; lean_object* v___x_4769_; 
lean_dec(v_name_4694_);
lean_dec(v_modName_4686_);
v_a_4762_ = lean_ctor_get(v___x_4761_, 0);
lean_inc(v_a_4762_);
lean_dec_ref_known(v___x_4761_, 1);
v___x_4763_ = lean_st_ref_get(v___x_4760_);
lean_dec(v___x_4760_);
v___x_4764_ = lean_st_ref_get(v___x_4727_);
lean_dec(v___x_4727_);
v_ngen_4765_ = lean_ctor_get(v___x_4764_, 2);
lean_inc_ref(v_ngen_4765_);
v_cache_4766_ = lean_ctor_get(v___x_4764_, 5);
lean_inc_ref(v_cache_4766_);
lean_dec(v___x_4764_);
v_cache_4767_ = lean_ctor_get(v___x_4763_, 1);
lean_inc_ref(v_cache_4767_);
lean_dec(v___x_4763_);
if (v_isShared_4704_ == 0)
{
lean_ctor_set(v___x_4703_, 2, v_cache_4767_);
lean_ctor_set(v___x_4703_, 1, v_cache_4766_);
lean_ctor_set(v___x_4703_, 0, v_ngen_4765_);
v___x_4769_ = v___x_4703_;
goto v_reusejp_4768_;
}
else
{
lean_object* v_reuseFailAlloc_4780_; 
v_reuseFailAlloc_4780_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4780_, 0, v_ngen_4765_);
lean_ctor_set(v_reuseFailAlloc_4780_, 1, v_cache_4766_);
lean_ctor_set(v_reuseFailAlloc_4780_, 2, v_cache_4767_);
v___x_4769_ = v_reuseFailAlloc_4780_;
goto v_reusejp_4768_;
}
v_reusejp_4768_:
{
lean_object* v___x_4770_; lean_object* v___x_4771_; uint8_t v___x_4772_; 
v___x_4770_ = lean_st_ref_swap(v_cacheRef_4688_, v___x_4769_);
lean_dec(v___x_4770_);
v___x_4771_ = lean_array_get_size(v_a_4762_);
v___x_4772_ = lean_nat_dec_lt(v___x_4705_, v___x_4771_);
if (v___x_4772_ == 0)
{
lean_dec(v_a_4762_);
return v_tree_4689_;
}
else
{
uint8_t v___x_4773_; 
v___x_4773_ = lean_nat_dec_le(v___x_4771_, v___x_4771_);
if (v___x_4773_ == 0)
{
if (v___x_4772_ == 0)
{
lean_dec(v_a_4762_);
return v_tree_4689_;
}
else
{
size_t v___x_4774_; size_t v___x_4775_; lean_object* v___x_4776_; 
v___x_4774_ = ((size_t)0ULL);
v___x_4775_ = lean_usize_of_nat(v___x_4771_);
v___x_4776_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1___redArg(v_a_4762_, v___x_4774_, v___x_4775_, v_tree_4689_);
lean_dec(v_a_4762_);
return v___x_4776_;
}
}
else
{
size_t v___x_4777_; size_t v___x_4778_; lean_object* v___x_4779_; 
v___x_4777_ = ((size_t)0ULL);
v___x_4778_ = lean_usize_of_nat(v___x_4771_);
v___x_4779_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1___redArg(v_a_4762_, v___x_4777_, v___x_4778_, v_tree_4689_);
lean_dec(v_a_4762_);
return v___x_4779_;
}
}
}
}
else
{
lean_object* v_a_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; 
lean_dec(v___x_4760_);
lean_dec(v___x_4727_);
lean_del_object(v___x_4703_);
v_a_4781_ = lean_ctor_get(v___x_4761_, 0);
lean_inc(v_a_4781_);
lean_dec_ref_known(v___x_4761_, 1);
v___x_4782_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4782_, 0, v_modName_4686_);
lean_ctor_set(v___x_4782_, 1, v_name_4694_);
lean_ctor_set(v___x_4782_, 2, v_a_4781_);
v___x_4783_ = lean_st_ref_take(v_d_4687_);
v___x_4784_ = lean_array_push(v___x_4783_, v___x_4782_);
v___x_4785_ = lean_st_ref_put(v_d_4687_, v___x_4784_);
return v_tree_4689_;
}
}
}
}
v___jp_4789_:
{
lean_object* v___x_4791_; lean_object* v_env_4792_; lean_object* v_nextMacroScope_4793_; lean_object* v_ngen_4794_; lean_object* v_auxDeclNGen_4795_; lean_object* v_traceState_4796_; lean_object* v_recordedDeps_4797_; lean_object* v_messages_4798_; lean_object* v_infoState_4799_; lean_object* v_snapshotTasks_4800_; lean_object* v___x_4802_; uint8_t v_isShared_4803_; uint8_t v_isSharedCheck_4810_; 
v___x_4791_ = lean_st_ref_take(v___x_4727_);
v_env_4792_ = lean_ctor_get(v___x_4791_, 0);
v_nextMacroScope_4793_ = lean_ctor_get(v___x_4791_, 1);
v_ngen_4794_ = lean_ctor_get(v___x_4791_, 2);
v_auxDeclNGen_4795_ = lean_ctor_get(v___x_4791_, 3);
v_traceState_4796_ = lean_ctor_get(v___x_4791_, 4);
v_recordedDeps_4797_ = lean_ctor_get(v___x_4791_, 6);
v_messages_4798_ = lean_ctor_get(v___x_4791_, 7);
v_infoState_4799_ = lean_ctor_get(v___x_4791_, 8);
v_snapshotTasks_4800_ = lean_ctor_get(v___x_4791_, 9);
v_isSharedCheck_4810_ = !lean_is_exclusive(v___x_4791_);
if (v_isSharedCheck_4810_ == 0)
{
lean_object* v_unused_4811_; 
v_unused_4811_ = lean_ctor_get(v___x_4791_, 5);
lean_dec(v_unused_4811_);
v___x_4802_ = v___x_4791_;
v_isShared_4803_ = v_isSharedCheck_4810_;
goto v_resetjp_4801_;
}
else
{
lean_inc(v_snapshotTasks_4800_);
lean_inc(v_infoState_4799_);
lean_inc(v_messages_4798_);
lean_inc(v_recordedDeps_4797_);
lean_inc(v_traceState_4796_);
lean_inc(v_auxDeclNGen_4795_);
lean_inc(v_ngen_4794_);
lean_inc(v_nextMacroScope_4793_);
lean_inc(v_env_4792_);
lean_dec(v___x_4791_);
v___x_4802_ = lean_box(0);
v_isShared_4803_ = v_isSharedCheck_4810_;
goto v_resetjp_4801_;
}
v_resetjp_4801_:
{
lean_object* v___x_4804_; lean_object* v___x_4805_; lean_object* v___x_4807_; 
v___x_4804_ = l_Lean_Kernel_enableDiag(v_env_4792_, v___y_4790_);
v___x_4805_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12);
if (v_isShared_4803_ == 0)
{
lean_ctor_set(v___x_4802_, 5, v___x_4805_);
lean_ctor_set(v___x_4802_, 0, v___x_4804_);
v___x_4807_ = v___x_4802_;
goto v_reusejp_4806_;
}
else
{
lean_object* v_reuseFailAlloc_4809_; 
v_reuseFailAlloc_4809_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4809_, 0, v___x_4804_);
lean_ctor_set(v_reuseFailAlloc_4809_, 1, v_nextMacroScope_4793_);
lean_ctor_set(v_reuseFailAlloc_4809_, 2, v_ngen_4794_);
lean_ctor_set(v_reuseFailAlloc_4809_, 3, v_auxDeclNGen_4795_);
lean_ctor_set(v_reuseFailAlloc_4809_, 4, v_traceState_4796_);
lean_ctor_set(v_reuseFailAlloc_4809_, 5, v___x_4805_);
lean_ctor_set(v_reuseFailAlloc_4809_, 6, v_recordedDeps_4797_);
lean_ctor_set(v_reuseFailAlloc_4809_, 7, v_messages_4798_);
lean_ctor_set(v_reuseFailAlloc_4809_, 8, v_infoState_4799_);
lean_ctor_set(v_reuseFailAlloc_4809_, 9, v_snapshotTasks_4800_);
v___x_4807_ = v_reuseFailAlloc_4809_;
goto v_reusejp_4806_;
}
v_reusejp_4806_:
{
lean_object* v___x_4808_; 
v___x_4808_ = lean_st_ref_put(v___x_4727_, v___x_4807_);
lean_inc(v___x_4727_);
v___y_4753_ = v___x_4727_;
goto v___jp_4752_;
}
}
}
v___jp_4814_:
{
if (v___x_4813_ == 0)
{
v___y_4790_ = v___y_4815_;
goto v___jp_4789_;
}
else
{
lean_inc(v___x_4727_);
v___y_4753_ = v___x_4727_;
goto v___jp_4752_;
}
}
}
}
}
}
else
{
lean_dec(v_name_4694_);
lean_dec_ref(v_c_4691_);
lean_dec_ref(v_act_4690_);
lean_dec(v_modName_4686_);
lean_dec_ref(v_env_4685_);
lean_dec_ref(v_cctx_4684_);
return v_tree_4689_;
}
}
else
{
lean_dec_ref(v_c_4691_);
lean_dec_ref(v_act_4690_);
lean_dec(v_modName_4686_);
lean_dec_ref(v_env_4685_);
lean_dec_ref(v_cctx_4684_);
return v_tree_4689_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___boxed(lean_object* v_cctx_4825_, lean_object* v_env_4826_, lean_object* v_modName_4827_, lean_object* v_d_4828_, lean_object* v_cacheRef_4829_, lean_object* v_tree_4830_, lean_object* v_act_4831_, lean_object* v_c_4832_, lean_object* v_a_4833_){
_start:
{
lean_object* v_res_4834_; 
v_res_4834_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_4825_, v_env_4826_, v_modName_4827_, v_d_4828_, v_cacheRef_4829_, v_tree_4830_, v_act_4831_, v_c_4832_);
lean_dec(v_cacheRef_4829_);
lean_dec(v_d_4828_);
return v_res_4834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData(lean_object* v_00_u03b1_4835_, lean_object* v_cctx_4836_, lean_object* v_env_4837_, lean_object* v_modName_4838_, lean_object* v_d_4839_, lean_object* v_cacheRef_4840_, lean_object* v_tree_4841_, lean_object* v_act_4842_, lean_object* v_c_4843_){
_start:
{
lean_object* v___x_4845_; 
v___x_4845_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_4836_, v_env_4837_, v_modName_4838_, v_d_4839_, v_cacheRef_4840_, v_tree_4841_, v_act_4842_, v_c_4843_);
return v___x_4845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___boxed(lean_object* v_00_u03b1_4846_, lean_object* v_cctx_4847_, lean_object* v_env_4848_, lean_object* v_modName_4849_, lean_object* v_d_4850_, lean_object* v_cacheRef_4851_, lean_object* v_tree_4852_, lean_object* v_act_4853_, lean_object* v_c_4854_, lean_object* v_a_4855_){
_start:
{
lean_object* v_res_4856_; 
v_res_4856_ = l_Lean_Meta_LazyDiscrTree_addConstImportData(v_00_u03b1_4846_, v_cctx_4847_, v_env_4848_, v_modName_4849_, v_d_4850_, v_cacheRef_4851_, v_tree_4852_, v_act_4853_, v_c_4854_);
lean_dec(v_cacheRef_4851_);
lean_dec(v_d_4850_);
return v_res_4856_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1(lean_object* v_00_u03b1_4857_, lean_object* v_as_4858_, size_t v_i_4859_, size_t v_stop_4860_, lean_object* v_b_4861_){
_start:
{
lean_object* v___x_4862_; 
v___x_4862_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1___redArg(v_as_4858_, v_i_4859_, v_stop_4860_, v_b_4861_);
return v___x_4862_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1___boxed(lean_object* v_00_u03b1_4863_, lean_object* v_as_4864_, lean_object* v_i_4865_, lean_object* v_stop_4866_, lean_object* v_b_4867_){
_start:
{
size_t v_i_boxed_4868_; size_t v_stop_boxed_4869_; lean_object* v_res_4870_; 
v_i_boxed_4868_ = lean_unbox_usize(v_i_4865_);
lean_dec(v_i_4865_);
v_stop_boxed_4869_ = lean_unbox_usize(v_stop_4866_);
lean_dec(v_stop_4866_);
v_res_4870_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1(v_00_u03b1_4863_, v_as_4864_, v_i_boxed_4868_, v_stop_boxed_4869_, v_b_4867_);
lean_dec_ref(v_as_4864_);
return v_res_4870_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___redArg___closed__0(void){
_start:
{
lean_object* v___x_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; 
v___x_4871_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__0));
v___x_4872_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1);
v___x_4873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4873_, 0, v___x_4872_);
lean_ctor_set(v___x_4873_, 1, v___x_4871_);
return v___x_4873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___redArg(){
_start:
{
lean_object* v___x_4875_; 
v___x_4875_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___redArg___closed__0);
return v___x_4875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___redArg___boxed(lean_object* v___dummy_4876_){
_start:
{
lean_object* v_res_4877_; 
v_res_4877_ = l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___redArg();
return v_res_4877_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0(void){
_start:
{
lean_object* v___x_4878_; 
v___x_4878_ = l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___redArg();
return v___x_4878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults(lean_object* v_00_u03b1_4879_){
_start:
{
lean_object* v___x_4880_; 
v___x_4880_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0);
return v___x_4880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_append___redArg(lean_object* v_x_4881_, lean_object* v_y_4882_){
_start:
{
lean_object* v_tree_4883_; lean_object* v_errors_4884_; lean_object* v_tree_4885_; lean_object* v_errors_4886_; lean_object* v___x_4888_; uint8_t v_isShared_4889_; uint8_t v_isSharedCheck_4895_; 
v_tree_4883_ = lean_ctor_get(v_x_4881_, 0);
lean_inc_ref(v_tree_4883_);
v_errors_4884_ = lean_ctor_get(v_x_4881_, 1);
lean_inc_ref(v_errors_4884_);
lean_dec_ref(v_x_4881_);
v_tree_4885_ = lean_ctor_get(v_y_4882_, 0);
v_errors_4886_ = lean_ctor_get(v_y_4882_, 1);
v_isSharedCheck_4895_ = !lean_is_exclusive(v_y_4882_);
if (v_isSharedCheck_4895_ == 0)
{
v___x_4888_ = v_y_4882_;
v_isShared_4889_ = v_isSharedCheck_4895_;
goto v_resetjp_4887_;
}
else
{
lean_inc(v_errors_4886_);
lean_inc(v_tree_4885_);
lean_dec(v_y_4882_);
v___x_4888_ = lean_box(0);
v_isShared_4889_ = v_isSharedCheck_4895_;
goto v_resetjp_4887_;
}
v_resetjp_4887_:
{
lean_object* v___x_4890_; lean_object* v___x_4891_; lean_object* v___x_4893_; 
v___x_4890_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg(v_tree_4883_, v_tree_4885_);
v___x_4891_ = l_Array_append___redArg(v_errors_4884_, v_errors_4886_);
lean_dec_ref(v_errors_4886_);
if (v_isShared_4889_ == 0)
{
lean_ctor_set(v___x_4888_, 1, v___x_4891_);
lean_ctor_set(v___x_4888_, 0, v___x_4890_);
v___x_4893_ = v___x_4888_;
goto v_reusejp_4892_;
}
else
{
lean_object* v_reuseFailAlloc_4894_; 
v_reuseFailAlloc_4894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4894_, 0, v___x_4890_);
lean_ctor_set(v_reuseFailAlloc_4894_, 1, v___x_4891_);
v___x_4893_ = v_reuseFailAlloc_4894_;
goto v_reusejp_4892_;
}
v_reusejp_4892_:
{
return v___x_4893_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_append(lean_object* v_00_u03b1_4896_, lean_object* v_x_4897_, lean_object* v_y_4898_){
_start:
{
lean_object* v___x_4899_; 
v___x_4899_ = l_Lean_Meta_LazyDiscrTree_InitResults_append___redArg(v_x_4897_, v_y_4898_);
return v___x_4899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___redArg(){
_start:
{
lean_object* v___x_4902_; 
v___x_4902_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___redArg___closed__0));
return v___x_4902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___redArg___boxed(lean_object* v___dummy_4903_){
_start:
{
lean_object* v_res_4904_; 
v_res_4904_ = l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___redArg();
return v_res_4904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_instAppend(lean_object* v_00_u03b1_4905_){
_start:
{
lean_object* v___x_4906_; 
v___x_4906_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___redArg___closed__0));
return v___x_4906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat___redArg(lean_object* v_d_4907_, lean_object* v_tree_4908_){
_start:
{
lean_object* v___x_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; 
v___x_4910_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_ImportData_new___closed__0));
v___x_4911_ = lean_st_ref_swap(v_d_4907_, v___x_4910_);
v___x_4912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4912_, 0, v_tree_4908_);
lean_ctor_set(v___x_4912_, 1, v___x_4911_);
return v___x_4912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat___redArg___boxed(lean_object* v_d_4913_, lean_object* v_tree_4914_, lean_object* v_a_4915_){
_start:
{
lean_object* v_res_4916_; 
v_res_4916_ = l_Lean_Meta_LazyDiscrTree_toFlat___redArg(v_d_4913_, v_tree_4914_);
lean_dec(v_d_4913_);
return v_res_4916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat(lean_object* v_00_u03b1_4917_, lean_object* v_d_4918_, lean_object* v_tree_4919_){
_start:
{
lean_object* v___x_4921_; 
v___x_4921_ = l_Lean_Meta_LazyDiscrTree_toFlat___redArg(v_d_4918_, v_tree_4919_);
return v___x_4921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat___boxed(lean_object* v_00_u03b1_4922_, lean_object* v_d_4923_, lean_object* v_tree_4924_, lean_object* v_a_4925_){
_start:
{
lean_object* v_res_4926_; 
v_res_4926_ = l_Lean_Meta_LazyDiscrTree_toFlat(v_00_u03b1_4922_, v_d_4923_, v_tree_4924_);
lean_dec(v_d_4923_);
return v_res_4926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(lean_object* v_cctx_4927_, lean_object* v_env_4928_, lean_object* v_act_4929_, lean_object* v_d_4930_, lean_object* v_cacheRef_4931_, lean_object* v_tree_4932_, lean_object* v_mname_4933_, lean_object* v_mdata_4934_, lean_object* v_i_4935_){
_start:
{
lean_object* v_constants_4937_; lean_object* v___x_4938_; uint8_t v___x_4939_; 
v_constants_4937_ = lean_ctor_get(v_mdata_4934_, 2);
v___x_4938_ = lean_array_get_size(v_constants_4937_);
v___x_4939_ = lean_nat_dec_lt(v_i_4935_, v___x_4938_);
if (v___x_4939_ == 0)
{
lean_dec(v_i_4935_);
lean_dec(v_mname_4933_);
lean_dec_ref(v_act_4929_);
lean_dec_ref(v_env_4928_);
lean_dec_ref(v_cctx_4927_);
return v_tree_4932_;
}
else
{
lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; 
v___x_4940_ = lean_array_fget_borrowed(v_constants_4937_, v_i_4935_);
lean_inc(v___x_4940_);
v___x_4941_ = l_Lean_AsyncConstantInfo_ofConstantInfo(v___x_4940_);
lean_inc_ref(v_act_4929_);
lean_inc(v_mname_4933_);
lean_inc_ref(v_env_4928_);
lean_inc_ref(v_cctx_4927_);
v___x_4942_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_4927_, v_env_4928_, v_mname_4933_, v_d_4930_, v_cacheRef_4931_, v_tree_4932_, v_act_4929_, v___x_4941_);
v___x_4943_ = lean_unsigned_to_nat(1u);
v___x_4944_ = lean_nat_add(v_i_4935_, v___x_4943_);
lean_dec(v_i_4935_);
v_tree_4932_ = v___x_4942_;
v_i_4935_ = v___x_4944_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg___boxed(lean_object* v_cctx_4946_, lean_object* v_env_4947_, lean_object* v_act_4948_, lean_object* v_d_4949_, lean_object* v_cacheRef_4950_, lean_object* v_tree_4951_, lean_object* v_mname_4952_, lean_object* v_mdata_4953_, lean_object* v_i_4954_, lean_object* v_a_4955_){
_start:
{
lean_object* v_res_4956_; 
v_res_4956_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(v_cctx_4946_, v_env_4947_, v_act_4948_, v_d_4949_, v_cacheRef_4950_, v_tree_4951_, v_mname_4952_, v_mdata_4953_, v_i_4954_);
lean_dec_ref(v_mdata_4953_);
lean_dec(v_cacheRef_4950_);
lean_dec(v_d_4949_);
return v_res_4956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule(lean_object* v_00_u03b1_4957_, lean_object* v_cctx_4958_, lean_object* v_env_4959_, lean_object* v_act_4960_, lean_object* v_d_4961_, lean_object* v_cacheRef_4962_, lean_object* v_tree_4963_, lean_object* v_mname_4964_, lean_object* v_mdata_4965_, lean_object* v_i_4966_){
_start:
{
lean_object* v___x_4968_; 
v___x_4968_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(v_cctx_4958_, v_env_4959_, v_act_4960_, v_d_4961_, v_cacheRef_4962_, v_tree_4963_, v_mname_4964_, v_mdata_4965_, v_i_4966_);
return v___x_4968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule___boxed(lean_object* v_00_u03b1_4969_, lean_object* v_cctx_4970_, lean_object* v_env_4971_, lean_object* v_act_4972_, lean_object* v_d_4973_, lean_object* v_cacheRef_4974_, lean_object* v_tree_4975_, lean_object* v_mname_4976_, lean_object* v_mdata_4977_, lean_object* v_i_4978_, lean_object* v_a_4979_){
_start:
{
lean_object* v_res_4980_; 
v_res_4980_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule(v_00_u03b1_4969_, v_cctx_4970_, v_env_4971_, v_act_4972_, v_d_4973_, v_cacheRef_4974_, v_tree_4975_, v_mname_4976_, v_mdata_4977_, v_i_4978_);
lean_dec_ref(v_mdata_4977_);
lean_dec(v_cacheRef_4974_);
lean_dec(v_d_4973_);
return v_res_4980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg(lean_object* v_cctx_4981_, lean_object* v_env_4982_, lean_object* v_act_4983_, lean_object* v_d_4984_, lean_object* v_cacheRef_4985_, lean_object* v_tree_4986_, lean_object* v_start_4987_, lean_object* v_stop_4988_){
_start:
{
uint8_t v___x_4990_; 
v___x_4990_ = lean_nat_dec_lt(v_start_4987_, v_stop_4988_);
if (v___x_4990_ == 0)
{
lean_object* v___x_4991_; 
lean_dec(v_start_4987_);
lean_dec_ref(v_act_4983_);
lean_dec_ref(v_env_4982_);
lean_dec_ref(v_cctx_4981_);
v___x_4991_ = l_Lean_Meta_LazyDiscrTree_toFlat___redArg(v_d_4984_, v_tree_4986_);
return v___x_4991_;
}
else
{
lean_object* v___x_4992_; lean_object* v_moduleData_4993_; lean_object* v___x_4994_; lean_object* v___x_4995_; lean_object* v___x_4996_; lean_object* v_mname_4997_; lean_object* v_mdata_4998_; lean_object* v___x_4999_; lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; 
v___x_4992_ = l_Lean_Environment_header(v_env_4982_);
v_moduleData_4993_ = lean_ctor_get(v___x_4992_, 6);
lean_inc_ref(v_moduleData_4993_);
v___x_4994_ = lean_box(0);
v___x_4995_ = l_Lean_instInhabitedModuleData_default;
v___x_4996_ = l_Lean_EnvironmentHeader_moduleNames(v___x_4992_);
v_mname_4997_ = lean_array_get(v___x_4994_, v___x_4996_, v_start_4987_);
lean_dec_ref(v___x_4996_);
v_mdata_4998_ = lean_array_get(v___x_4995_, v_moduleData_4993_, v_start_4987_);
lean_dec_ref(v_moduleData_4993_);
v___x_4999_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_act_4983_);
lean_inc_ref(v_env_4982_);
lean_inc_ref(v_cctx_4981_);
v___x_5000_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(v_cctx_4981_, v_env_4982_, v_act_4983_, v_d_4984_, v_cacheRef_4985_, v_tree_4986_, v_mname_4997_, v_mdata_4998_, v___x_4999_);
lean_dec(v_mdata_4998_);
v___x_5001_ = lean_unsigned_to_nat(1u);
v___x_5002_ = lean_nat_add(v_start_4987_, v___x_5001_);
lean_dec(v_start_4987_);
v_tree_4986_ = v___x_5000_;
v_start_4987_ = v___x_5002_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg___boxed(lean_object* v_cctx_5004_, lean_object* v_env_5005_, lean_object* v_act_5006_, lean_object* v_d_5007_, lean_object* v_cacheRef_5008_, lean_object* v_tree_5009_, lean_object* v_start_5010_, lean_object* v_stop_5011_, lean_object* v_a_5012_){
_start:
{
lean_object* v_res_5013_; 
v_res_5013_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg(v_cctx_5004_, v_env_5005_, v_act_5006_, v_d_5007_, v_cacheRef_5008_, v_tree_5009_, v_start_5010_, v_stop_5011_);
lean_dec(v_stop_5011_);
lean_dec(v_cacheRef_5008_);
lean_dec(v_d_5007_);
return v_res_5013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go(lean_object* v_00_u03b1_5014_, lean_object* v_cctx_5015_, lean_object* v_env_5016_, lean_object* v_act_5017_, lean_object* v_d_5018_, lean_object* v_cacheRef_5019_, lean_object* v_tree_5020_, lean_object* v_start_5021_, lean_object* v_stop_5022_){
_start:
{
lean_object* v___x_5024_; 
v___x_5024_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg(v_cctx_5015_, v_env_5016_, v_act_5017_, v_d_5018_, v_cacheRef_5019_, v_tree_5020_, v_start_5021_, v_stop_5022_);
return v___x_5024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___boxed(lean_object* v_00_u03b1_5025_, lean_object* v_cctx_5026_, lean_object* v_env_5027_, lean_object* v_act_5028_, lean_object* v_d_5029_, lean_object* v_cacheRef_5030_, lean_object* v_tree_5031_, lean_object* v_start_5032_, lean_object* v_stop_5033_, lean_object* v_a_5034_){
_start:
{
lean_object* v_res_5035_; 
v_res_5035_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go(v_00_u03b1_5025_, v_cctx_5026_, v_env_5027_, v_act_5028_, v_d_5029_, v_cacheRef_5030_, v_tree_5031_, v_start_5032_, v_stop_5033_);
lean_dec(v_stop_5033_);
lean_dec(v_cacheRef_5030_);
lean_dec(v_d_5029_);
return v_res_5035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___redArg(lean_object* v_cctx_5036_, lean_object* v_ngen_5037_, lean_object* v_env_5038_, lean_object* v_act_5039_, lean_object* v_start_5040_, lean_object* v_stop_5041_){
_start:
{
lean_object* v___x_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; lean_object* v___x_5046_; lean_object* v___x_5047_; 
v___x_5043_ = l_Lean_Meta_LazyDiscrTree_Cache_empty(v_ngen_5037_);
v___x_5044_ = lean_st_mk_ref(v___x_5043_);
v___x_5045_ = l_Lean_Meta_LazyDiscrTree_ImportData_new();
v___x_5046_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1);
v___x_5047_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg(v_cctx_5036_, v_env_5038_, v_act_5039_, v___x_5045_, v___x_5044_, v___x_5046_, v_start_5040_, v_stop_5041_);
lean_dec(v___x_5044_);
lean_dec(v___x_5045_);
return v___x_5047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___redArg___boxed(lean_object* v_cctx_5048_, lean_object* v_ngen_5049_, lean_object* v_env_5050_, lean_object* v_act_5051_, lean_object* v_start_5052_, lean_object* v_stop_5053_, lean_object* v_a_5054_){
_start:
{
lean_object* v_res_5055_; 
v_res_5055_ = l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___redArg(v_cctx_5048_, v_ngen_5049_, v_env_5050_, v_act_5051_, v_start_5052_, v_stop_5053_);
lean_dec(v_stop_5053_);
return v_res_5055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq(lean_object* v_00_u03b1_5056_, lean_object* v_cctx_5057_, lean_object* v_ngen_5058_, lean_object* v_env_5059_, lean_object* v_act_5060_, lean_object* v_start_5061_, lean_object* v_stop_5062_){
_start:
{
lean_object* v___x_5064_; 
v___x_5064_ = l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___redArg(v_cctx_5057_, v_ngen_5058_, v_env_5059_, v_act_5060_, v_start_5061_, v_stop_5062_);
return v___x_5064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed(lean_object* v_00_u03b1_5065_, lean_object* v_cctx_5066_, lean_object* v_ngen_5067_, lean_object* v_env_5068_, lean_object* v_act_5069_, lean_object* v_start_5070_, lean_object* v_stop_5071_, lean_object* v_a_5072_){
_start:
{
lean_object* v_res_5073_; 
v_res_5073_ = l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq(v_00_u03b1_5065_, v_cctx_5066_, v_ngen_5067_, v_env_5068_, v_act_5069_, v_start_5070_, v_stop_5071_);
lean_dec(v_stop_5071_);
return v_res_5073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___redArg___lam__0(lean_object* v_inst_5074_, lean_object* v_x1_5075_, lean_object* v_x2_5076_){
_start:
{
lean_object* v___x_5077_; lean_object* v___x_5078_; 
v___x_5077_ = lean_task_get_own(v_x2_5076_);
v___x_5078_ = lean_apply_2(v_inst_5074_, v_x1_5075_, v___x_5077_);
return v___x_5078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___redArg(lean_object* v_inst_5079_, lean_object* v_z_5080_, lean_object* v_tasks_5081_){
_start:
{
lean_object* v___x_5082_; lean_object* v___x_5083_; lean_object* v___x_5084_; uint8_t v___x_5085_; 
v___x_5082_ = lean_unsigned_to_nat(0u);
v___x_5083_ = lean_array_get_size(v_tasks_5081_);
v___x_5084_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__9));
v___x_5085_ = lean_nat_dec_lt(v___x_5082_, v___x_5083_);
if (v___x_5085_ == 0)
{
lean_dec_ref(v_tasks_5081_);
lean_dec(v_inst_5079_);
return v_z_5080_;
}
else
{
lean_object* v___f_5086_; uint8_t v___x_5087_; 
v___f_5086_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_combineGet___redArg___lam__0), 3, 1);
lean_closure_set(v___f_5086_, 0, v_inst_5079_);
v___x_5087_ = lean_nat_dec_le(v___x_5083_, v___x_5083_);
if (v___x_5087_ == 0)
{
if (v___x_5085_ == 0)
{
lean_dec_ref(v___f_5086_);
lean_dec_ref(v_tasks_5081_);
return v_z_5080_;
}
else
{
size_t v___x_5088_; size_t v___x_5089_; lean_object* v___x_5090_; 
v___x_5088_ = ((size_t)0ULL);
v___x_5089_ = lean_usize_of_nat(v___x_5083_);
v___x_5090_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_5084_, v___f_5086_, v_tasks_5081_, v___x_5088_, v___x_5089_, v_z_5080_);
return v___x_5090_;
}
}
else
{
size_t v___x_5091_; size_t v___x_5092_; lean_object* v___x_5093_; 
v___x_5091_ = ((size_t)0ULL);
v___x_5092_ = lean_usize_of_nat(v___x_5083_);
v___x_5093_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_5084_, v___f_5086_, v_tasks_5081_, v___x_5091_, v___x_5092_, v_z_5080_);
return v___x_5093_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet(lean_object* v_00_u03b1_5094_, lean_object* v_inst_5095_, lean_object* v_z_5096_, lean_object* v_tasks_5097_){
_start:
{
lean_object* v___x_5098_; 
v___x_5098_ = l_Lean_Meta_LazyDiscrTree_combineGet___redArg(v_inst_5095_, v_z_5096_, v_tasks_5097_);
return v___x_5098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg___lam__0(lean_object* v_toPure_5099_, lean_object* v___x_5100_, lean_object* v_____r_5101_){
_start:
{
lean_object* v___x_5102_; 
v___x_5102_ = lean_apply_2(v_toPure_5099_, lean_box(0), v___x_5100_);
return v___x_5102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg___lam__1(lean_object* v_toPure_5103_, lean_object* v_setNGen_5104_, lean_object* v_toBind_5105_, lean_object* v_ngen_5106_){
_start:
{
lean_object* v_namePrefix_5107_; lean_object* v_idx_5108_; lean_object* v___x_5110_; uint8_t v_isShared_5111_; uint8_t v_isSharedCheck_5122_; 
v_namePrefix_5107_ = lean_ctor_get(v_ngen_5106_, 0);
v_idx_5108_ = lean_ctor_get(v_ngen_5106_, 1);
v_isSharedCheck_5122_ = !lean_is_exclusive(v_ngen_5106_);
if (v_isSharedCheck_5122_ == 0)
{
v___x_5110_ = v_ngen_5106_;
v_isShared_5111_ = v_isSharedCheck_5122_;
goto v_resetjp_5109_;
}
else
{
lean_inc(v_idx_5108_);
lean_inc(v_namePrefix_5107_);
lean_dec(v_ngen_5106_);
v___x_5110_ = lean_box(0);
v_isShared_5111_ = v_isSharedCheck_5122_;
goto v_resetjp_5109_;
}
v_resetjp_5109_:
{
lean_object* v___x_5112_; lean_object* v___x_5113_; lean_object* v___x_5115_; 
lean_inc(v_idx_5108_);
lean_inc(v_namePrefix_5107_);
v___x_5112_ = l_Lean_Name_num___override(v_namePrefix_5107_, v_idx_5108_);
v___x_5113_ = lean_unsigned_to_nat(1u);
if (v_isShared_5111_ == 0)
{
lean_ctor_set(v___x_5110_, 1, v___x_5113_);
lean_ctor_set(v___x_5110_, 0, v___x_5112_);
v___x_5115_ = v___x_5110_;
goto v_reusejp_5114_;
}
else
{
lean_object* v_reuseFailAlloc_5121_; 
v_reuseFailAlloc_5121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5121_, 0, v___x_5112_);
lean_ctor_set(v_reuseFailAlloc_5121_, 1, v___x_5113_);
v___x_5115_ = v_reuseFailAlloc_5121_;
goto v_reusejp_5114_;
}
v_reusejp_5114_:
{
lean_object* v___f_5116_; lean_object* v___x_5117_; lean_object* v___x_5118_; lean_object* v___x_5119_; lean_object* v___x_5120_; 
v___f_5116_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5116_, 0, v_toPure_5103_);
lean_closure_set(v___f_5116_, 1, v___x_5115_);
v___x_5117_ = lean_nat_add(v_idx_5108_, v___x_5113_);
lean_dec(v_idx_5108_);
v___x_5118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5118_, 0, v_namePrefix_5107_);
lean_ctor_set(v___x_5118_, 1, v___x_5117_);
v___x_5119_ = lean_apply_1(v_setNGen_5104_, v___x_5118_);
v___x_5120_ = lean_apply_4(v_toBind_5105_, lean_box(0), lean_box(0), v___x_5119_, v___f_5116_);
return v___x_5120_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg(lean_object* v_inst_5123_, lean_object* v_inst_5124_){
_start:
{
lean_object* v_toApplicative_5125_; lean_object* v_toBind_5126_; lean_object* v_getNGen_5127_; lean_object* v_setNGen_5128_; lean_object* v_toPure_5129_; lean_object* v___f_5130_; lean_object* v___x_5131_; 
v_toApplicative_5125_ = lean_ctor_get(v_inst_5123_, 0);
lean_inc_ref(v_toApplicative_5125_);
v_toBind_5126_ = lean_ctor_get(v_inst_5123_, 1);
lean_inc_n(v_toBind_5126_, 2);
lean_dec_ref(v_inst_5123_);
v_getNGen_5127_ = lean_ctor_get(v_inst_5124_, 0);
lean_inc(v_getNGen_5127_);
v_setNGen_5128_ = lean_ctor_get(v_inst_5124_, 1);
lean_inc(v_setNGen_5128_);
lean_dec_ref(v_inst_5124_);
v_toPure_5129_ = lean_ctor_get(v_toApplicative_5125_, 1);
lean_inc(v_toPure_5129_);
lean_dec_ref(v_toApplicative_5125_);
v___f_5130_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg___lam__1), 4, 3);
lean_closure_set(v___f_5130_, 0, v_toPure_5129_);
lean_closure_set(v___f_5130_, 1, v_setNGen_5128_);
lean_closure_set(v___f_5130_, 2, v_toBind_5126_);
v___x_5131_ = lean_apply_4(v_toBind_5126_, lean_box(0), lean_box(0), v_getNGen_5127_, v___f_5130_);
return v___x_5131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen(lean_object* v_M_5132_, lean_object* v_inst_5133_, lean_object* v_inst_5134_){
_start:
{
lean_object* v___x_5135_; 
v___x_5135_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg(v_inst_5133_, v_inst_5134_);
return v___x_5135_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg(lean_object* v_cctx_5136_, lean_object* v_env_5137_, lean_object* v_modName_5138_, lean_object* v_d_5139_, lean_object* v_val_5140_, lean_object* v_act_5141_, lean_object* v_as_5142_, size_t v_sz_5143_, size_t v_i_5144_, lean_object* v_b_5145_){
_start:
{
uint8_t v___x_5147_; 
v___x_5147_ = lean_usize_dec_lt(v_i_5144_, v_sz_5143_);
if (v___x_5147_ == 0)
{
lean_dec_ref(v_act_5141_);
lean_dec(v_modName_5138_);
lean_dec_ref(v_env_5137_);
lean_dec_ref(v_cctx_5136_);
return v_b_5145_;
}
else
{
lean_object* v_a_5148_; lean_object* v___x_5149_; size_t v___x_5150_; size_t v___x_5151_; 
v_a_5148_ = lean_array_uget_borrowed(v_as_5142_, v_i_5144_);
lean_inc(v_a_5148_);
lean_inc_ref(v_act_5141_);
lean_inc(v_modName_5138_);
lean_inc_ref(v_env_5137_);
lean_inc_ref(v_cctx_5136_);
v___x_5149_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_5136_, v_env_5137_, v_modName_5138_, v_d_5139_, v_val_5140_, v_b_5145_, v_act_5141_, v_a_5148_);
v___x_5150_ = ((size_t)1ULL);
v___x_5151_ = lean_usize_add(v_i_5144_, v___x_5150_);
v_i_5144_ = v___x_5151_;
v_b_5145_ = v___x_5149_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg___boxed(lean_object* v_cctx_5153_, lean_object* v_env_5154_, lean_object* v_modName_5155_, lean_object* v_d_5156_, lean_object* v_val_5157_, lean_object* v_act_5158_, lean_object* v_as_5159_, lean_object* v_sz_5160_, lean_object* v_i_5161_, lean_object* v_b_5162_, lean_object* v___y_5163_){
_start:
{
size_t v_sz_boxed_5164_; size_t v_i_boxed_5165_; lean_object* v_res_5166_; 
v_sz_boxed_5164_ = lean_unbox_usize(v_sz_5160_);
lean_dec(v_sz_5160_);
v_i_boxed_5165_ = lean_unbox_usize(v_i_5161_);
lean_dec(v_i_5161_);
v_res_5166_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg(v_cctx_5153_, v_env_5154_, v_modName_5155_, v_d_5156_, v_val_5157_, v_act_5158_, v_as_5159_, v_sz_boxed_5164_, v_i_boxed_5165_, v_b_5162_);
lean_dec_ref(v_as_5159_);
lean_dec(v_val_5157_);
lean_dec(v_d_5156_);
return v_res_5166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(lean_object* v_cctx_5167_, lean_object* v_ngen_5168_, lean_object* v_env_5169_, lean_object* v_d_5170_, lean_object* v_act_5171_){
_start:
{
lean_object* v___x_5173_; lean_object* v_mainModule_5174_; lean_object* v___x_5175_; lean_object* v___x_5176_; lean_object* v___x_5177_; uint8_t v___x_5178_; lean_object* v___x_5179_; size_t v_sz_5180_; size_t v___x_5181_; lean_object* v___x_5182_; 
v___x_5173_ = l_Lean_Environment_header(v_env_5169_);
v_mainModule_5174_ = lean_ctor_get(v___x_5173_, 0);
lean_inc(v_mainModule_5174_);
lean_dec_ref(v___x_5173_);
v___x_5175_ = l_Lean_Meta_LazyDiscrTree_Cache_empty(v_ngen_5168_);
v___x_5176_ = lean_st_mk_ref(v___x_5175_);
v___x_5177_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1);
v___x_5178_ = 1;
v___x_5179_ = l_Lean_Environment_getLocalConstantInfos(v_env_5169_, v___x_5178_);
v_sz_5180_ = lean_array_size(v___x_5179_);
v___x_5181_ = ((size_t)0ULL);
v___x_5182_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg(v_cctx_5167_, v_env_5169_, v_mainModule_5174_, v_d_5170_, v___x_5176_, v_act_5171_, v___x_5179_, v_sz_5180_, v___x_5181_, v___x_5177_);
lean_dec_ref(v___x_5179_);
lean_dec(v___x_5176_);
return v___x_5182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg___boxed(lean_object* v_cctx_5183_, lean_object* v_ngen_5184_, lean_object* v_env_5185_, lean_object* v_d_5186_, lean_object* v_act_5187_, lean_object* v_a_5188_){
_start:
{
lean_object* v_res_5189_; 
v_res_5189_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(v_cctx_5183_, v_ngen_5184_, v_env_5185_, v_d_5186_, v_act_5187_);
lean_dec(v_d_5186_);
return v_res_5189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree(lean_object* v_00_u03b1_5190_, lean_object* v_cctx_5191_, lean_object* v_ngen_5192_, lean_object* v_env_5193_, lean_object* v_d_5194_, lean_object* v_act_5195_){
_start:
{
lean_object* v___x_5197_; 
v___x_5197_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(v_cctx_5191_, v_ngen_5192_, v_env_5193_, v_d_5194_, v_act_5195_);
return v___x_5197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___boxed(lean_object* v_00_u03b1_5198_, lean_object* v_cctx_5199_, lean_object* v_ngen_5200_, lean_object* v_env_5201_, lean_object* v_d_5202_, lean_object* v_act_5203_, lean_object* v_a_5204_){
_start:
{
lean_object* v_res_5205_; 
v_res_5205_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree(v_00_u03b1_5198_, v_cctx_5199_, v_ngen_5200_, v_env_5201_, v_d_5202_, v_act_5203_);
lean_dec(v_d_5202_);
return v_res_5205_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0(lean_object* v_00_u03b1_5206_, lean_object* v_cctx_5207_, lean_object* v_env_5208_, lean_object* v_modName_5209_, lean_object* v_d_5210_, lean_object* v_val_5211_, lean_object* v_act_5212_, lean_object* v_as_5213_, size_t v_sz_5214_, size_t v_i_5215_, lean_object* v_b_5216_){
_start:
{
lean_object* v___x_5218_; 
v___x_5218_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg(v_cctx_5207_, v_env_5208_, v_modName_5209_, v_d_5210_, v_val_5211_, v_act_5212_, v_as_5213_, v_sz_5214_, v_i_5215_, v_b_5216_);
return v___x_5218_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___boxed(lean_object* v_00_u03b1_5219_, lean_object* v_cctx_5220_, lean_object* v_env_5221_, lean_object* v_modName_5222_, lean_object* v_d_5223_, lean_object* v_val_5224_, lean_object* v_act_5225_, lean_object* v_as_5226_, lean_object* v_sz_5227_, lean_object* v_i_5228_, lean_object* v_b_5229_, lean_object* v___y_5230_){
_start:
{
size_t v_sz_boxed_5231_; size_t v_i_boxed_5232_; lean_object* v_res_5233_; 
v_sz_boxed_5231_ = lean_unbox_usize(v_sz_5227_);
lean_dec(v_sz_5227_);
v_i_boxed_5232_ = lean_unbox_usize(v_i_5228_);
lean_dec(v_i_5228_);
v_res_5233_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0(v_00_u03b1_5219_, v_cctx_5220_, v_env_5221_, v_modName_5222_, v_d_5223_, v_val_5224_, v_act_5225_, v_as_5226_, v_sz_boxed_5231_, v_i_boxed_5232_, v_b_5229_);
lean_dec_ref(v_as_5226_);
lean_dec(v_val_5224_);
lean_dec(v_d_5223_);
return v_res_5233_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(lean_object* v_x_5234_, lean_object* v_x_5235_, lean_object* v___y_5236_, lean_object* v___y_5237_, lean_object* v___y_5238_, lean_object* v___y_5239_){
_start:
{
if (lean_obj_tag(v_x_5235_) == 0)
{
lean_object* v___x_5241_; 
v___x_5241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5241_, 0, v_x_5234_);
return v___x_5241_;
}
else
{
lean_object* v_head_5242_; lean_object* v_tail_5243_; lean_object* v___x_5244_; 
v_head_5242_ = lean_ctor_get(v_x_5235_, 0);
lean_inc(v_head_5242_);
v_tail_5243_ = lean_ctor_get(v_x_5235_, 1);
lean_inc(v_tail_5243_);
lean_dec_ref_known(v_x_5235_, 2);
v___x_5244_ = l_Lean_Meta_LazyDiscrTree_dropKey___redArg(v_x_5234_, v_head_5242_, v___y_5236_, v___y_5237_, v___y_5238_, v___y_5239_);
if (lean_obj_tag(v___x_5244_) == 0)
{
lean_object* v_a_5245_; 
v_a_5245_ = lean_ctor_get(v___x_5244_, 0);
lean_inc(v_a_5245_);
lean_dec_ref_known(v___x_5244_, 1);
v_x_5234_ = v_a_5245_;
v_x_5235_ = v_tail_5243_;
goto _start;
}
else
{
lean_dec(v_tail_5243_);
return v___x_5244_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg___boxed(lean_object* v_x_5247_, lean_object* v_x_5248_, lean_object* v___y_5249_, lean_object* v___y_5250_, lean_object* v___y_5251_, lean_object* v___y_5252_, lean_object* v___y_5253_){
_start:
{
lean_object* v_res_5254_; 
v_res_5254_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_x_5247_, v_x_5248_, v___y_5249_, v___y_5250_, v___y_5251_, v___y_5252_);
lean_dec(v___y_5252_);
lean_dec_ref(v___y_5251_);
lean_dec(v___y_5250_);
lean_dec_ref(v___y_5249_);
return v_res_5254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys___redArg(lean_object* v_t_5255_, lean_object* v_keys_5256_, lean_object* v_a_5257_, lean_object* v_a_5258_, lean_object* v_a_5259_, lean_object* v_a_5260_){
_start:
{
lean_object* v___x_5262_; 
v___x_5262_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_t_5255_, v_keys_5256_, v_a_5257_, v_a_5258_, v_a_5259_, v_a_5260_);
return v___x_5262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys___redArg___boxed(lean_object* v_t_5263_, lean_object* v_keys_5264_, lean_object* v_a_5265_, lean_object* v_a_5266_, lean_object* v_a_5267_, lean_object* v_a_5268_, lean_object* v_a_5269_){
_start:
{
lean_object* v_res_5270_; 
v_res_5270_ = l_Lean_Meta_LazyDiscrTree_dropKeys___redArg(v_t_5263_, v_keys_5264_, v_a_5265_, v_a_5266_, v_a_5267_, v_a_5268_);
lean_dec(v_a_5268_);
lean_dec_ref(v_a_5267_);
lean_dec(v_a_5266_);
lean_dec_ref(v_a_5265_);
return v_res_5270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys(lean_object* v_00_u03b1_5271_, lean_object* v_t_5272_, lean_object* v_keys_5273_, lean_object* v_a_5274_, lean_object* v_a_5275_, lean_object* v_a_5276_, lean_object* v_a_5277_){
_start:
{
lean_object* v___x_5279_; 
v___x_5279_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_t_5272_, v_keys_5273_, v_a_5274_, v_a_5275_, v_a_5276_, v_a_5277_);
return v___x_5279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys___boxed(lean_object* v_00_u03b1_5280_, lean_object* v_t_5281_, lean_object* v_keys_5282_, lean_object* v_a_5283_, lean_object* v_a_5284_, lean_object* v_a_5285_, lean_object* v_a_5286_, lean_object* v_a_5287_){
_start:
{
lean_object* v_res_5288_; 
v_res_5288_ = l_Lean_Meta_LazyDiscrTree_dropKeys(v_00_u03b1_5280_, v_t_5281_, v_keys_5282_, v_a_5283_, v_a_5284_, v_a_5285_, v_a_5286_);
lean_dec(v_a_5286_);
lean_dec_ref(v_a_5285_);
lean_dec(v_a_5284_);
lean_dec_ref(v_a_5283_);
return v_res_5288_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0(lean_object* v_00_u03b1_5289_, lean_object* v_x_5290_, lean_object* v_x_5291_, lean_object* v___y_5292_, lean_object* v___y_5293_, lean_object* v___y_5294_, lean_object* v___y_5295_){
_start:
{
lean_object* v___x_5297_; 
v___x_5297_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_x_5290_, v_x_5291_, v___y_5292_, v___y_5293_, v___y_5294_, v___y_5295_);
return v___x_5297_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___boxed(lean_object* v_00_u03b1_5298_, lean_object* v_x_5299_, lean_object* v_x_5300_, lean_object* v___y_5301_, lean_object* v___y_5302_, lean_object* v___y_5303_, lean_object* v___y_5304_, lean_object* v___y_5305_){
_start:
{
lean_object* v_res_5306_; 
v_res_5306_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0(v_00_u03b1_5298_, v_x_5299_, v_x_5300_, v___y_5301_, v___y_5302_, v___y_5303_, v___y_5304_);
lean_dec(v___y_5304_);
lean_dec_ref(v___y_5303_);
lean_dec(v___y_5302_);
lean_dec_ref(v___y_5301_);
return v_res_5306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(lean_object* v_as_5307_, size_t v_sz_5308_, size_t v_i_5309_, lean_object* v_b_5310_, lean_object* v___y_5311_, lean_object* v___y_5312_, lean_object* v___y_5313_, lean_object* v___y_5314_, lean_object* v___y_5315_){
_start:
{
uint8_t v___x_5317_; 
v___x_5317_ = lean_usize_dec_lt(v_i_5309_, v_sz_5308_);
if (v___x_5317_ == 0)
{
lean_object* v___x_5318_; 
v___x_5318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5318_, 0, v_b_5310_);
return v___x_5318_;
}
else
{
lean_object* v_a_5319_; lean_object* v___x_5320_; 
v_a_5319_ = lean_array_uget_borrowed(v_as_5307_, v_i_5309_);
v___x_5320_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(v_a_5319_, v_b_5310_, v___y_5311_, v___y_5312_, v___y_5313_, v___y_5314_, v___y_5315_);
if (lean_obj_tag(v___x_5320_) == 0)
{
lean_object* v_a_5321_; lean_object* v___x_5323_; uint8_t v_isShared_5324_; uint8_t v_isSharedCheck_5333_; 
v_a_5321_ = lean_ctor_get(v___x_5320_, 0);
v_isSharedCheck_5333_ = !lean_is_exclusive(v___x_5320_);
if (v_isSharedCheck_5333_ == 0)
{
v___x_5323_ = v___x_5320_;
v_isShared_5324_ = v_isSharedCheck_5333_;
goto v_resetjp_5322_;
}
else
{
lean_inc(v_a_5321_);
lean_dec(v___x_5320_);
v___x_5323_ = lean_box(0);
v_isShared_5324_ = v_isSharedCheck_5333_;
goto v_resetjp_5322_;
}
v_resetjp_5322_:
{
if (lean_obj_tag(v_a_5321_) == 0)
{
lean_object* v_a_5325_; lean_object* v___x_5327_; 
v_a_5325_ = lean_ctor_get(v_a_5321_, 0);
lean_inc(v_a_5325_);
lean_dec_ref_known(v_a_5321_, 1);
if (v_isShared_5324_ == 0)
{
lean_ctor_set(v___x_5323_, 0, v_a_5325_);
v___x_5327_ = v___x_5323_;
goto v_reusejp_5326_;
}
else
{
lean_object* v_reuseFailAlloc_5328_; 
v_reuseFailAlloc_5328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5328_, 0, v_a_5325_);
v___x_5327_ = v_reuseFailAlloc_5328_;
goto v_reusejp_5326_;
}
v_reusejp_5326_:
{
return v___x_5327_;
}
}
else
{
lean_object* v_a_5329_; size_t v___x_5330_; size_t v___x_5331_; 
lean_del_object(v___x_5323_);
v_a_5329_ = lean_ctor_get(v_a_5321_, 0);
lean_inc(v_a_5329_);
lean_dec_ref_known(v_a_5321_, 1);
v___x_5330_ = ((size_t)1ULL);
v___x_5331_ = lean_usize_add(v_i_5309_, v___x_5330_);
v_i_5309_ = v___x_5331_;
v_b_5310_ = v_a_5329_;
goto _start;
}
}
}
else
{
lean_object* v_a_5334_; lean_object* v___x_5336_; uint8_t v_isShared_5337_; uint8_t v_isSharedCheck_5341_; 
v_a_5334_ = lean_ctor_get(v___x_5320_, 0);
v_isSharedCheck_5341_ = !lean_is_exclusive(v___x_5320_);
if (v_isSharedCheck_5341_ == 0)
{
v___x_5336_ = v___x_5320_;
v_isShared_5337_ = v_isSharedCheck_5341_;
goto v_resetjp_5335_;
}
else
{
lean_inc(v_a_5334_);
lean_dec(v___x_5320_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(lean_object* v_next_5342_, lean_object* v_a_5343_, lean_object* v_a_5344_, lean_object* v_a_5345_, lean_object* v_a_5346_, lean_object* v_a_5347_){
_start:
{
lean_object* v___x_5349_; uint8_t v___x_5350_; 
v___x_5349_ = lean_unsigned_to_nat(0u);
v___x_5350_ = lean_nat_dec_eq(v_next_5342_, v___x_5349_);
if (v___x_5350_ == 0)
{
lean_object* v___x_5351_; 
v___x_5351_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_next_5342_, v_a_5343_, v_a_5344_, v_a_5345_, v_a_5346_, v_a_5347_);
if (lean_obj_tag(v___x_5351_) == 0)
{
lean_object* v_a_5352_; lean_object* v_snd_5353_; lean_object* v_fst_5354_; lean_object* v_fst_5355_; lean_object* v_snd_5356_; lean_object* v___x_5357_; 
v_a_5352_ = lean_ctor_get(v___x_5351_, 0);
lean_inc(v_a_5352_);
lean_dec_ref_known(v___x_5351_, 1);
v_snd_5353_ = lean_ctor_get(v_a_5352_, 1);
lean_inc(v_snd_5353_);
v_fst_5354_ = lean_ctor_get(v_a_5352_, 0);
lean_inc(v_fst_5354_);
lean_dec(v_a_5352_);
v_fst_5355_ = lean_ctor_get(v_snd_5353_, 0);
lean_inc(v_fst_5355_);
v_snd_5356_ = lean_ctor_get(v_snd_5353_, 1);
lean_inc(v_snd_5356_);
lean_dec(v_snd_5353_);
v___x_5357_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_fst_5355_, v_a_5343_, v_a_5344_, v_a_5345_, v_a_5346_, v_a_5347_);
if (lean_obj_tag(v___x_5357_) == 0)
{
lean_object* v_a_5358_; lean_object* v_buckets_5359_; lean_object* v___x_5360_; size_t v_sz_5361_; size_t v___x_5362_; lean_object* v___x_5363_; 
v_a_5358_ = lean_ctor_get(v___x_5357_, 0);
lean_inc(v_a_5358_);
lean_dec_ref_known(v___x_5357_, 1);
v_buckets_5359_ = lean_ctor_get(v_snd_5356_, 1);
v___x_5360_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v_sz_5361_ = lean_array_size(v_buckets_5359_);
v___x_5362_ = ((size_t)0ULL);
v___x_5363_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(v_buckets_5359_, v_sz_5361_, v___x_5362_, v___x_5360_, v_a_5343_, v_a_5344_, v_a_5345_, v_a_5346_, v_a_5347_);
if (lean_obj_tag(v___x_5363_) == 0)
{
lean_object* v_a_5364_; lean_object* v___x_5366_; uint8_t v_isShared_5367_; uint8_t v_isSharedCheck_5377_; 
v_a_5364_ = lean_ctor_get(v___x_5363_, 0);
v_isSharedCheck_5377_ = !lean_is_exclusive(v___x_5363_);
if (v_isSharedCheck_5377_ == 0)
{
v___x_5366_ = v___x_5363_;
v_isShared_5367_ = v_isSharedCheck_5377_;
goto v_resetjp_5365_;
}
else
{
lean_inc(v_a_5364_);
lean_dec(v___x_5363_);
v___x_5366_ = lean_box(0);
v_isShared_5367_ = v_isSharedCheck_5377_;
goto v_resetjp_5365_;
}
v_resetjp_5365_:
{
lean_object* v___x_5368_; lean_object* v___x_5369_; lean_object* v___x_5370_; lean_object* v___x_5371_; lean_object* v___x_5372_; lean_object* v___x_5373_; lean_object* v___x_5375_; 
v___x_5368_ = lean_st_ref_take(v_a_5343_);
v___x_5369_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5369_, 0, v___x_5360_);
lean_ctor_set(v___x_5369_, 1, v_fst_5355_);
lean_ctor_set(v___x_5369_, 2, v_snd_5356_);
lean_ctor_set(v___x_5369_, 3, v___x_5360_);
v___x_5370_ = lean_array_set(v___x_5368_, v_next_5342_, v___x_5369_);
v___x_5371_ = lean_st_ref_put(v_a_5343_, v___x_5370_);
v___x_5372_ = l_Array_append___redArg(v_fst_5354_, v_a_5358_);
lean_dec(v_a_5358_);
v___x_5373_ = l_Array_append___redArg(v___x_5372_, v_a_5364_);
lean_dec(v_a_5364_);
if (v_isShared_5367_ == 0)
{
lean_ctor_set(v___x_5366_, 0, v___x_5373_);
v___x_5375_ = v___x_5366_;
goto v_reusejp_5374_;
}
else
{
lean_object* v_reuseFailAlloc_5376_; 
v_reuseFailAlloc_5376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5376_, 0, v___x_5373_);
v___x_5375_ = v_reuseFailAlloc_5376_;
goto v_reusejp_5374_;
}
v_reusejp_5374_:
{
return v___x_5375_;
}
}
}
else
{
lean_dec(v_a_5358_);
lean_dec(v_snd_5356_);
lean_dec(v_fst_5355_);
lean_dec(v_fst_5354_);
return v___x_5363_;
}
}
else
{
lean_dec(v_snd_5356_);
lean_dec(v_fst_5355_);
lean_dec(v_fst_5354_);
return v___x_5357_;
}
}
else
{
lean_object* v_a_5378_; lean_object* v___x_5380_; uint8_t v_isShared_5381_; uint8_t v_isSharedCheck_5385_; 
v_a_5378_ = lean_ctor_get(v___x_5351_, 0);
v_isSharedCheck_5385_ = !lean_is_exclusive(v___x_5351_);
if (v_isSharedCheck_5385_ == 0)
{
v___x_5380_ = v___x_5351_;
v_isShared_5381_ = v_isSharedCheck_5385_;
goto v_resetjp_5379_;
}
else
{
lean_inc(v_a_5378_);
lean_dec(v___x_5351_);
v___x_5380_ = lean_box(0);
v_isShared_5381_ = v_isSharedCheck_5385_;
goto v_resetjp_5379_;
}
v_resetjp_5379_:
{
lean_object* v___x_5383_; 
if (v_isShared_5381_ == 0)
{
v___x_5383_ = v___x_5380_;
goto v_reusejp_5382_;
}
else
{
lean_object* v_reuseFailAlloc_5384_; 
v_reuseFailAlloc_5384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5384_, 0, v_a_5378_);
v___x_5383_ = v_reuseFailAlloc_5384_;
goto v_reusejp_5382_;
}
v_reusejp_5382_:
{
return v___x_5383_;
}
}
}
}
else
{
lean_object* v___x_5386_; lean_object* v___x_5387_; 
v___x_5386_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___x_5387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5387_, 0, v___x_5386_);
return v___x_5387_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(lean_object* v_a_5388_, lean_object* v_a_5389_, lean_object* v___y_5390_, lean_object* v___y_5391_, lean_object* v___y_5392_, lean_object* v___y_5393_, lean_object* v___y_5394_){
_start:
{
if (lean_obj_tag(v_a_5388_) == 0)
{
lean_object* v___x_5396_; lean_object* v___x_5397_; 
v___x_5396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5396_, 0, v_a_5389_);
v___x_5397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5397_, 0, v___x_5396_);
return v___x_5397_;
}
else
{
lean_object* v_value_5398_; lean_object* v_tail_5399_; lean_object* v___x_5400_; 
v_value_5398_ = lean_ctor_get(v_a_5388_, 1);
v_tail_5399_ = lean_ctor_get(v_a_5388_, 2);
v___x_5400_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_value_5398_, v___y_5390_, v___y_5391_, v___y_5392_, v___y_5393_, v___y_5394_);
if (lean_obj_tag(v___x_5400_) == 0)
{
lean_object* v_a_5401_; lean_object* v___x_5402_; 
v_a_5401_ = lean_ctor_get(v___x_5400_, 0);
lean_inc(v_a_5401_);
lean_dec_ref_known(v___x_5400_, 1);
v___x_5402_ = l_Array_append___redArg(v_a_5389_, v_a_5401_);
lean_dec(v_a_5401_);
v_a_5388_ = v_tail_5399_;
v_a_5389_ = v___x_5402_;
goto _start;
}
else
{
lean_object* v_a_5404_; lean_object* v___x_5406_; uint8_t v_isShared_5407_; uint8_t v_isSharedCheck_5411_; 
lean_dec_ref(v_a_5389_);
v_a_5404_ = lean_ctor_get(v___x_5400_, 0);
v_isSharedCheck_5411_ = !lean_is_exclusive(v___x_5400_);
if (v_isSharedCheck_5411_ == 0)
{
v___x_5406_ = v___x_5400_;
v_isShared_5407_ = v_isSharedCheck_5411_;
goto v_resetjp_5405_;
}
else
{
lean_inc(v_a_5404_);
lean_dec(v___x_5400_);
v___x_5406_ = lean_box(0);
v_isShared_5407_ = v_isSharedCheck_5411_;
goto v_resetjp_5405_;
}
v_resetjp_5405_:
{
lean_object* v___x_5409_; 
if (v_isShared_5407_ == 0)
{
v___x_5409_ = v___x_5406_;
goto v_reusejp_5408_;
}
else
{
lean_object* v_reuseFailAlloc_5410_; 
v_reuseFailAlloc_5410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5410_, 0, v_a_5404_);
v___x_5409_ = v_reuseFailAlloc_5410_;
goto v_reusejp_5408_;
}
v_reusejp_5408_:
{
return v___x_5409_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg___boxed(lean_object* v_a_5412_, lean_object* v_a_5413_, lean_object* v___y_5414_, lean_object* v___y_5415_, lean_object* v___y_5416_, lean_object* v___y_5417_, lean_object* v___y_5418_, lean_object* v___y_5419_){
_start:
{
lean_object* v_res_5420_; 
v_res_5420_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(v_a_5412_, v_a_5413_, v___y_5414_, v___y_5415_, v___y_5416_, v___y_5417_, v___y_5418_);
lean_dec(v___y_5418_);
lean_dec_ref(v___y_5417_);
lean_dec(v___y_5416_);
lean_dec_ref(v___y_5415_);
lean_dec(v___y_5414_);
lean_dec(v_a_5412_);
return v_res_5420_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg___boxed(lean_object* v_as_5421_, lean_object* v_sz_5422_, lean_object* v_i_5423_, lean_object* v_b_5424_, lean_object* v___y_5425_, lean_object* v___y_5426_, lean_object* v___y_5427_, lean_object* v___y_5428_, lean_object* v___y_5429_, lean_object* v___y_5430_){
_start:
{
size_t v_sz_boxed_5431_; size_t v_i_boxed_5432_; lean_object* v_res_5433_; 
v_sz_boxed_5431_ = lean_unbox_usize(v_sz_5422_);
lean_dec(v_sz_5422_);
v_i_boxed_5432_ = lean_unbox_usize(v_i_5423_);
lean_dec(v_i_5423_);
v_res_5433_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(v_as_5421_, v_sz_boxed_5431_, v_i_boxed_5432_, v_b_5424_, v___y_5425_, v___y_5426_, v___y_5427_, v___y_5428_, v___y_5429_);
lean_dec(v___y_5429_);
lean_dec_ref(v___y_5428_);
lean_dec(v___y_5427_);
lean_dec_ref(v___y_5426_);
lean_dec(v___y_5425_);
lean_dec_ref(v_as_5421_);
return v_res_5433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg___boxed(lean_object* v_next_5434_, lean_object* v_a_5435_, lean_object* v_a_5436_, lean_object* v_a_5437_, lean_object* v_a_5438_, lean_object* v_a_5439_, lean_object* v_a_5440_){
_start:
{
lean_object* v_res_5441_; 
v_res_5441_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_next_5434_, v_a_5435_, v_a_5436_, v_a_5437_, v_a_5438_, v_a_5439_);
lean_dec(v_a_5439_);
lean_dec_ref(v_a_5438_);
lean_dec(v_a_5437_);
lean_dec_ref(v_a_5436_);
lean_dec(v_a_5435_);
lean_dec(v_next_5434_);
return v_res_5441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux(lean_object* v_00_u03b1_5442_, lean_object* v_next_5443_, lean_object* v_a_5444_, lean_object* v_a_5445_, lean_object* v_a_5446_, lean_object* v_a_5447_, lean_object* v_a_5448_){
_start:
{
lean_object* v___x_5450_; 
v___x_5450_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_next_5443_, v_a_5444_, v_a_5445_, v_a_5446_, v_a_5447_, v_a_5448_);
return v___x_5450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___boxed(lean_object* v_00_u03b1_5451_, lean_object* v_next_5452_, lean_object* v_a_5453_, lean_object* v_a_5454_, lean_object* v_a_5455_, lean_object* v_a_5456_, lean_object* v_a_5457_, lean_object* v_a_5458_){
_start:
{
lean_object* v_res_5459_; 
v_res_5459_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux(v_00_u03b1_5451_, v_next_5452_, v_a_5453_, v_a_5454_, v_a_5455_, v_a_5456_, v_a_5457_);
lean_dec(v_a_5457_);
lean_dec_ref(v_a_5456_);
lean_dec(v_a_5455_);
lean_dec_ref(v_a_5454_);
lean_dec(v_a_5453_);
lean_dec(v_next_5452_);
return v_res_5459_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0(lean_object* v_00_u03b1_5460_, lean_object* v_a_5461_, lean_object* v_a_5462_, lean_object* v___y_5463_, lean_object* v___y_5464_, lean_object* v___y_5465_, lean_object* v___y_5466_, lean_object* v___y_5467_){
_start:
{
lean_object* v___x_5469_; 
v___x_5469_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(v_a_5461_, v_a_5462_, v___y_5463_, v___y_5464_, v___y_5465_, v___y_5466_, v___y_5467_);
return v___x_5469_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___boxed(lean_object* v_00_u03b1_5470_, lean_object* v_a_5471_, lean_object* v_a_5472_, lean_object* v___y_5473_, lean_object* v___y_5474_, lean_object* v___y_5475_, lean_object* v___y_5476_, lean_object* v___y_5477_, lean_object* v___y_5478_){
_start:
{
lean_object* v_res_5479_; 
v_res_5479_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0(v_00_u03b1_5470_, v_a_5471_, v_a_5472_, v___y_5473_, v___y_5474_, v___y_5475_, v___y_5476_, v___y_5477_);
lean_dec(v___y_5477_);
lean_dec_ref(v___y_5476_);
lean_dec(v___y_5475_);
lean_dec_ref(v___y_5474_);
lean_dec(v___y_5473_);
lean_dec(v_a_5471_);
return v_res_5479_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1(lean_object* v_00_u03b1_5480_, lean_object* v_as_5481_, size_t v_sz_5482_, size_t v_i_5483_, lean_object* v_b_5484_, lean_object* v___y_5485_, lean_object* v___y_5486_, lean_object* v___y_5487_, lean_object* v___y_5488_, lean_object* v___y_5489_){
_start:
{
lean_object* v___x_5491_; 
v___x_5491_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(v_as_5481_, v_sz_5482_, v_i_5483_, v_b_5484_, v___y_5485_, v___y_5486_, v___y_5487_, v___y_5488_, v___y_5489_);
return v___x_5491_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___boxed(lean_object* v_00_u03b1_5492_, lean_object* v_as_5493_, lean_object* v_sz_5494_, lean_object* v_i_5495_, lean_object* v_b_5496_, lean_object* v___y_5497_, lean_object* v___y_5498_, lean_object* v___y_5499_, lean_object* v___y_5500_, lean_object* v___y_5501_, lean_object* v___y_5502_){
_start:
{
size_t v_sz_boxed_5503_; size_t v_i_boxed_5504_; lean_object* v_res_5505_; 
v_sz_boxed_5503_ = lean_unbox_usize(v_sz_5494_);
lean_dec(v_sz_5494_);
v_i_boxed_5504_ = lean_unbox_usize(v_i_5495_);
lean_dec(v_i_5495_);
v_res_5505_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1(v_00_u03b1_5492_, v_as_5493_, v_sz_boxed_5503_, v_i_boxed_5504_, v_b_5496_, v___y_5497_, v___y_5498_, v___y_5499_, v___y_5500_, v___y_5501_);
lean_dec(v___y_5501_);
lean_dec_ref(v___y_5500_);
lean_dec(v___y_5499_);
lean_dec_ref(v___y_5498_);
lean_dec(v___y_5497_);
lean_dec_ref(v_as_5493_);
return v_res_5505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg(lean_object* v_next_5506_, lean_object* v_rest_5507_, lean_object* v_a_5508_, lean_object* v_a_5509_, lean_object* v_a_5510_, lean_object* v_a_5511_, lean_object* v_a_5512_){
_start:
{
lean_object* v___x_5514_; uint8_t v___x_5515_; 
v___x_5514_ = lean_unsigned_to_nat(0u);
v___x_5515_ = lean_nat_dec_eq(v_next_5506_, v___x_5514_);
if (v___x_5515_ == 0)
{
lean_object* v___x_5516_; 
v___x_5516_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_next_5506_, v_a_5508_, v_a_5509_, v_a_5510_, v_a_5511_, v_a_5512_);
if (lean_obj_tag(v___x_5516_) == 0)
{
lean_object* v_a_5517_; lean_object* v_snd_5518_; 
v_a_5517_ = lean_ctor_get(v___x_5516_, 0);
lean_inc(v_a_5517_);
lean_dec_ref_known(v___x_5516_, 1);
v_snd_5518_ = lean_ctor_get(v_a_5517_, 1);
lean_inc(v_snd_5518_);
lean_dec(v_a_5517_);
if (lean_obj_tag(v_rest_5507_) == 0)
{
lean_object* v___x_5519_; 
lean_dec(v_snd_5518_);
v___x_5519_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_next_5506_, v_a_5508_, v_a_5509_, v_a_5510_, v_a_5511_, v_a_5512_);
lean_dec(v_next_5506_);
return v___x_5519_;
}
else
{
lean_object* v_fst_5520_; lean_object* v_snd_5521_; lean_object* v_head_5522_; lean_object* v_tail_5523_; lean_object* v___x_5524_; uint8_t v___x_5525_; 
lean_dec(v_next_5506_);
v_fst_5520_ = lean_ctor_get(v_snd_5518_, 0);
lean_inc(v_fst_5520_);
v_snd_5521_ = lean_ctor_get(v_snd_5518_, 1);
lean_inc(v_snd_5521_);
lean_dec(v_snd_5518_);
v_head_5522_ = lean_ctor_get(v_rest_5507_, 0);
v_tail_5523_ = lean_ctor_get(v_rest_5507_, 1);
v___x_5524_ = lean_box(3);
v___x_5525_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_head_5522_, v___x_5524_);
if (v___x_5525_ == 0)
{
lean_object* v___x_5526_; 
lean_dec(v_fst_5520_);
v___x_5526_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_snd_5521_, v_head_5522_, v___x_5514_);
lean_dec(v_snd_5521_);
v_next_5506_ = v___x_5526_;
v_rest_5507_ = v_tail_5523_;
goto _start;
}
else
{
lean_dec(v_snd_5521_);
v_next_5506_ = v_fst_5520_;
v_rest_5507_ = v_tail_5523_;
goto _start;
}
}
}
else
{
lean_object* v_a_5529_; lean_object* v___x_5531_; uint8_t v_isShared_5532_; uint8_t v_isSharedCheck_5536_; 
lean_dec(v_next_5506_);
v_a_5529_ = lean_ctor_get(v___x_5516_, 0);
v_isSharedCheck_5536_ = !lean_is_exclusive(v___x_5516_);
if (v_isSharedCheck_5536_ == 0)
{
v___x_5531_ = v___x_5516_;
v_isShared_5532_ = v_isSharedCheck_5536_;
goto v_resetjp_5530_;
}
else
{
lean_inc(v_a_5529_);
lean_dec(v___x_5516_);
v___x_5531_ = lean_box(0);
v_isShared_5532_ = v_isSharedCheck_5536_;
goto v_resetjp_5530_;
}
v_resetjp_5530_:
{
lean_object* v___x_5534_; 
if (v_isShared_5532_ == 0)
{
v___x_5534_ = v___x_5531_;
goto v_reusejp_5533_;
}
else
{
lean_object* v_reuseFailAlloc_5535_; 
v_reuseFailAlloc_5535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5535_, 0, v_a_5529_);
v___x_5534_ = v_reuseFailAlloc_5535_;
goto v_reusejp_5533_;
}
v_reusejp_5533_:
{
return v___x_5534_;
}
}
}
}
else
{
lean_object* v___x_5537_; lean_object* v___x_5538_; 
lean_dec(v_next_5506_);
v___x_5537_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___x_5538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5538_, 0, v___x_5537_);
return v___x_5538_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg___boxed(lean_object* v_next_5539_, lean_object* v_rest_5540_, lean_object* v_a_5541_, lean_object* v_a_5542_, lean_object* v_a_5543_, lean_object* v_a_5544_, lean_object* v_a_5545_, lean_object* v_a_5546_){
_start:
{
lean_object* v_res_5547_; 
v_res_5547_ = l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg(v_next_5539_, v_rest_5540_, v_a_5541_, v_a_5542_, v_a_5543_, v_a_5544_, v_a_5545_);
lean_dec(v_a_5545_);
lean_dec_ref(v_a_5544_);
lean_dec(v_a_5543_);
lean_dec_ref(v_a_5542_);
lean_dec(v_a_5541_);
lean_dec(v_rest_5540_);
return v_res_5547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux(lean_object* v_00_u03b1_5548_, lean_object* v_next_5549_, lean_object* v_rest_5550_, lean_object* v_a_5551_, lean_object* v_a_5552_, lean_object* v_a_5553_, lean_object* v_a_5554_, lean_object* v_a_5555_){
_start:
{
lean_object* v___x_5557_; 
v___x_5557_ = l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg(v_next_5549_, v_rest_5550_, v_a_5551_, v_a_5552_, v_a_5553_, v_a_5554_, v_a_5555_);
return v___x_5557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux___boxed(lean_object* v_00_u03b1_5558_, lean_object* v_next_5559_, lean_object* v_rest_5560_, lean_object* v_a_5561_, lean_object* v_a_5562_, lean_object* v_a_5563_, lean_object* v_a_5564_, lean_object* v_a_5565_, lean_object* v_a_5566_){
_start:
{
lean_object* v_res_5567_; 
v_res_5567_ = l_Lean_Meta_LazyDiscrTree_extractKeyAux(v_00_u03b1_5558_, v_next_5559_, v_rest_5560_, v_a_5561_, v_a_5562_, v_a_5563_, v_a_5564_, v_a_5565_);
lean_dec(v_a_5565_);
lean_dec_ref(v_a_5564_);
lean_dec(v_a_5563_);
lean_dec_ref(v_a_5562_);
lean_dec(v_a_5561_);
lean_dec(v_rest_5560_);
return v_res_5567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey___redArg(lean_object* v_t_5568_, lean_object* v_path_5569_, lean_object* v_a_5570_, lean_object* v_a_5571_, lean_object* v_a_5572_, lean_object* v_a_5573_){
_start:
{
if (lean_obj_tag(v_path_5569_) == 0)
{
lean_object* v___x_5575_; lean_object* v___x_5576_; lean_object* v___x_5577_; 
v___x_5575_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___x_5576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5576_, 0, v___x_5575_);
lean_ctor_set(v___x_5576_, 1, v_t_5568_);
v___x_5577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5577_, 0, v___x_5576_);
return v___x_5577_;
}
else
{
lean_object* v_head_5578_; lean_object* v_tail_5579_; lean_object* v_roots_5580_; lean_object* v___x_5581_; lean_object* v_idx_5582_; lean_object* v___x_5583_; lean_object* v___x_5584_; 
v_head_5578_ = lean_ctor_get(v_path_5569_, 0);
lean_inc(v_head_5578_);
v_tail_5579_ = lean_ctor_get(v_path_5569_, 1);
lean_inc(v_tail_5579_);
lean_dec_ref_known(v_path_5569_, 2);
v_roots_5580_ = lean_ctor_get(v_t_5568_, 1);
v___x_5581_ = lean_unsigned_to_nat(0u);
v_idx_5582_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_roots_5580_, v_head_5578_, v___x_5581_);
lean_dec(v_head_5578_);
v___x_5583_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_extractKeyAux___boxed), 9, 3);
lean_closure_set(v___x_5583_, 0, lean_box(0));
lean_closure_set(v___x_5583_, 1, v_idx_5582_);
lean_closure_set(v___x_5583_, 2, v_tail_5579_);
v___x_5584_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_t_5568_, v___x_5583_, v_a_5570_, v_a_5571_, v_a_5572_, v_a_5573_);
return v___x_5584_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey___redArg___boxed(lean_object* v_t_5585_, lean_object* v_path_5586_, lean_object* v_a_5587_, lean_object* v_a_5588_, lean_object* v_a_5589_, lean_object* v_a_5590_, lean_object* v_a_5591_){
_start:
{
lean_object* v_res_5592_; 
v_res_5592_ = l_Lean_Meta_LazyDiscrTree_extractKey___redArg(v_t_5585_, v_path_5586_, v_a_5587_, v_a_5588_, v_a_5589_, v_a_5590_);
lean_dec(v_a_5590_);
lean_dec_ref(v_a_5589_);
lean_dec(v_a_5588_);
lean_dec_ref(v_a_5587_);
return v_res_5592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey(lean_object* v_00_u03b1_5593_, lean_object* v_t_5594_, lean_object* v_path_5595_, lean_object* v_a_5596_, lean_object* v_a_5597_, lean_object* v_a_5598_, lean_object* v_a_5599_){
_start:
{
lean_object* v___x_5601_; 
v___x_5601_ = l_Lean_Meta_LazyDiscrTree_extractKey___redArg(v_t_5594_, v_path_5595_, v_a_5596_, v_a_5597_, v_a_5598_, v_a_5599_);
return v___x_5601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey___boxed(lean_object* v_00_u03b1_5602_, lean_object* v_t_5603_, lean_object* v_path_5604_, lean_object* v_a_5605_, lean_object* v_a_5606_, lean_object* v_a_5607_, lean_object* v_a_5608_, lean_object* v_a_5609_){
_start:
{
lean_object* v_res_5610_; 
v_res_5610_ = l_Lean_Meta_LazyDiscrTree_extractKey(v_00_u03b1_5602_, v_t_5603_, v_path_5604_, v_a_5605_, v_a_5606_, v_a_5607_, v_a_5608_);
lean_dec(v_a_5608_);
lean_dec_ref(v_a_5607_);
lean_dec(v_a_5606_);
lean_dec_ref(v_a_5605_);
return v_res_5610_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(lean_object* v_as_x27_5611_, lean_object* v_b_5612_, lean_object* v___y_5613_, lean_object* v___y_5614_, lean_object* v___y_5615_, lean_object* v___y_5616_){
_start:
{
if (lean_obj_tag(v_as_x27_5611_) == 0)
{
lean_object* v___x_5618_; 
v___x_5618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5618_, 0, v_b_5612_);
return v___x_5618_;
}
else
{
lean_object* v_head_5619_; lean_object* v_tail_5620_; lean_object* v_fst_5621_; lean_object* v_snd_5622_; lean_object* v___x_5623_; 
v_head_5619_ = lean_ctor_get(v_as_x27_5611_, 0);
v_tail_5620_ = lean_ctor_get(v_as_x27_5611_, 1);
v_fst_5621_ = lean_ctor_get(v_b_5612_, 0);
lean_inc(v_fst_5621_);
v_snd_5622_ = lean_ctor_get(v_b_5612_, 1);
lean_inc(v_snd_5622_);
lean_dec_ref(v_b_5612_);
lean_inc(v_head_5619_);
v___x_5623_ = l_Lean_Meta_LazyDiscrTree_extractKey___redArg(v_snd_5622_, v_head_5619_, v___y_5613_, v___y_5614_, v___y_5615_, v___y_5616_);
if (lean_obj_tag(v___x_5623_) == 0)
{
lean_object* v_a_5624_; lean_object* v_fst_5625_; lean_object* v_snd_5626_; lean_object* v___x_5628_; uint8_t v_isShared_5629_; uint8_t v_isSharedCheck_5635_; 
v_a_5624_ = lean_ctor_get(v___x_5623_, 0);
lean_inc(v_a_5624_);
lean_dec_ref_known(v___x_5623_, 1);
v_fst_5625_ = lean_ctor_get(v_a_5624_, 0);
v_snd_5626_ = lean_ctor_get(v_a_5624_, 1);
v_isSharedCheck_5635_ = !lean_is_exclusive(v_a_5624_);
if (v_isSharedCheck_5635_ == 0)
{
v___x_5628_ = v_a_5624_;
v_isShared_5629_ = v_isSharedCheck_5635_;
goto v_resetjp_5627_;
}
else
{
lean_inc(v_snd_5626_);
lean_inc(v_fst_5625_);
lean_dec(v_a_5624_);
v___x_5628_ = lean_box(0);
v_isShared_5629_ = v_isSharedCheck_5635_;
goto v_resetjp_5627_;
}
v_resetjp_5627_:
{
lean_object* v___x_5630_; lean_object* v___x_5632_; 
v___x_5630_ = l_Array_append___redArg(v_fst_5621_, v_fst_5625_);
lean_dec(v_fst_5625_);
if (v_isShared_5629_ == 0)
{
lean_ctor_set(v___x_5628_, 0, v___x_5630_);
v___x_5632_ = v___x_5628_;
goto v_reusejp_5631_;
}
else
{
lean_object* v_reuseFailAlloc_5634_; 
v_reuseFailAlloc_5634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5634_, 0, v___x_5630_);
lean_ctor_set(v_reuseFailAlloc_5634_, 1, v_snd_5626_);
v___x_5632_ = v_reuseFailAlloc_5634_;
goto v_reusejp_5631_;
}
v_reusejp_5631_:
{
v_as_x27_5611_ = v_tail_5620_;
v_b_5612_ = v___x_5632_;
goto _start;
}
}
}
else
{
lean_dec(v_fst_5621_);
return v___x_5623_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg___boxed(lean_object* v_as_x27_5636_, lean_object* v_b_5637_, lean_object* v___y_5638_, lean_object* v___y_5639_, lean_object* v___y_5640_, lean_object* v___y_5641_, lean_object* v___y_5642_){
_start:
{
lean_object* v_res_5643_; 
v_res_5643_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(v_as_x27_5636_, v_b_5637_, v___y_5638_, v___y_5639_, v___y_5640_, v___y_5641_);
lean_dec(v___y_5641_);
lean_dec_ref(v___y_5640_);
lean_dec(v___y_5639_);
lean_dec_ref(v___y_5638_);
lean_dec(v_as_x27_5636_);
return v_res_5643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(lean_object* v_t_5644_, lean_object* v_keys_5645_, lean_object* v_a_5646_, lean_object* v_a_5647_, lean_object* v_a_5648_, lean_object* v_a_5649_){
_start:
{
lean_object* v_allExtracted_5651_; lean_object* v___x_5652_; lean_object* v___x_5653_; 
v_allExtracted_5651_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___x_5652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5652_, 0, v_allExtracted_5651_);
lean_ctor_set(v___x_5652_, 1, v_t_5644_);
v___x_5653_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(v_keys_5645_, v___x_5652_, v_a_5646_, v_a_5647_, v_a_5648_, v_a_5649_);
if (lean_obj_tag(v___x_5653_) == 0)
{
lean_object* v_a_5654_; lean_object* v___x_5656_; uint8_t v_isShared_5657_; uint8_t v_isSharedCheck_5670_; 
v_a_5654_ = lean_ctor_get(v___x_5653_, 0);
v_isSharedCheck_5670_ = !lean_is_exclusive(v___x_5653_);
if (v_isSharedCheck_5670_ == 0)
{
v___x_5656_ = v___x_5653_;
v_isShared_5657_ = v_isSharedCheck_5670_;
goto v_resetjp_5655_;
}
else
{
lean_inc(v_a_5654_);
lean_dec(v___x_5653_);
v___x_5656_ = lean_box(0);
v_isShared_5657_ = v_isSharedCheck_5670_;
goto v_resetjp_5655_;
}
v_resetjp_5655_:
{
lean_object* v_fst_5658_; lean_object* v_snd_5659_; lean_object* v___x_5661_; uint8_t v_isShared_5662_; uint8_t v_isSharedCheck_5669_; 
v_fst_5658_ = lean_ctor_get(v_a_5654_, 0);
v_snd_5659_ = lean_ctor_get(v_a_5654_, 1);
v_isSharedCheck_5669_ = !lean_is_exclusive(v_a_5654_);
if (v_isSharedCheck_5669_ == 0)
{
v___x_5661_ = v_a_5654_;
v_isShared_5662_ = v_isSharedCheck_5669_;
goto v_resetjp_5660_;
}
else
{
lean_inc(v_snd_5659_);
lean_inc(v_fst_5658_);
lean_dec(v_a_5654_);
v___x_5661_ = lean_box(0);
v_isShared_5662_ = v_isSharedCheck_5669_;
goto v_resetjp_5660_;
}
v_resetjp_5660_:
{
lean_object* v___x_5664_; 
if (v_isShared_5662_ == 0)
{
v___x_5664_ = v___x_5661_;
goto v_reusejp_5663_;
}
else
{
lean_object* v_reuseFailAlloc_5668_; 
v_reuseFailAlloc_5668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5668_, 0, v_fst_5658_);
lean_ctor_set(v_reuseFailAlloc_5668_, 1, v_snd_5659_);
v___x_5664_ = v_reuseFailAlloc_5668_;
goto v_reusejp_5663_;
}
v_reusejp_5663_:
{
lean_object* v___x_5666_; 
if (v_isShared_5657_ == 0)
{
lean_ctor_set(v___x_5656_, 0, v___x_5664_);
v___x_5666_ = v___x_5656_;
goto v_reusejp_5665_;
}
else
{
lean_object* v_reuseFailAlloc_5667_; 
v_reuseFailAlloc_5667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5667_, 0, v___x_5664_);
v___x_5666_ = v_reuseFailAlloc_5667_;
goto v_reusejp_5665_;
}
v_reusejp_5665_:
{
return v___x_5666_;
}
}
}
}
}
else
{
return v___x_5653_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys___redArg___boxed(lean_object* v_t_5671_, lean_object* v_keys_5672_, lean_object* v_a_5673_, lean_object* v_a_5674_, lean_object* v_a_5675_, lean_object* v_a_5676_, lean_object* v_a_5677_){
_start:
{
lean_object* v_res_5678_; 
v_res_5678_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_t_5671_, v_keys_5672_, v_a_5673_, v_a_5674_, v_a_5675_, v_a_5676_);
lean_dec(v_a_5676_);
lean_dec_ref(v_a_5675_);
lean_dec(v_a_5674_);
lean_dec_ref(v_a_5673_);
lean_dec(v_keys_5672_);
return v_res_5678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys(lean_object* v_00_u03b1_5679_, lean_object* v_t_5680_, lean_object* v_keys_5681_, lean_object* v_a_5682_, lean_object* v_a_5683_, lean_object* v_a_5684_, lean_object* v_a_5685_){
_start:
{
lean_object* v___x_5687_; 
v___x_5687_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_t_5680_, v_keys_5681_, v_a_5682_, v_a_5683_, v_a_5684_, v_a_5685_);
return v___x_5687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys___boxed(lean_object* v_00_u03b1_5688_, lean_object* v_t_5689_, lean_object* v_keys_5690_, lean_object* v_a_5691_, lean_object* v_a_5692_, lean_object* v_a_5693_, lean_object* v_a_5694_, lean_object* v_a_5695_){
_start:
{
lean_object* v_res_5696_; 
v_res_5696_ = l_Lean_Meta_LazyDiscrTree_extractKeys(v_00_u03b1_5688_, v_t_5689_, v_keys_5690_, v_a_5691_, v_a_5692_, v_a_5693_, v_a_5694_);
lean_dec(v_a_5694_);
lean_dec_ref(v_a_5693_);
lean_dec(v_a_5692_);
lean_dec_ref(v_a_5691_);
lean_dec(v_keys_5690_);
return v_res_5696_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0(lean_object* v_00_u03b1_5697_, lean_object* v_as_5698_, lean_object* v_as_x27_5699_, lean_object* v_b_5700_, lean_object* v_a_5701_, lean_object* v___y_5702_, lean_object* v___y_5703_, lean_object* v___y_5704_, lean_object* v___y_5705_){
_start:
{
lean_object* v___x_5707_; 
v___x_5707_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(v_as_x27_5699_, v_b_5700_, v___y_5702_, v___y_5703_, v___y_5704_, v___y_5705_);
return v___x_5707_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___boxed(lean_object* v_00_u03b1_5708_, lean_object* v_as_5709_, lean_object* v_as_x27_5710_, lean_object* v_b_5711_, lean_object* v_a_5712_, lean_object* v___y_5713_, lean_object* v___y_5714_, lean_object* v___y_5715_, lean_object* v___y_5716_, lean_object* v___y_5717_){
_start:
{
lean_object* v_res_5718_; 
v_res_5718_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0(v_00_u03b1_5708_, v_as_5709_, v_as_x27_5710_, v_b_5711_, v_a_5712_, v___y_5713_, v___y_5714_, v___y_5715_, v___y_5716_);
lean_dec(v___y_5716_);
lean_dec_ref(v___y_5715_);
lean_dec(v___y_5714_);
lean_dec_ref(v___y_5713_);
lean_dec(v_as_x27_5710_);
lean_dec(v_as_5709_);
return v_res_5718_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1(void){
_start:
{
lean_object* v___x_5720_; lean_object* v___x_5721_; 
v___x_5720_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__0));
v___x_5721_ = l_Lean_stringToMessageData(v___x_5720_);
return v___x_5721_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3(void){
_start:
{
lean_object* v___x_5723_; lean_object* v___x_5724_; 
v___x_5723_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__2));
v___x_5724_ = l_Lean_stringToMessageData(v___x_5723_);
return v___x_5724_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5(void){
_start:
{
lean_object* v___x_5726_; lean_object* v___x_5727_; 
v___x_5726_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__4));
v___x_5727_ = l_Lean_stringToMessageData(v___x_5726_);
return v___x_5727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg(lean_object* v_inst_5728_, lean_object* v_inst_5729_, lean_object* v_inst_5730_, lean_object* v_inst_5731_, lean_object* v_f_5732_){
_start:
{
lean_object* v_module_5733_; lean_object* v_const_5734_; lean_object* v_exception_5735_; lean_object* v___x_5736_; lean_object* v___x_5737_; lean_object* v___x_5738_; lean_object* v___x_5739_; lean_object* v___x_5740_; lean_object* v___x_5741_; lean_object* v___x_5742_; lean_object* v___x_5743_; lean_object* v___x_5744_; lean_object* v___x_5745_; lean_object* v___x_5746_; lean_object* v___x_5747_; 
v_module_5733_ = lean_ctor_get(v_f_5732_, 0);
lean_inc(v_module_5733_);
v_const_5734_ = lean_ctor_get(v_f_5732_, 1);
lean_inc(v_const_5734_);
v_exception_5735_ = lean_ctor_get(v_f_5732_, 2);
lean_inc_ref(v_exception_5735_);
lean_dec_ref(v_f_5732_);
v___x_5736_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1);
v___x_5737_ = l_Lean_MessageData_ofName(v_const_5734_);
v___x_5738_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5738_, 0, v___x_5736_);
lean_ctor_set(v___x_5738_, 1, v___x_5737_);
v___x_5739_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3);
v___x_5740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5740_, 0, v___x_5738_);
lean_ctor_set(v___x_5740_, 1, v___x_5739_);
v___x_5741_ = l_Lean_MessageData_ofName(v_module_5733_);
v___x_5742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5742_, 0, v___x_5740_);
lean_ctor_set(v___x_5742_, 1, v___x_5741_);
v___x_5743_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5);
v___x_5744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5744_, 0, v___x_5742_);
lean_ctor_set(v___x_5744_, 1, v___x_5743_);
v___x_5745_ = l_Lean_Exception_toMessageData(v_exception_5735_);
v___x_5746_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5746_, 0, v___x_5744_);
lean_ctor_set(v___x_5746_, 1, v___x_5745_);
v___x_5747_ = l_Lean_logError___redArg(v_inst_5728_, v_inst_5729_, v_inst_5730_, v_inst_5731_, v___x_5746_);
return v___x_5747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure(lean_object* v_m_5748_, lean_object* v_inst_5749_, lean_object* v_inst_5750_, lean_object* v_inst_5751_, lean_object* v_inst_5752_, lean_object* v_f_5753_){
_start:
{
lean_object* v___x_5754_; 
v___x_5754_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg(v_inst_5749_, v_inst_5750_, v_inst_5751_, v_inst_5752_, v_f_5753_);
return v___x_5754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__0(lean_object* v_tasks_5755_, lean_object* v_toPure_5756_, lean_object* v_t_5757_){
_start:
{
lean_object* v___x_5758_; lean_object* v___x_5759_; 
v___x_5758_ = lean_array_push(v_tasks_5755_, v_t_5757_);
v___x_5759_ = lean_apply_2(v_toPure_5756_, lean_box(0), v___x_5758_);
return v___x_5759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(lean_object* v_inst_5760_, lean_object* v_inst_5761_, lean_object* v_cctx_5762_, lean_object* v_env_5763_, lean_object* v_act_5764_, lean_object* v_constantsPerTask_5765_, lean_object* v_n_5766_, lean_object* v_ngen_5767_, lean_object* v_tasks_5768_, lean_object* v_start_5769_, lean_object* v_cnt_5770_, lean_object* v_idx_5771_){
_start:
{
lean_object* v___x_5772_; lean_object* v_toApplicative_5773_; lean_object* v_moduleData_5774_; lean_object* v_toBind_5775_; lean_object* v_toPure_5776_; lean_object* v___x_5777_; uint8_t v___x_5778_; 
v___x_5772_ = l_Lean_Environment_header(v_env_5763_);
v_toApplicative_5773_ = lean_ctor_get(v_inst_5760_, 0);
v_moduleData_5774_ = lean_ctor_get(v___x_5772_, 6);
lean_inc_ref(v_moduleData_5774_);
lean_dec_ref(v___x_5772_);
v_toBind_5775_ = lean_ctor_get(v_inst_5760_, 1);
v_toPure_5776_ = lean_ctor_get(v_toApplicative_5773_, 1);
v___x_5777_ = lean_array_get_size(v_moduleData_5774_);
v___x_5778_ = lean_nat_dec_lt(v_idx_5771_, v___x_5777_);
if (v___x_5778_ == 0)
{
uint8_t v___x_5779_; 
lean_inc(v_toPure_5776_);
lean_inc(v_toBind_5775_);
lean_dec_ref(v_moduleData_5774_);
lean_dec(v_idx_5771_);
lean_dec(v_cnt_5770_);
lean_dec(v_constantsPerTask_5765_);
lean_dec_ref(v_inst_5760_);
v___x_5779_ = lean_nat_dec_lt(v_start_5769_, v_n_5766_);
if (v___x_5779_ == 0)
{
lean_object* v___x_5780_; 
lean_dec(v_toBind_5775_);
lean_dec(v_start_5769_);
lean_dec_ref(v_ngen_5767_);
lean_dec(v_n_5766_);
lean_dec_ref(v_act_5764_);
lean_dec_ref(v_env_5763_);
lean_dec_ref(v_cctx_5762_);
lean_dec(v_inst_5761_);
v___x_5780_ = lean_apply_2(v_toPure_5776_, lean_box(0), v_tasks_5768_);
return v___x_5780_;
}
else
{
lean_object* v_namePrefix_5781_; lean_object* v_idx_5782_; lean_object* v___x_5784_; uint8_t v_isShared_5785_; uint8_t v_isSharedCheck_5797_; 
v_namePrefix_5781_ = lean_ctor_get(v_ngen_5767_, 0);
v_idx_5782_ = lean_ctor_get(v_ngen_5767_, 1);
v_isSharedCheck_5797_ = !lean_is_exclusive(v_ngen_5767_);
if (v_isSharedCheck_5797_ == 0)
{
v___x_5784_ = v_ngen_5767_;
v_isShared_5785_ = v_isSharedCheck_5797_;
goto v_resetjp_5783_;
}
else
{
lean_inc(v_idx_5782_);
lean_inc(v_namePrefix_5781_);
lean_dec(v_ngen_5767_);
v___x_5784_ = lean_box(0);
v_isShared_5785_ = v_isSharedCheck_5797_;
goto v_resetjp_5783_;
}
v_resetjp_5783_:
{
lean_object* v___f_5786_; lean_object* v___x_5787_; lean_object* v___x_5788_; lean_object* v___x_5790_; 
v___f_5786_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5786_, 0, v_tasks_5768_);
lean_closure_set(v___f_5786_, 1, v_toPure_5776_);
v___x_5787_ = l_Lean_Name_num___override(v_namePrefix_5781_, v_idx_5782_);
v___x_5788_ = lean_unsigned_to_nat(1u);
if (v_isShared_5785_ == 0)
{
lean_ctor_set(v___x_5784_, 1, v___x_5788_);
lean_ctor_set(v___x_5784_, 0, v___x_5787_);
v___x_5790_ = v___x_5784_;
goto v_reusejp_5789_;
}
else
{
lean_object* v_reuseFailAlloc_5796_; 
v_reuseFailAlloc_5796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5796_, 0, v___x_5787_);
lean_ctor_set(v_reuseFailAlloc_5796_, 1, v___x_5788_);
v___x_5790_ = v_reuseFailAlloc_5796_;
goto v_reusejp_5789_;
}
v_reusejp_5789_:
{
lean_object* v___x_5791_; lean_object* v___x_5792_; lean_object* v___x_5793_; lean_object* v___x_5794_; lean_object* v___x_5795_; 
v___x_5791_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_5791_, 0, lean_box(0));
lean_closure_set(v___x_5791_, 1, v_cctx_5762_);
lean_closure_set(v___x_5791_, 2, v___x_5790_);
lean_closure_set(v___x_5791_, 3, v_env_5763_);
lean_closure_set(v___x_5791_, 4, v_act_5764_);
lean_closure_set(v___x_5791_, 5, v_start_5769_);
lean_closure_set(v___x_5791_, 6, v_n_5766_);
v___x_5792_ = lean_unsigned_to_nat(0u);
v___x_5793_ = lean_alloc_closure((void*)(l_BaseIO_asTask___boxed), 4, 3);
lean_closure_set(v___x_5793_, 0, lean_box(0));
lean_closure_set(v___x_5793_, 1, v___x_5791_);
lean_closure_set(v___x_5793_, 2, v___x_5792_);
v___x_5794_ = lean_apply_2(v_inst_5761_, lean_box(0), v___x_5793_);
v___x_5795_ = lean_apply_4(v_toBind_5775_, lean_box(0), lean_box(0), v___x_5794_, v___f_5786_);
return v___x_5795_;
}
}
}
}
else
{
lean_object* v_mdata_5798_; lean_object* v_constants_5799_; lean_object* v___x_5800_; lean_object* v_cnt_5801_; uint8_t v___x_5802_; 
v_mdata_5798_ = lean_array_fget(v_moduleData_5774_, v_idx_5771_);
lean_dec_ref(v_moduleData_5774_);
v_constants_5799_ = lean_ctor_get(v_mdata_5798_, 2);
lean_inc_ref(v_constants_5799_);
lean_dec(v_mdata_5798_);
v___x_5800_ = lean_array_get_size(v_constants_5799_);
lean_dec_ref(v_constants_5799_);
v_cnt_5801_ = lean_nat_add(v_cnt_5770_, v___x_5800_);
lean_dec(v_cnt_5770_);
v___x_5802_ = lean_nat_dec_lt(v_constantsPerTask_5765_, v_cnt_5801_);
if (v___x_5802_ == 0)
{
lean_object* v___x_5803_; lean_object* v___x_5804_; 
v___x_5803_ = lean_unsigned_to_nat(1u);
v___x_5804_ = lean_nat_add(v_idx_5771_, v___x_5803_);
lean_dec(v_idx_5771_);
v_cnt_5770_ = v_cnt_5801_;
v_idx_5771_ = v___x_5804_;
goto _start;
}
else
{
lean_object* v_namePrefix_5806_; lean_object* v_idx_5807_; lean_object* v___x_5809_; uint8_t v_isShared_5810_; uint8_t v_isSharedCheck_5825_; 
lean_inc(v_toBind_5775_);
lean_dec(v_cnt_5801_);
v_namePrefix_5806_ = lean_ctor_get(v_ngen_5767_, 0);
v_idx_5807_ = lean_ctor_get(v_ngen_5767_, 1);
v_isSharedCheck_5825_ = !lean_is_exclusive(v_ngen_5767_);
if (v_isSharedCheck_5825_ == 0)
{
v___x_5809_ = v_ngen_5767_;
v_isShared_5810_ = v_isSharedCheck_5825_;
goto v_resetjp_5808_;
}
else
{
lean_inc(v_idx_5807_);
lean_inc(v_namePrefix_5806_);
lean_dec(v_ngen_5767_);
v___x_5809_ = lean_box(0);
v_isShared_5810_ = v_isSharedCheck_5825_;
goto v_resetjp_5808_;
}
v_resetjp_5808_:
{
lean_object* v___x_5811_; lean_object* v___x_5812_; lean_object* v___x_5814_; 
lean_inc(v_idx_5807_);
lean_inc(v_namePrefix_5806_);
v___x_5811_ = l_Lean_Name_num___override(v_namePrefix_5806_, v_idx_5807_);
v___x_5812_ = lean_unsigned_to_nat(1u);
if (v_isShared_5810_ == 0)
{
lean_ctor_set(v___x_5809_, 1, v___x_5812_);
lean_ctor_set(v___x_5809_, 0, v___x_5811_);
v___x_5814_ = v___x_5809_;
goto v_reusejp_5813_;
}
else
{
lean_object* v_reuseFailAlloc_5824_; 
v_reuseFailAlloc_5824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5824_, 0, v___x_5811_);
lean_ctor_set(v_reuseFailAlloc_5824_, 1, v___x_5812_);
v___x_5814_ = v_reuseFailAlloc_5824_;
goto v_reusejp_5813_;
}
v_reusejp_5813_:
{
lean_object* v___x_5815_; lean_object* v___x_5816_; lean_object* v___x_5817_; lean_object* v___f_5818_; lean_object* v___x_5819_; lean_object* v___x_5820_; lean_object* v___x_5821_; lean_object* v___x_5822_; lean_object* v___x_5823_; 
v___x_5815_ = lean_nat_add(v_idx_5807_, v___x_5812_);
lean_dec(v_idx_5807_);
v___x_5816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5816_, 0, v_namePrefix_5806_);
lean_ctor_set(v___x_5816_, 1, v___x_5815_);
v___x_5817_ = lean_nat_add(v_idx_5771_, v___x_5812_);
lean_dec(v_idx_5771_);
lean_inc(v___x_5817_);
lean_inc_ref(v_act_5764_);
lean_inc_ref(v_env_5763_);
lean_inc_ref(v_cctx_5762_);
lean_inc(v_inst_5761_);
v___f_5818_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__1), 11, 10);
lean_closure_set(v___f_5818_, 0, v_tasks_5768_);
lean_closure_set(v___f_5818_, 1, v_inst_5760_);
lean_closure_set(v___f_5818_, 2, v_inst_5761_);
lean_closure_set(v___f_5818_, 3, v_cctx_5762_);
lean_closure_set(v___f_5818_, 4, v_env_5763_);
lean_closure_set(v___f_5818_, 5, v_act_5764_);
lean_closure_set(v___f_5818_, 6, v_constantsPerTask_5765_);
lean_closure_set(v___f_5818_, 7, v_n_5766_);
lean_closure_set(v___f_5818_, 8, v___x_5816_);
lean_closure_set(v___f_5818_, 9, v___x_5817_);
v___x_5819_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_5819_, 0, lean_box(0));
lean_closure_set(v___x_5819_, 1, v_cctx_5762_);
lean_closure_set(v___x_5819_, 2, v___x_5814_);
lean_closure_set(v___x_5819_, 3, v_env_5763_);
lean_closure_set(v___x_5819_, 4, v_act_5764_);
lean_closure_set(v___x_5819_, 5, v_start_5769_);
lean_closure_set(v___x_5819_, 6, v___x_5817_);
v___x_5820_ = lean_unsigned_to_nat(0u);
v___x_5821_ = lean_alloc_closure((void*)(l_BaseIO_asTask___boxed), 4, 3);
lean_closure_set(v___x_5821_, 0, lean_box(0));
lean_closure_set(v___x_5821_, 1, v___x_5819_);
lean_closure_set(v___x_5821_, 2, v___x_5820_);
v___x_5822_ = lean_apply_2(v_inst_5761_, lean_box(0), v___x_5821_);
v___x_5823_ = lean_apply_4(v_toBind_5775_, lean_box(0), lean_box(0), v___x_5822_, v___f_5818_);
return v___x_5823_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__1(lean_object* v_tasks_5826_, lean_object* v_inst_5827_, lean_object* v_inst_5828_, lean_object* v_cctx_5829_, lean_object* v_env_5830_, lean_object* v_act_5831_, lean_object* v_constantsPerTask_5832_, lean_object* v_n_5833_, lean_object* v___x_5834_, lean_object* v___x_5835_, lean_object* v_t_5836_){
_start:
{
lean_object* v___x_5837_; lean_object* v___x_5838_; lean_object* v___x_5839_; 
v___x_5837_ = lean_array_push(v_tasks_5826_, v_t_5836_);
v___x_5838_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_5835_);
v___x_5839_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(v_inst_5827_, v_inst_5828_, v_cctx_5829_, v_env_5830_, v_act_5831_, v_constantsPerTask_5832_, v_n_5833_, v___x_5834_, v___x_5837_, v___x_5835_, v___x_5838_, v___x_5835_);
return v___x_5839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go(lean_object* v_m_5840_, lean_object* v_00_u03b1_5841_, lean_object* v_inst_5842_, lean_object* v_inst_5843_, lean_object* v_cctx_5844_, lean_object* v_env_5845_, lean_object* v_act_5846_, lean_object* v_constantsPerTask_5847_, lean_object* v_n_5848_, lean_object* v_ngen_5849_, lean_object* v_tasks_5850_, lean_object* v_start_5851_, lean_object* v_cnt_5852_, lean_object* v_idx_5853_){
_start:
{
lean_object* v___x_5854_; 
v___x_5854_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(v_inst_5842_, v_inst_5843_, v_cctx_5844_, v_env_5845_, v_act_5846_, v_constantsPerTask_5847_, v_n_5848_, v_ngen_5849_, v_tasks_5850_, v_start_5851_, v_cnt_5852_, v_idx_5853_);
return v___x_5854_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_getChildNgen_match__1_splitter___redArg(lean_object* v_x_5855_, lean_object* v_h__1_5856_){
_start:
{
lean_object* v_fst_5857_; lean_object* v_snd_5858_; lean_object* v___x_5859_; 
v_fst_5857_ = lean_ctor_get(v_x_5855_, 0);
lean_inc(v_fst_5857_);
v_snd_5858_ = lean_ctor_get(v_x_5855_, 1);
lean_inc(v_snd_5858_);
lean_dec_ref(v_x_5855_);
v___x_5859_ = lean_apply_2(v_h__1_5856_, v_fst_5857_, v_snd_5858_);
return v___x_5859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_getChildNgen_match__1_splitter(lean_object* v_motive_5860_, lean_object* v_x_5861_, lean_object* v_h__1_5862_){
_start:
{
lean_object* v_fst_5863_; lean_object* v_snd_5864_; lean_object* v___x_5865_; 
v_fst_5863_ = lean_ctor_get(v_x_5861_, 0);
lean_inc(v_fst_5863_);
v_snd_5864_ = lean_ctor_get(v_x_5861_, 1);
lean_inc(v_snd_5864_);
lean_dec_ref(v_x_5861_);
v___x_5865_ = lean_apply_2(v_h__1_5862_, v_fst_5863_, v_snd_5864_);
return v___x_5865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__0(lean_object* v_inst_5866_, lean_object* v_inst_5867_, lean_object* v_inst_5868_, lean_object* v_inst_5869_, lean_object* v_x_5870_, lean_object* v___y_5871_){
_start:
{
lean_object* v___x_5872_; 
v___x_5872_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg(v_inst_5866_, v_inst_5867_, v_inst_5868_, v_inst_5869_, v___y_5871_);
return v___x_5872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__1(lean_object* v_r_5873_, lean_object* v_toPure_5874_, lean_object* v_____r_5875_){
_start:
{
lean_object* v_tree_5876_; lean_object* v___x_5877_; lean_object* v___x_5878_; 
v_tree_5876_ = lean_ctor_get(v_r_5873_, 0);
lean_inc_ref(v_tree_5876_);
lean_dec(v_r_5873_);
v___x_5877_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_tree_5876_);
v___x_5878_ = lean_apply_2(v_toPure_5874_, lean_box(0), v___x_5877_);
return v___x_5878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__2(lean_object* v___x_5879_, lean_object* v___x_5880_, lean_object* v_toPure_5881_, lean_object* v_toBind_5882_, lean_object* v_inst_5883_, lean_object* v___f_5884_, lean_object* v_tasks_5885_){
_start:
{
lean_object* v___x_5886_; lean_object* v___x_5887_; lean_object* v___x_5888_; lean_object* v___x_5889_; lean_object* v___x_5890_; lean_object* v_r_5891_; lean_object* v_errors_5892_; lean_object* v___f_5893_; lean_object* v___x_5894_; lean_object* v___x_5895_; uint8_t v___x_5896_; 
v___x_5886_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__1);
lean_inc(v___x_5879_);
v___x_5887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5887_, 0, v___x_5879_);
lean_ctor_set(v___x_5887_, 1, v___x_5886_);
v___x_5888_ = lean_mk_empty_array_with_capacity(v___x_5879_);
lean_inc_ref(v___x_5888_);
v___x_5889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5889_, 0, v___x_5887_);
lean_ctor_set(v___x_5889_, 1, v___x_5888_);
v___x_5890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5890_, 0, v___x_5889_);
lean_ctor_set(v___x_5890_, 1, v___x_5888_);
v_r_5891_ = l_Lean_Meta_LazyDiscrTree_combineGet___redArg(v___x_5880_, v___x_5890_, v_tasks_5885_);
v_errors_5892_ = lean_ctor_get(v_r_5891_, 1);
lean_inc_ref(v_errors_5892_);
lean_inc(v_toPure_5881_);
v___f_5893_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__1), 3, 2);
lean_closure_set(v___f_5893_, 0, v_r_5891_);
lean_closure_set(v___f_5893_, 1, v_toPure_5881_);
v___x_5894_ = lean_array_get_size(v_errors_5892_);
v___x_5895_ = lean_box(0);
v___x_5896_ = lean_nat_dec_lt(v___x_5879_, v___x_5894_);
lean_dec(v___x_5879_);
if (v___x_5896_ == 0)
{
lean_object* v___x_5897_; lean_object* v___x_5898_; 
lean_dec_ref(v_errors_5892_);
lean_dec(v___f_5884_);
lean_dec_ref(v_inst_5883_);
v___x_5897_ = lean_apply_2(v_toPure_5881_, lean_box(0), v___x_5895_);
v___x_5898_ = lean_apply_4(v_toBind_5882_, lean_box(0), lean_box(0), v___x_5897_, v___f_5893_);
return v___x_5898_;
}
else
{
uint8_t v___x_5899_; 
v___x_5899_ = lean_nat_dec_le(v___x_5894_, v___x_5894_);
if (v___x_5899_ == 0)
{
if (v___x_5896_ == 0)
{
lean_object* v___x_5900_; lean_object* v___x_5901_; 
lean_dec_ref(v_errors_5892_);
lean_dec(v___f_5884_);
lean_dec_ref(v_inst_5883_);
v___x_5900_ = lean_apply_2(v_toPure_5881_, lean_box(0), v___x_5895_);
v___x_5901_ = lean_apply_4(v_toBind_5882_, lean_box(0), lean_box(0), v___x_5900_, v___f_5893_);
return v___x_5901_;
}
else
{
size_t v___x_5902_; size_t v___x_5903_; lean_object* v___x_5904_; lean_object* v___x_5905_; 
lean_dec(v_toPure_5881_);
v___x_5902_ = ((size_t)0ULL);
v___x_5903_ = lean_usize_of_nat(v___x_5894_);
v___x_5904_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_5883_, v___f_5884_, v_errors_5892_, v___x_5902_, v___x_5903_, v___x_5895_);
v___x_5905_ = lean_apply_4(v_toBind_5882_, lean_box(0), lean_box(0), v___x_5904_, v___f_5893_);
return v___x_5905_;
}
}
else
{
size_t v___x_5906_; size_t v___x_5907_; lean_object* v___x_5908_; lean_object* v___x_5909_; 
lean_dec(v_toPure_5881_);
v___x_5906_ = ((size_t)0ULL);
v___x_5907_ = lean_usize_of_nat(v___x_5894_);
v___x_5908_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_5883_, v___f_5884_, v_errors_5892_, v___x_5906_, v___x_5907_, v___x_5895_);
v___x_5909_ = lean_apply_4(v_toBind_5882_, lean_box(0), lean_box(0), v___x_5908_, v___f_5893_);
return v___x_5909_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg(lean_object* v_inst_5912_, lean_object* v_inst_5913_, lean_object* v_inst_5914_, lean_object* v_inst_5915_, lean_object* v_inst_5916_, lean_object* v_cctx_5917_, lean_object* v_ngen_5918_, lean_object* v_env_5919_, lean_object* v_act_5920_, lean_object* v_constantsPerTask_5921_){
_start:
{
lean_object* v___x_5922_; lean_object* v_moduleData_5923_; lean_object* v_toApplicative_5924_; lean_object* v_toBind_5925_; lean_object* v_n_5926_; lean_object* v___x_5927_; lean_object* v___x_5928_; lean_object* v___x_5929_; lean_object* v_toPure_5930_; lean_object* v___f_5931_; lean_object* v___x_5932_; lean_object* v___f_5933_; lean_object* v___x_5934_; 
v___x_5922_ = l_Lean_Environment_header(v_env_5919_);
v_moduleData_5923_ = lean_ctor_get(v___x_5922_, 6);
lean_inc_ref(v_moduleData_5923_);
lean_dec_ref(v___x_5922_);
v_toApplicative_5924_ = lean_ctor_get(v_inst_5912_, 0);
v_toBind_5925_ = lean_ctor_get(v_inst_5912_, 1);
lean_inc_n(v_toBind_5925_, 2);
v_n_5926_ = lean_array_get_size(v_moduleData_5923_);
lean_dec_ref(v_moduleData_5923_);
v___x_5927_ = lean_unsigned_to_nat(0u);
v___x_5928_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
lean_inc_ref_n(v_inst_5912_, 2);
v___x_5929_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(v_inst_5912_, v_inst_5916_, v_cctx_5917_, v_env_5919_, v_act_5920_, v_constantsPerTask_5921_, v_n_5926_, v_ngen_5918_, v___x_5928_, v___x_5927_, v___x_5927_, v___x_5927_);
v_toPure_5930_ = lean_ctor_get(v_toApplicative_5924_, 1);
lean_inc(v_toPure_5930_);
v___f_5931_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__0), 6, 4);
lean_closure_set(v___f_5931_, 0, v_inst_5912_);
lean_closure_set(v___f_5931_, 1, v_inst_5913_);
lean_closure_set(v___f_5931_, 2, v_inst_5914_);
lean_closure_set(v___f_5931_, 3, v_inst_5915_);
v___x_5932_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___redArg___closed__0));
v___f_5933_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__2), 7, 6);
lean_closure_set(v___f_5933_, 0, v___x_5927_);
lean_closure_set(v___f_5933_, 1, v___x_5932_);
lean_closure_set(v___f_5933_, 2, v_toPure_5930_);
lean_closure_set(v___f_5933_, 3, v_toBind_5925_);
lean_closure_set(v___f_5933_, 4, v_inst_5912_);
lean_closure_set(v___f_5933_, 5, v___f_5931_);
v___x_5934_ = lean_apply_4(v_toBind_5925_, lean_box(0), lean_box(0), v___x_5929_, v___f_5933_);
return v___x_5934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree(lean_object* v_m_5935_, lean_object* v_00_u03b1_5936_, lean_object* v_inst_5937_, lean_object* v_inst_5938_, lean_object* v_inst_5939_, lean_object* v_inst_5940_, lean_object* v_inst_5941_, lean_object* v_cctx_5942_, lean_object* v_ngen_5943_, lean_object* v_env_5944_, lean_object* v_act_5945_, lean_object* v_constantsPerTask_5946_){
_start:
{
lean_object* v___x_5947_; 
v___x_5947_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg(v_inst_5937_, v_inst_5938_, v_inst_5939_, v_inst_5940_, v_inst_5941_, v_cctx_5942_, v_ngen_5943_, v_env_5944_, v_act_5945_, v_constantsPerTask_5946_);
return v___x_5947_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0(void){
_start:
{
lean_object* v___x_5948_; lean_object* v___x_5949_; lean_object* v___x_5950_; 
v___x_5948_ = lean_box(0);
v___x_5949_ = lean_unsigned_to_nat(16u);
v___x_5950_ = lean_mk_array(v___x_5949_, v___x_5948_);
return v___x_5950_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1(void){
_start:
{
lean_object* v___x_5951_; lean_object* v___x_5952_; lean_object* v___x_5953_; 
v___x_5951_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0, &l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0);
v___x_5952_ = lean_unsigned_to_nat(0u);
v___x_5953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5953_, 0, v___x_5952_);
lean_ctor_set(v___x_5953_, 1, v___x_5951_);
return v___x_5953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createTreeCtx(lean_object* v_ctx_5954_){
_start:
{
lean_object* v_toCold_5955_; lean_object* v_ref_5956_; lean_object* v___x_5958_; uint8_t v_isShared_5959_; uint8_t v_isSharedCheck_5990_; 
v_toCold_5955_ = lean_ctor_get(v_ctx_5954_, 0);
v_ref_5956_ = lean_ctor_get(v_ctx_5954_, 2);
v_isSharedCheck_5990_ = !lean_is_exclusive(v_ctx_5954_);
if (v_isSharedCheck_5990_ == 0)
{
lean_object* v_unused_5991_; 
v_unused_5991_ = lean_ctor_get(v_ctx_5954_, 1);
lean_dec(v_unused_5991_);
v___x_5958_ = v_ctx_5954_;
v_isShared_5959_ = v_isSharedCheck_5990_;
goto v_resetjp_5957_;
}
else
{
lean_inc(v_ref_5956_);
lean_inc(v_toCold_5955_);
lean_dec(v_ctx_5954_);
v___x_5958_ = lean_box(0);
v_isShared_5959_ = v_isSharedCheck_5990_;
goto v_resetjp_5957_;
}
v_resetjp_5957_:
{
lean_object* v_fileName_5960_; lean_object* v_fileMap_5961_; lean_object* v_options_5962_; lean_object* v_maxRecDepth_5963_; lean_object* v___x_5965_; uint8_t v_isShared_5966_; uint8_t v_isSharedCheck_5981_; 
v_fileName_5960_ = lean_ctor_get(v_toCold_5955_, 0);
v_fileMap_5961_ = lean_ctor_get(v_toCold_5955_, 1);
v_options_5962_ = lean_ctor_get(v_toCold_5955_, 2);
v_maxRecDepth_5963_ = lean_ctor_get(v_toCold_5955_, 3);
v_isSharedCheck_5981_ = !lean_is_exclusive(v_toCold_5955_);
if (v_isSharedCheck_5981_ == 0)
{
lean_object* v_unused_5982_; lean_object* v_unused_5983_; lean_object* v_unused_5984_; lean_object* v_unused_5985_; lean_object* v_unused_5986_; lean_object* v_unused_5987_; lean_object* v_unused_5988_; lean_object* v_unused_5989_; 
v_unused_5982_ = lean_ctor_get(v_toCold_5955_, 11);
lean_dec(v_unused_5982_);
v_unused_5983_ = lean_ctor_get(v_toCold_5955_, 10);
lean_dec(v_unused_5983_);
v_unused_5984_ = lean_ctor_get(v_toCold_5955_, 9);
lean_dec(v_unused_5984_);
v_unused_5985_ = lean_ctor_get(v_toCold_5955_, 8);
lean_dec(v_unused_5985_);
v_unused_5986_ = lean_ctor_get(v_toCold_5955_, 7);
lean_dec(v_unused_5986_);
v_unused_5987_ = lean_ctor_get(v_toCold_5955_, 6);
lean_dec(v_unused_5987_);
v_unused_5988_ = lean_ctor_get(v_toCold_5955_, 5);
lean_dec(v_unused_5988_);
v_unused_5989_ = lean_ctor_get(v_toCold_5955_, 4);
lean_dec(v_unused_5989_);
v___x_5965_ = v_toCold_5955_;
v_isShared_5966_ = v_isSharedCheck_5981_;
goto v_resetjp_5964_;
}
else
{
lean_inc(v_maxRecDepth_5963_);
lean_inc(v_options_5962_);
lean_inc(v_fileMap_5961_);
lean_inc(v_fileName_5960_);
lean_dec(v_toCold_5955_);
v___x_5965_ = lean_box(0);
v_isShared_5966_ = v_isSharedCheck_5981_;
goto v_resetjp_5964_;
}
v_resetjp_5964_:
{
lean_object* v___x_5967_; lean_object* v___x_5968_; lean_object* v___x_5969_; lean_object* v___x_5970_; lean_object* v___x_5971_; lean_object* v___x_5972_; lean_object* v___x_5974_; 
v___x_5967_ = lean_box(0);
v___x_5968_ = lean_box(0);
v___x_5969_ = lean_unsigned_to_nat(0u);
v___x_5970_ = l_Lean_firstFrontendMacroScope;
v___x_5971_ = lean_box(0);
v___x_5972_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1, &l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1);
lean_inc_ref(v_options_5962_);
if (v_isShared_5966_ == 0)
{
lean_ctor_set(v___x_5965_, 11, v___x_5972_);
lean_ctor_set(v___x_5965_, 10, v___x_5971_);
lean_ctor_set(v___x_5965_, 9, v___x_5970_);
lean_ctor_set(v___x_5965_, 8, v___x_5967_);
lean_ctor_set(v___x_5965_, 7, v___x_5969_);
lean_ctor_set(v___x_5965_, 6, v___x_5969_);
lean_ctor_set(v___x_5965_, 5, v___x_5968_);
lean_ctor_set(v___x_5965_, 4, v___x_5967_);
v___x_5974_ = v___x_5965_;
goto v_reusejp_5973_;
}
else
{
lean_object* v_reuseFailAlloc_5980_; 
v_reuseFailAlloc_5980_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_5980_, 0, v_fileName_5960_);
lean_ctor_set(v_reuseFailAlloc_5980_, 1, v_fileMap_5961_);
lean_ctor_set(v_reuseFailAlloc_5980_, 2, v_options_5962_);
lean_ctor_set(v_reuseFailAlloc_5980_, 3, v_maxRecDepth_5963_);
lean_ctor_set(v_reuseFailAlloc_5980_, 4, v___x_5967_);
lean_ctor_set(v_reuseFailAlloc_5980_, 5, v___x_5968_);
lean_ctor_set(v_reuseFailAlloc_5980_, 6, v___x_5969_);
lean_ctor_set(v_reuseFailAlloc_5980_, 7, v___x_5969_);
lean_ctor_set(v_reuseFailAlloc_5980_, 8, v___x_5967_);
lean_ctor_set(v_reuseFailAlloc_5980_, 9, v___x_5970_);
lean_ctor_set(v_reuseFailAlloc_5980_, 10, v___x_5971_);
lean_ctor_set(v_reuseFailAlloc_5980_, 11, v___x_5972_);
v___x_5974_ = v_reuseFailAlloc_5980_;
goto v_reusejp_5973_;
}
v_reusejp_5973_:
{
uint16_t v___x_5975_; uint8_t v___x_5976_; lean_object* v___x_5978_; 
v___x_5975_ = l_Lean_OptionFlags_ofOptions(v_options_5962_);
lean_dec_ref(v_options_5962_);
v___x_5976_ = 0;
if (v_isShared_5959_ == 0)
{
lean_ctor_set(v___x_5958_, 1, v___x_5969_);
lean_ctor_set(v___x_5958_, 0, v___x_5974_);
v___x_5978_ = v___x_5958_;
goto v_reusejp_5977_;
}
else
{
lean_object* v_reuseFailAlloc_5979_; 
v_reuseFailAlloc_5979_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v_reuseFailAlloc_5979_, 0, v___x_5974_);
lean_ctor_set(v_reuseFailAlloc_5979_, 1, v___x_5969_);
lean_ctor_set(v_reuseFailAlloc_5979_, 2, v_ref_5956_);
v___x_5978_ = v_reuseFailAlloc_5979_;
goto v_reusejp_5977_;
}
v_reusejp_5977_:
{
lean_ctor_set_uint16(v___x_5978_, sizeof(void*)*3, v___x_5975_);
lean_ctor_set_uint8(v___x_5978_, sizeof(void*)*3 + 2, v___x_5976_);
lean_ctor_set_uint8(v___x_5978_, sizeof(void*)*3 + 3, v___x_5976_);
return v___x_5978_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(lean_object* v_category_5992_, lean_object* v_opts_5993_, lean_object* v_act_5994_, lean_object* v_decl_5995_, lean_object* v___y_5996_, lean_object* v___y_5997_, lean_object* v___y_5998_, lean_object* v___y_5999_){
_start:
{
lean_object* v___x_6001_; lean_object* v___x_6002_; 
lean_inc(v___y_5999_);
lean_inc_ref(v___y_5998_);
lean_inc(v___y_5997_);
lean_inc_ref(v___y_5996_);
v___x_6001_ = lean_apply_4(v_act_5994_, v___y_5996_, v___y_5997_, v___y_5998_, v___y_5999_);
v___x_6002_ = l_Lean_profileitIOUnsafe___redArg(v_category_5992_, v_opts_5993_, v___x_6001_, v_decl_5995_);
return v___x_6002_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg___boxed(lean_object* v_category_6003_, lean_object* v_opts_6004_, lean_object* v_act_6005_, lean_object* v_decl_6006_, lean_object* v___y_6007_, lean_object* v___y_6008_, lean_object* v___y_6009_, lean_object* v___y_6010_, lean_object* v___y_6011_){
_start:
{
lean_object* v_res_6012_; 
v_res_6012_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v_category_6003_, v_opts_6004_, v_act_6005_, v_decl_6006_, v___y_6007_, v___y_6008_, v___y_6009_, v___y_6010_);
lean_dec(v___y_6010_);
lean_dec_ref(v___y_6009_);
lean_dec(v___y_6008_);
lean_dec_ref(v___y_6007_);
lean_dec_ref(v_opts_6004_);
lean_dec_ref(v_category_6003_);
return v_res_6012_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1(lean_object* v_00_u03b1_6013_, lean_object* v_category_6014_, lean_object* v_opts_6015_, lean_object* v_act_6016_, lean_object* v_decl_6017_, lean_object* v___y_6018_, lean_object* v___y_6019_, lean_object* v___y_6020_, lean_object* v___y_6021_){
_start:
{
lean_object* v___x_6023_; 
v___x_6023_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v_category_6014_, v_opts_6015_, v_act_6016_, v_decl_6017_, v___y_6018_, v___y_6019_, v___y_6020_, v___y_6021_);
return v___x_6023_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___boxed(lean_object* v_00_u03b1_6024_, lean_object* v_category_6025_, lean_object* v_opts_6026_, lean_object* v_act_6027_, lean_object* v_decl_6028_, lean_object* v___y_6029_, lean_object* v___y_6030_, lean_object* v___y_6031_, lean_object* v___y_6032_, lean_object* v___y_6033_){
_start:
{
lean_object* v_res_6034_; 
v_res_6034_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1(v_00_u03b1_6024_, v_category_6025_, v_opts_6026_, v_act_6027_, v_decl_6028_, v___y_6029_, v___y_6030_, v___y_6031_, v___y_6032_);
lean_dec(v___y_6032_);
lean_dec_ref(v___y_6031_);
lean_dec(v___y_6030_);
lean_dec_ref(v___y_6029_);
lean_dec_ref(v_opts_6026_);
lean_dec_ref(v_category_6025_);
return v_res_6034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(lean_object* v_cctx_6035_, lean_object* v_env_6036_, lean_object* v_act_6037_, lean_object* v_constantsPerTask_6038_, lean_object* v_n_6039_, lean_object* v_ngen_6040_, lean_object* v_tasks_6041_, lean_object* v_start_6042_, lean_object* v_cnt_6043_, lean_object* v_idx_6044_){
_start:
{
lean_object* v___x_6046_; lean_object* v_moduleData_6047_; lean_object* v___x_6048_; uint8_t v___x_6049_; 
v___x_6046_ = l_Lean_Environment_header(v_env_6036_);
v_moduleData_6047_ = lean_ctor_get(v___x_6046_, 6);
lean_inc_ref(v_moduleData_6047_);
lean_dec_ref(v___x_6046_);
v___x_6048_ = lean_array_get_size(v_moduleData_6047_);
v___x_6049_ = lean_nat_dec_lt(v_idx_6044_, v___x_6048_);
if (v___x_6049_ == 0)
{
uint8_t v___x_6050_; 
lean_dec_ref(v_moduleData_6047_);
lean_dec(v_idx_6044_);
lean_dec(v_cnt_6043_);
v___x_6050_ = lean_nat_dec_lt(v_start_6042_, v_n_6039_);
if (v___x_6050_ == 0)
{
lean_object* v___x_6051_; 
lean_dec(v_start_6042_);
lean_dec_ref(v_ngen_6040_);
lean_dec(v_n_6039_);
lean_dec_ref(v_act_6037_);
lean_dec_ref(v_env_6036_);
lean_dec_ref(v_cctx_6035_);
v___x_6051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6051_, 0, v_tasks_6041_);
return v___x_6051_;
}
else
{
lean_object* v_namePrefix_6052_; lean_object* v_idx_6053_; lean_object* v___x_6055_; uint8_t v_isShared_6056_; uint8_t v_isSharedCheck_6067_; 
v_namePrefix_6052_ = lean_ctor_get(v_ngen_6040_, 0);
v_idx_6053_ = lean_ctor_get(v_ngen_6040_, 1);
v_isSharedCheck_6067_ = !lean_is_exclusive(v_ngen_6040_);
if (v_isSharedCheck_6067_ == 0)
{
v___x_6055_ = v_ngen_6040_;
v_isShared_6056_ = v_isSharedCheck_6067_;
goto v_resetjp_6054_;
}
else
{
lean_inc(v_idx_6053_);
lean_inc(v_namePrefix_6052_);
lean_dec(v_ngen_6040_);
v___x_6055_ = lean_box(0);
v_isShared_6056_ = v_isSharedCheck_6067_;
goto v_resetjp_6054_;
}
v_resetjp_6054_:
{
lean_object* v___x_6057_; lean_object* v___x_6058_; lean_object* v___x_6060_; 
v___x_6057_ = l_Lean_Name_num___override(v_namePrefix_6052_, v_idx_6053_);
v___x_6058_ = lean_unsigned_to_nat(1u);
if (v_isShared_6056_ == 0)
{
lean_ctor_set(v___x_6055_, 1, v___x_6058_);
lean_ctor_set(v___x_6055_, 0, v___x_6057_);
v___x_6060_ = v___x_6055_;
goto v_reusejp_6059_;
}
else
{
lean_object* v_reuseFailAlloc_6066_; 
v_reuseFailAlloc_6066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6066_, 0, v___x_6057_);
lean_ctor_set(v_reuseFailAlloc_6066_, 1, v___x_6058_);
v___x_6060_ = v_reuseFailAlloc_6066_;
goto v_reusejp_6059_;
}
v_reusejp_6059_:
{
lean_object* v___x_6061_; lean_object* v___x_6062_; lean_object* v___x_6063_; lean_object* v___x_6064_; lean_object* v___x_6065_; 
v___x_6061_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_6061_, 0, lean_box(0));
lean_closure_set(v___x_6061_, 1, v_cctx_6035_);
lean_closure_set(v___x_6061_, 2, v___x_6060_);
lean_closure_set(v___x_6061_, 3, v_env_6036_);
lean_closure_set(v___x_6061_, 4, v_act_6037_);
lean_closure_set(v___x_6061_, 5, v_start_6042_);
lean_closure_set(v___x_6061_, 6, v_n_6039_);
v___x_6062_ = lean_unsigned_to_nat(0u);
v___x_6063_ = lean_io_as_task(v___x_6061_, v___x_6062_);
v___x_6064_ = lean_array_push(v_tasks_6041_, v___x_6063_);
v___x_6065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6065_, 0, v___x_6064_);
return v___x_6065_;
}
}
}
}
else
{
lean_object* v_mdata_6068_; lean_object* v_constants_6069_; lean_object* v___x_6070_; lean_object* v_cnt_6071_; uint8_t v___x_6072_; 
v_mdata_6068_ = lean_array_fget(v_moduleData_6047_, v_idx_6044_);
lean_dec_ref(v_moduleData_6047_);
v_constants_6069_ = lean_ctor_get(v_mdata_6068_, 2);
lean_inc_ref(v_constants_6069_);
lean_dec(v_mdata_6068_);
v___x_6070_ = lean_array_get_size(v_constants_6069_);
lean_dec_ref(v_constants_6069_);
v_cnt_6071_ = lean_nat_add(v_cnt_6043_, v___x_6070_);
lean_dec(v_cnt_6043_);
v___x_6072_ = lean_nat_dec_lt(v_constantsPerTask_6038_, v_cnt_6071_);
if (v___x_6072_ == 0)
{
lean_object* v___x_6073_; lean_object* v___x_6074_; 
v___x_6073_ = lean_unsigned_to_nat(1u);
v___x_6074_ = lean_nat_add(v_idx_6044_, v___x_6073_);
lean_dec(v_idx_6044_);
v_cnt_6043_ = v_cnt_6071_;
v_idx_6044_ = v___x_6074_;
goto _start;
}
else
{
lean_object* v_namePrefix_6076_; lean_object* v_idx_6077_; lean_object* v___x_6079_; uint8_t v_isShared_6080_; uint8_t v_isSharedCheck_6094_; 
lean_dec(v_cnt_6071_);
v_namePrefix_6076_ = lean_ctor_get(v_ngen_6040_, 0);
v_idx_6077_ = lean_ctor_get(v_ngen_6040_, 1);
v_isSharedCheck_6094_ = !lean_is_exclusive(v_ngen_6040_);
if (v_isSharedCheck_6094_ == 0)
{
v___x_6079_ = v_ngen_6040_;
v_isShared_6080_ = v_isSharedCheck_6094_;
goto v_resetjp_6078_;
}
else
{
lean_inc(v_idx_6077_);
lean_inc(v_namePrefix_6076_);
lean_dec(v_ngen_6040_);
v___x_6079_ = lean_box(0);
v_isShared_6080_ = v_isSharedCheck_6094_;
goto v_resetjp_6078_;
}
v_resetjp_6078_:
{
lean_object* v___x_6081_; lean_object* v___x_6082_; lean_object* v___x_6084_; 
lean_inc(v_idx_6077_);
lean_inc(v_namePrefix_6076_);
v___x_6081_ = l_Lean_Name_num___override(v_namePrefix_6076_, v_idx_6077_);
v___x_6082_ = lean_unsigned_to_nat(1u);
if (v_isShared_6080_ == 0)
{
lean_ctor_set(v___x_6079_, 1, v___x_6082_);
lean_ctor_set(v___x_6079_, 0, v___x_6081_);
v___x_6084_ = v___x_6079_;
goto v_reusejp_6083_;
}
else
{
lean_object* v_reuseFailAlloc_6093_; 
v_reuseFailAlloc_6093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6093_, 0, v___x_6081_);
lean_ctor_set(v_reuseFailAlloc_6093_, 1, v___x_6082_);
v___x_6084_ = v_reuseFailAlloc_6093_;
goto v_reusejp_6083_;
}
v_reusejp_6083_:
{
lean_object* v___x_6085_; lean_object* v___x_6086_; lean_object* v___x_6087_; lean_object* v___x_6088_; lean_object* v___x_6089_; lean_object* v___x_6090_; lean_object* v___x_6091_; 
v___x_6085_ = lean_nat_add(v_idx_6077_, v___x_6082_);
lean_dec(v_idx_6077_);
v___x_6086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6086_, 0, v_namePrefix_6076_);
lean_ctor_set(v___x_6086_, 1, v___x_6085_);
v___x_6087_ = lean_nat_add(v_idx_6044_, v___x_6082_);
lean_dec(v_idx_6044_);
lean_inc_n(v___x_6087_, 2);
lean_inc_ref(v_act_6037_);
lean_inc_ref(v_env_6036_);
lean_inc_ref(v_cctx_6035_);
v___x_6088_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_6088_, 0, lean_box(0));
lean_closure_set(v___x_6088_, 1, v_cctx_6035_);
lean_closure_set(v___x_6088_, 2, v___x_6084_);
lean_closure_set(v___x_6088_, 3, v_env_6036_);
lean_closure_set(v___x_6088_, 4, v_act_6037_);
lean_closure_set(v___x_6088_, 5, v_start_6042_);
lean_closure_set(v___x_6088_, 6, v___x_6087_);
v___x_6089_ = lean_unsigned_to_nat(0u);
v___x_6090_ = lean_io_as_task(v___x_6088_, v___x_6089_);
v___x_6091_ = lean_array_push(v_tasks_6041_, v___x_6090_);
v_ngen_6040_ = v___x_6086_;
v_tasks_6041_ = v___x_6091_;
v_start_6042_ = v___x_6087_;
v_cnt_6043_ = v___x_6089_;
v_idx_6044_ = v___x_6087_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg___boxed(lean_object* v_cctx_6095_, lean_object* v_env_6096_, lean_object* v_act_6097_, lean_object* v_constantsPerTask_6098_, lean_object* v_n_6099_, lean_object* v_ngen_6100_, lean_object* v_tasks_6101_, lean_object* v_start_6102_, lean_object* v_cnt_6103_, lean_object* v_idx_6104_, lean_object* v___y_6105_){
_start:
{
lean_object* v_res_6106_; 
v_res_6106_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(v_cctx_6095_, v_env_6096_, v_act_6097_, v_constantsPerTask_6098_, v_n_6099_, v_ngen_6100_, v_tasks_6101_, v_start_6102_, v_cnt_6103_, v_idx_6104_);
lean_dec(v_constantsPerTask_6098_);
return v_res_6106_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0(uint8_t v_suppressElabErrors_6115_, uint8_t v___y_6116_, lean_object* v_x_6117_){
_start:
{
if (lean_obj_tag(v_x_6117_) == 1)
{
lean_object* v_pre_6118_; 
v_pre_6118_ = lean_ctor_get(v_x_6117_, 0);
switch(lean_obj_tag(v_pre_6118_))
{
case 1:
{
lean_object* v_pre_6119_; 
v_pre_6119_ = lean_ctor_get(v_pre_6118_, 0);
switch(lean_obj_tag(v_pre_6119_))
{
case 0:
{
lean_object* v_str_6120_; lean_object* v_str_6121_; lean_object* v___x_6122_; uint8_t v___x_6123_; 
v_str_6120_ = lean_ctor_get(v_x_6117_, 1);
v_str_6121_ = lean_ctor_get(v_pre_6118_, 1);
v___x_6122_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__0));
v___x_6123_ = lean_string_dec_eq(v_str_6121_, v___x_6122_);
if (v___x_6123_ == 0)
{
lean_object* v___x_6124_; uint8_t v___x_6125_; 
v___x_6124_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__1));
v___x_6125_ = lean_string_dec_eq(v_str_6121_, v___x_6124_);
if (v___x_6125_ == 0)
{
return v___x_6125_;
}
else
{
lean_object* v___x_6126_; uint8_t v___x_6127_; 
v___x_6126_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__2));
v___x_6127_ = lean_string_dec_eq(v_str_6120_, v___x_6126_);
if (v___x_6127_ == 0)
{
return v___x_6127_;
}
else
{
return v_suppressElabErrors_6115_;
}
}
}
else
{
lean_object* v___x_6128_; uint8_t v___x_6129_; 
v___x_6128_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__3));
v___x_6129_ = lean_string_dec_eq(v_str_6120_, v___x_6128_);
if (v___x_6129_ == 0)
{
return v___x_6129_;
}
else
{
return v_suppressElabErrors_6115_;
}
}
}
case 1:
{
lean_object* v_pre_6130_; 
v_pre_6130_ = lean_ctor_get(v_pre_6119_, 0);
if (lean_obj_tag(v_pre_6130_) == 0)
{
lean_object* v_str_6131_; lean_object* v_str_6132_; lean_object* v_str_6133_; lean_object* v___x_6134_; uint8_t v___x_6135_; 
v_str_6131_ = lean_ctor_get(v_x_6117_, 1);
v_str_6132_ = lean_ctor_get(v_pre_6118_, 1);
v_str_6133_ = lean_ctor_get(v_pre_6119_, 1);
v___x_6134_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__4));
v___x_6135_ = lean_string_dec_eq(v_str_6133_, v___x_6134_);
if (v___x_6135_ == 0)
{
return v___x_6135_;
}
else
{
lean_object* v___x_6136_; uint8_t v___x_6137_; 
v___x_6136_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__5));
v___x_6137_ = lean_string_dec_eq(v_str_6132_, v___x_6136_);
if (v___x_6137_ == 0)
{
return v___x_6137_;
}
else
{
lean_object* v___x_6138_; uint8_t v___x_6139_; 
v___x_6138_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__6));
v___x_6139_ = lean_string_dec_eq(v_str_6131_, v___x_6138_);
if (v___x_6139_ == 0)
{
return v___x_6139_;
}
else
{
return v_suppressElabErrors_6115_;
}
}
}
}
else
{
return v___y_6116_;
}
}
default: 
{
return v___y_6116_;
}
}
}
case 0:
{
lean_object* v_str_6140_; lean_object* v___x_6141_; uint8_t v___x_6142_; 
v_str_6140_ = lean_ctor_get(v_x_6117_, 1);
v___x_6141_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__7));
v___x_6142_ = lean_string_dec_eq(v_str_6140_, v___x_6141_);
if (v___x_6142_ == 0)
{
return v___x_6142_;
}
else
{
return v_suppressElabErrors_6115_;
}
}
default: 
{
return v___y_6116_;
}
}
}
else
{
return v___y_6116_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___boxed(lean_object* v_suppressElabErrors_6143_, lean_object* v___y_6144_, lean_object* v_x_6145_){
_start:
{
uint8_t v_suppressElabErrors_boxed_6146_; uint8_t v___y_8181__boxed_6147_; uint8_t v_res_6148_; lean_object* v_r_6149_; 
v_suppressElabErrors_boxed_6146_ = lean_unbox(v_suppressElabErrors_6143_);
v___y_8181__boxed_6147_ = lean_unbox(v___y_6144_);
v_res_6148_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0(v_suppressElabErrors_boxed_6146_, v___y_8181__boxed_6147_, v_x_6145_);
lean_dec(v_x_6145_);
v_r_6149_ = lean_box(v_res_6148_);
return v_r_6149_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7_spec__9(lean_object* v_opts_6150_, lean_object* v_opt_6151_){
_start:
{
lean_object* v_name_6152_; lean_object* v_defValue_6153_; lean_object* v_map_6154_; lean_object* v___x_6155_; 
v_name_6152_ = lean_ctor_get(v_opt_6151_, 0);
v_defValue_6153_ = lean_ctor_get(v_opt_6151_, 1);
v_map_6154_ = lean_ctor_get(v_opts_6150_, 0);
v___x_6155_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_6154_, v_name_6152_);
if (lean_obj_tag(v___x_6155_) == 0)
{
uint8_t v___x_6156_; 
v___x_6156_ = lean_unbox(v_defValue_6153_);
return v___x_6156_;
}
else
{
lean_object* v_val_6157_; 
v_val_6157_ = lean_ctor_get(v___x_6155_, 0);
lean_inc(v_val_6157_);
lean_dec_ref_known(v___x_6155_, 1);
if (lean_obj_tag(v_val_6157_) == 1)
{
uint8_t v_v_6158_; 
v_v_6158_ = lean_ctor_get_uint8(v_val_6157_, 0);
lean_dec_ref_known(v_val_6157_, 0);
return v_v_6158_;
}
else
{
uint8_t v___x_6159_; 
lean_dec(v_val_6157_);
v___x_6159_ = lean_unbox(v_defValue_6153_);
return v___x_6159_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7_spec__9___boxed(lean_object* v_opts_6160_, lean_object* v_opt_6161_){
_start:
{
uint8_t v_res_6162_; lean_object* v_r_6163_; 
v_res_6162_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7_spec__9(v_opts_6160_, v_opt_6161_);
lean_dec_ref(v_opt_6161_);
lean_dec_ref(v_opts_6160_);
v_r_6163_ = lean_box(v_res_6162_);
return v_r_6163_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7(lean_object* v_ref_6165_, lean_object* v_msgData_6166_, uint8_t v_severity_6167_, uint8_t v_isSilent_6168_, lean_object* v___y_6169_, lean_object* v___y_6170_, lean_object* v___y_6171_, lean_object* v___y_6172_){
_start:
{
lean_object* v___y_6175_; lean_object* v___y_6176_; lean_object* v___y_6177_; lean_object* v___y_6178_; lean_object* v___y_6179_; uint8_t v___y_6180_; uint8_t v___y_6181_; lean_object* v_toCold_6182_; lean_object* v___y_6183_; lean_object* v___y_6212_; lean_object* v___y_6213_; lean_object* v___y_6214_; uint8_t v___y_6215_; lean_object* v___y_6216_; uint8_t v___y_6217_; uint8_t v___y_6218_; lean_object* v___y_6219_; lean_object* v___y_6239_; lean_object* v___y_6240_; uint8_t v___y_6241_; lean_object* v___y_6242_; uint8_t v___y_6243_; uint8_t v___y_6244_; lean_object* v___y_6245_; uint8_t v___y_6249_; uint8_t v___y_6250_; uint8_t v___y_6251_; uint8_t v___x_6262_; uint8_t v___y_6264_; uint8_t v___y_6265_; uint8_t v___y_6266_; uint8_t v___y_6268_; uint8_t v___x_6276_; 
v___x_6262_ = 2;
v___x_6276_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6167_, v___x_6262_);
if (v___x_6276_ == 0)
{
v___y_6268_ = v___x_6276_;
goto v___jp_6267_;
}
else
{
uint8_t v___x_6277_; 
lean_inc_ref(v_msgData_6166_);
v___x_6277_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_6166_);
v___y_6268_ = v___x_6277_;
goto v___jp_6267_;
}
v___jp_6174_:
{
lean_object* v_currNamespace_6184_; lean_object* v_openDecls_6185_; lean_object* v___x_6186_; lean_object* v___x_6187_; lean_object* v___x_6188_; lean_object* v___x_6189_; lean_object* v_env_6190_; lean_object* v_nextMacroScope_6191_; lean_object* v_ngen_6192_; lean_object* v_auxDeclNGen_6193_; lean_object* v_traceState_6194_; lean_object* v_cache_6195_; lean_object* v_recordedDeps_6196_; lean_object* v_messages_6197_; lean_object* v_infoState_6198_; lean_object* v_snapshotTasks_6199_; lean_object* v___x_6201_; uint8_t v_isShared_6202_; uint8_t v_isSharedCheck_6210_; 
v_currNamespace_6184_ = lean_ctor_get(v_toCold_6182_, 4);
v_openDecls_6185_ = lean_ctor_get(v_toCold_6182_, 5);
lean_inc(v_openDecls_6185_);
lean_inc(v_currNamespace_6184_);
v___x_6186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6186_, 0, v_currNamespace_6184_);
lean_ctor_set(v___x_6186_, 1, v_openDecls_6185_);
v___x_6187_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6187_, 0, v___x_6186_);
lean_ctor_set(v___x_6187_, 1, v___y_6175_);
lean_inc_ref(v___y_6176_);
lean_inc_ref(v___y_6178_);
v___x_6188_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_6188_, 0, v___y_6178_);
lean_ctor_set(v___x_6188_, 1, v___y_6179_);
lean_ctor_set(v___x_6188_, 2, v___y_6177_);
lean_ctor_set(v___x_6188_, 3, v___y_6176_);
lean_ctor_set(v___x_6188_, 4, v___x_6187_);
lean_ctor_set_uint8(v___x_6188_, sizeof(void*)*5, v___y_6181_);
lean_ctor_set_uint8(v___x_6188_, sizeof(void*)*5 + 1, v___y_6180_);
lean_ctor_set_uint8(v___x_6188_, sizeof(void*)*5 + 2, v_isSilent_6168_);
v___x_6189_ = lean_st_ref_take(v___y_6183_);
v_env_6190_ = lean_ctor_get(v___x_6189_, 0);
v_nextMacroScope_6191_ = lean_ctor_get(v___x_6189_, 1);
v_ngen_6192_ = lean_ctor_get(v___x_6189_, 2);
v_auxDeclNGen_6193_ = lean_ctor_get(v___x_6189_, 3);
v_traceState_6194_ = lean_ctor_get(v___x_6189_, 4);
v_cache_6195_ = lean_ctor_get(v___x_6189_, 5);
v_recordedDeps_6196_ = lean_ctor_get(v___x_6189_, 6);
v_messages_6197_ = lean_ctor_get(v___x_6189_, 7);
v_infoState_6198_ = lean_ctor_get(v___x_6189_, 8);
v_snapshotTasks_6199_ = lean_ctor_get(v___x_6189_, 9);
v_isSharedCheck_6210_ = !lean_is_exclusive(v___x_6189_);
if (v_isSharedCheck_6210_ == 0)
{
v___x_6201_ = v___x_6189_;
v_isShared_6202_ = v_isSharedCheck_6210_;
goto v_resetjp_6200_;
}
else
{
lean_inc(v_snapshotTasks_6199_);
lean_inc(v_infoState_6198_);
lean_inc(v_messages_6197_);
lean_inc(v_recordedDeps_6196_);
lean_inc(v_cache_6195_);
lean_inc(v_traceState_6194_);
lean_inc(v_auxDeclNGen_6193_);
lean_inc(v_ngen_6192_);
lean_inc(v_nextMacroScope_6191_);
lean_inc(v_env_6190_);
lean_dec(v___x_6189_);
v___x_6201_ = lean_box(0);
v_isShared_6202_ = v_isSharedCheck_6210_;
goto v_resetjp_6200_;
}
v_resetjp_6200_:
{
lean_object* v___x_6203_; lean_object* v___x_6204_; lean_object* v___x_6206_; 
v___x_6203_ = lean_box(0);
v___x_6204_ = l_Lean_MessageLog_add(v___x_6188_, v_messages_6197_);
if (v_isShared_6202_ == 0)
{
lean_ctor_set(v___x_6201_, 7, v___x_6204_);
v___x_6206_ = v___x_6201_;
goto v_reusejp_6205_;
}
else
{
lean_object* v_reuseFailAlloc_6209_; 
v_reuseFailAlloc_6209_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6209_, 0, v_env_6190_);
lean_ctor_set(v_reuseFailAlloc_6209_, 1, v_nextMacroScope_6191_);
lean_ctor_set(v_reuseFailAlloc_6209_, 2, v_ngen_6192_);
lean_ctor_set(v_reuseFailAlloc_6209_, 3, v_auxDeclNGen_6193_);
lean_ctor_set(v_reuseFailAlloc_6209_, 4, v_traceState_6194_);
lean_ctor_set(v_reuseFailAlloc_6209_, 5, v_cache_6195_);
lean_ctor_set(v_reuseFailAlloc_6209_, 6, v_recordedDeps_6196_);
lean_ctor_set(v_reuseFailAlloc_6209_, 7, v___x_6204_);
lean_ctor_set(v_reuseFailAlloc_6209_, 8, v_infoState_6198_);
lean_ctor_set(v_reuseFailAlloc_6209_, 9, v_snapshotTasks_6199_);
v___x_6206_ = v_reuseFailAlloc_6209_;
goto v_reusejp_6205_;
}
v_reusejp_6205_:
{
lean_object* v___x_6207_; lean_object* v___x_6208_; 
v___x_6207_ = lean_st_ref_put(v___y_6183_, v___x_6206_);
v___x_6208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6208_, 0, v___x_6203_);
return v___x_6208_;
}
}
}
v___jp_6211_:
{
lean_object* v_fileName_6220_; lean_object* v_fileMap_6221_; lean_object* v___x_6222_; lean_object* v___x_6223_; lean_object* v_a_6224_; lean_object* v___x_6226_; uint8_t v_isShared_6227_; uint8_t v_isSharedCheck_6237_; 
v_fileName_6220_ = lean_ctor_get(v___y_6216_, 0);
v_fileMap_6221_ = lean_ctor_get(v___y_6216_, 1);
v___x_6222_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_6166_);
v___x_6223_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(v___x_6222_, v___y_6169_, v___y_6170_, v___y_6171_, v___y_6172_);
v_a_6224_ = lean_ctor_get(v___x_6223_, 0);
v_isSharedCheck_6237_ = !lean_is_exclusive(v___x_6223_);
if (v_isSharedCheck_6237_ == 0)
{
v___x_6226_ = v___x_6223_;
v_isShared_6227_ = v_isSharedCheck_6237_;
goto v_resetjp_6225_;
}
else
{
lean_inc(v_a_6224_);
lean_dec(v___x_6223_);
v___x_6226_ = lean_box(0);
v_isShared_6227_ = v_isSharedCheck_6237_;
goto v_resetjp_6225_;
}
v_resetjp_6225_:
{
lean_object* v___x_6228_; lean_object* v___x_6229_; lean_object* v___x_6230_; lean_object* v___x_6231_; 
lean_inc_ref_n(v_fileMap_6221_, 2);
v___x_6228_ = l_Lean_FileMap_toPosition(v_fileMap_6221_, v___y_6214_);
lean_dec(v___y_6214_);
v___x_6229_ = l_Lean_FileMap_toPosition(v_fileMap_6221_, v___y_6219_);
lean_dec(v___y_6219_);
v___x_6230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6230_, 0, v___x_6229_);
v___x_6231_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___closed__0));
if (v___y_6217_ == 0)
{
lean_del_object(v___x_6226_);
lean_dec_ref(v___y_6213_);
v___y_6175_ = v_a_6224_;
v___y_6176_ = v___x_6231_;
v___y_6177_ = v___x_6230_;
v___y_6178_ = v_fileName_6220_;
v___y_6179_ = v___x_6228_;
v___y_6180_ = v___y_6215_;
v___y_6181_ = v___y_6218_;
v_toCold_6182_ = v___y_6212_;
v___y_6183_ = v___y_6172_;
goto v___jp_6174_;
}
else
{
uint8_t v___x_6232_; 
lean_inc(v_a_6224_);
v___x_6232_ = l_Lean_MessageData_hasTag(v___y_6213_, v_a_6224_);
if (v___x_6232_ == 0)
{
lean_object* v___x_6233_; lean_object* v___x_6235_; 
lean_dec_ref_known(v___x_6230_, 1);
lean_dec_ref(v___x_6228_);
lean_dec(v_a_6224_);
v___x_6233_ = lean_box(0);
if (v_isShared_6227_ == 0)
{
lean_ctor_set(v___x_6226_, 0, v___x_6233_);
v___x_6235_ = v___x_6226_;
goto v_reusejp_6234_;
}
else
{
lean_object* v_reuseFailAlloc_6236_; 
v_reuseFailAlloc_6236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6236_, 0, v___x_6233_);
v___x_6235_ = v_reuseFailAlloc_6236_;
goto v_reusejp_6234_;
}
v_reusejp_6234_:
{
return v___x_6235_;
}
}
else
{
lean_del_object(v___x_6226_);
v___y_6175_ = v_a_6224_;
v___y_6176_ = v___x_6231_;
v___y_6177_ = v___x_6230_;
v___y_6178_ = v_fileName_6220_;
v___y_6179_ = v___x_6228_;
v___y_6180_ = v___y_6215_;
v___y_6181_ = v___y_6218_;
v_toCold_6182_ = v___y_6212_;
v___y_6183_ = v___y_6172_;
goto v___jp_6174_;
}
}
}
}
v___jp_6238_:
{
lean_object* v___x_6246_; 
v___x_6246_ = l_Lean_Syntax_getTailPos_x3f(v___y_6242_, v___y_6244_);
lean_dec(v___y_6242_);
if (lean_obj_tag(v___x_6246_) == 0)
{
lean_inc(v___y_6245_);
v___y_6212_ = v___y_6239_;
v___y_6213_ = v___y_6240_;
v___y_6214_ = v___y_6245_;
v___y_6215_ = v___y_6243_;
v___y_6216_ = v___y_6239_;
v___y_6217_ = v___y_6241_;
v___y_6218_ = v___y_6244_;
v___y_6219_ = v___y_6245_;
goto v___jp_6211_;
}
else
{
lean_object* v_val_6247_; 
v_val_6247_ = lean_ctor_get(v___x_6246_, 0);
lean_inc(v_val_6247_);
lean_dec_ref_known(v___x_6246_, 1);
v___y_6212_ = v___y_6239_;
v___y_6213_ = v___y_6240_;
v___y_6214_ = v___y_6245_;
v___y_6215_ = v___y_6243_;
v___y_6216_ = v___y_6239_;
v___y_6217_ = v___y_6241_;
v___y_6218_ = v___y_6244_;
v___y_6219_ = v_val_6247_;
goto v___jp_6211_;
}
}
v___jp_6248_:
{
lean_object* v_toCold_6252_; lean_object* v_ref_6253_; uint8_t v_suppressElabErrors_6254_; lean_object* v___x_6255_; lean_object* v___x_6256_; lean_object* v___f_6257_; lean_object* v_ref_6258_; lean_object* v___x_6259_; 
v_toCold_6252_ = lean_ctor_get(v___y_6171_, 0);
v_ref_6253_ = lean_ctor_get(v___y_6171_, 2);
v_suppressElabErrors_6254_ = lean_ctor_get_uint8(v___y_6171_, sizeof(void*)*3 + 2);
v___x_6255_ = lean_box(v_suppressElabErrors_6254_);
v___x_6256_ = lean_box(v___y_6249_);
v___f_6257_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_6257_, 0, v___x_6255_);
lean_closure_set(v___f_6257_, 1, v___x_6256_);
v_ref_6258_ = l_Lean_replaceRef(v_ref_6165_, v_ref_6253_);
v___x_6259_ = l_Lean_Syntax_getPos_x3f(v_ref_6258_, v___y_6250_);
if (lean_obj_tag(v___x_6259_) == 0)
{
lean_object* v___x_6260_; 
v___x_6260_ = lean_unsigned_to_nat(0u);
v___y_6239_ = v_toCold_6252_;
v___y_6240_ = v___f_6257_;
v___y_6241_ = v_suppressElabErrors_6254_;
v___y_6242_ = v_ref_6258_;
v___y_6243_ = v___y_6251_;
v___y_6244_ = v___y_6250_;
v___y_6245_ = v___x_6260_;
goto v___jp_6238_;
}
else
{
lean_object* v_val_6261_; 
v_val_6261_ = lean_ctor_get(v___x_6259_, 0);
lean_inc(v_val_6261_);
lean_dec_ref_known(v___x_6259_, 1);
v___y_6239_ = v_toCold_6252_;
v___y_6240_ = v___f_6257_;
v___y_6241_ = v_suppressElabErrors_6254_;
v___y_6242_ = v_ref_6258_;
v___y_6243_ = v___y_6251_;
v___y_6244_ = v___y_6250_;
v___y_6245_ = v_val_6261_;
goto v___jp_6238_;
}
}
v___jp_6263_:
{
if (v___y_6266_ == 0)
{
v___y_6249_ = v___y_6264_;
v___y_6250_ = v___y_6265_;
v___y_6251_ = v_severity_6167_;
goto v___jp_6248_;
}
else
{
v___y_6249_ = v___y_6264_;
v___y_6250_ = v___y_6265_;
v___y_6251_ = v___x_6262_;
goto v___jp_6248_;
}
}
v___jp_6267_:
{
if (v___y_6268_ == 0)
{
uint8_t v___x_6269_; uint8_t v___x_6270_; 
v___x_6269_ = 1;
v___x_6270_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6167_, v___x_6269_);
if (v___x_6270_ == 0)
{
v___y_6264_ = v___y_6268_;
v___y_6265_ = v___y_6268_;
v___y_6266_ = v___x_6270_;
goto v___jp_6263_;
}
else
{
lean_object* v___x_6271_; lean_object* v___x_6272_; uint8_t v___x_6273_; 
v___x_6271_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_6171_);
v___x_6272_ = l_Lean_warningAsError;
v___x_6273_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7_spec__9(v___x_6271_, v___x_6272_);
lean_dec_ref(v___x_6271_);
v___y_6264_ = v___y_6268_;
v___y_6265_ = v___y_6268_;
v___y_6266_ = v___x_6273_;
goto v___jp_6263_;
}
}
else
{
lean_object* v___x_6274_; lean_object* v___x_6275_; 
lean_dec_ref(v_msgData_6166_);
v___x_6274_ = lean_box(0);
v___x_6275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6275_, 0, v___x_6274_);
return v___x_6275_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___boxed(lean_object* v_ref_6278_, lean_object* v_msgData_6279_, lean_object* v_severity_6280_, lean_object* v_isSilent_6281_, lean_object* v___y_6282_, lean_object* v___y_6283_, lean_object* v___y_6284_, lean_object* v___y_6285_, lean_object* v___y_6286_){
_start:
{
uint8_t v_severity_boxed_6287_; uint8_t v_isSilent_boxed_6288_; lean_object* v_res_6289_; 
v_severity_boxed_6287_ = lean_unbox(v_severity_6280_);
v_isSilent_boxed_6288_ = lean_unbox(v_isSilent_6281_);
v_res_6289_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7(v_ref_6278_, v_msgData_6279_, v_severity_boxed_6287_, v_isSilent_boxed_6288_, v___y_6282_, v___y_6283_, v___y_6284_, v___y_6285_);
lean_dec(v___y_6285_);
lean_dec_ref(v___y_6284_);
lean_dec(v___y_6283_);
lean_dec_ref(v___y_6282_);
lean_dec(v_ref_6278_);
return v_res_6289_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3(lean_object* v_msgData_6290_, uint8_t v_severity_6291_, uint8_t v_isSilent_6292_, lean_object* v___y_6293_, lean_object* v___y_6294_, lean_object* v___y_6295_, lean_object* v___y_6296_){
_start:
{
lean_object* v_ref_6298_; lean_object* v___x_6299_; 
v_ref_6298_ = lean_ctor_get(v___y_6295_, 2);
v___x_6299_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7(v_ref_6298_, v_msgData_6290_, v_severity_6291_, v_isSilent_6292_, v___y_6293_, v___y_6294_, v___y_6295_, v___y_6296_);
return v___x_6299_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_msgData_6300_, lean_object* v_severity_6301_, lean_object* v_isSilent_6302_, lean_object* v___y_6303_, lean_object* v___y_6304_, lean_object* v___y_6305_, lean_object* v___y_6306_, lean_object* v___y_6307_){
_start:
{
uint8_t v_severity_boxed_6308_; uint8_t v_isSilent_boxed_6309_; lean_object* v_res_6310_; 
v_severity_boxed_6308_ = lean_unbox(v_severity_6301_);
v_isSilent_boxed_6309_ = lean_unbox(v_isSilent_6302_);
v_res_6310_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3(v_msgData_6300_, v_severity_boxed_6308_, v_isSilent_boxed_6309_, v___y_6303_, v___y_6304_, v___y_6305_, v___y_6306_);
lean_dec(v___y_6306_);
lean_dec_ref(v___y_6305_);
lean_dec(v___y_6304_);
lean_dec_ref(v___y_6303_);
return v_res_6310_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2(lean_object* v_msgData_6311_, lean_object* v___y_6312_, lean_object* v___y_6313_, lean_object* v___y_6314_, lean_object* v___y_6315_){
_start:
{
uint8_t v___x_6317_; uint8_t v___x_6318_; lean_object* v___x_6319_; 
v___x_6317_ = 2;
v___x_6318_ = 0;
v___x_6319_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3(v_msgData_6311_, v___x_6317_, v___x_6318_, v___y_6312_, v___y_6313_, v___y_6314_, v___y_6315_);
return v___x_6319_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_6320_, lean_object* v___y_6321_, lean_object* v___y_6322_, lean_object* v___y_6323_, lean_object* v___y_6324_, lean_object* v___y_6325_){
_start:
{
lean_object* v_res_6326_; 
v_res_6326_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2(v_msgData_6320_, v___y_6321_, v___y_6322_, v___y_6323_, v___y_6324_);
lean_dec(v___y_6324_);
lean_dec_ref(v___y_6323_);
lean_dec(v___y_6322_);
lean_dec_ref(v___y_6321_);
return v_res_6326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0(lean_object* v_f_6327_, lean_object* v___y_6328_, lean_object* v___y_6329_, lean_object* v___y_6330_, lean_object* v___y_6331_){
_start:
{
lean_object* v_module_6333_; lean_object* v_const_6334_; lean_object* v_exception_6335_; lean_object* v___x_6336_; lean_object* v___x_6337_; lean_object* v___x_6338_; lean_object* v___x_6339_; lean_object* v___x_6340_; lean_object* v___x_6341_; lean_object* v___x_6342_; lean_object* v___x_6343_; lean_object* v___x_6344_; lean_object* v___x_6345_; lean_object* v___x_6346_; lean_object* v___x_6347_; 
v_module_6333_ = lean_ctor_get(v_f_6327_, 0);
lean_inc(v_module_6333_);
v_const_6334_ = lean_ctor_get(v_f_6327_, 1);
lean_inc(v_const_6334_);
v_exception_6335_ = lean_ctor_get(v_f_6327_, 2);
lean_inc_ref(v_exception_6335_);
lean_dec_ref(v_f_6327_);
v___x_6336_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1);
v___x_6337_ = l_Lean_MessageData_ofName(v_const_6334_);
v___x_6338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6338_, 0, v___x_6336_);
lean_ctor_set(v___x_6338_, 1, v___x_6337_);
v___x_6339_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3);
v___x_6340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6340_, 0, v___x_6338_);
lean_ctor_set(v___x_6340_, 1, v___x_6339_);
v___x_6341_ = l_Lean_MessageData_ofName(v_module_6333_);
v___x_6342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6342_, 0, v___x_6340_);
lean_ctor_set(v___x_6342_, 1, v___x_6341_);
v___x_6343_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5);
v___x_6344_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6344_, 0, v___x_6342_);
lean_ctor_set(v___x_6344_, 1, v___x_6343_);
v___x_6345_ = l_Lean_Exception_toMessageData(v_exception_6335_);
v___x_6346_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6346_, 0, v___x_6344_);
lean_ctor_set(v___x_6346_, 1, v___x_6345_);
v___x_6347_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2(v___x_6346_, v___y_6328_, v___y_6329_, v___y_6330_, v___y_6331_);
return v___x_6347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0___boxed(lean_object* v_f_6348_, lean_object* v___y_6349_, lean_object* v___y_6350_, lean_object* v___y_6351_, lean_object* v___y_6352_, lean_object* v___y_6353_){
_start:
{
lean_object* v_res_6354_; 
v_res_6354_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0(v_f_6348_, v___y_6349_, v___y_6350_, v___y_6351_, v___y_6352_);
lean_dec(v___y_6352_);
lean_dec_ref(v___y_6351_);
lean_dec(v___y_6350_);
lean_dec_ref(v___y_6349_);
return v_res_6354_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3(lean_object* v_as_6355_, size_t v_i_6356_, size_t v_stop_6357_, lean_object* v_b_6358_, lean_object* v___y_6359_, lean_object* v___y_6360_, lean_object* v___y_6361_, lean_object* v___y_6362_){
_start:
{
uint8_t v___x_6364_; 
v___x_6364_ = lean_usize_dec_eq(v_i_6356_, v_stop_6357_);
if (v___x_6364_ == 0)
{
lean_object* v___x_6365_; lean_object* v___x_6366_; 
v___x_6365_ = lean_array_uget_borrowed(v_as_6355_, v_i_6356_);
lean_inc(v___x_6365_);
v___x_6366_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0(v___x_6365_, v___y_6359_, v___y_6360_, v___y_6361_, v___y_6362_);
if (lean_obj_tag(v___x_6366_) == 0)
{
lean_object* v_a_6367_; size_t v___x_6368_; size_t v___x_6369_; 
v_a_6367_ = lean_ctor_get(v___x_6366_, 0);
lean_inc(v_a_6367_);
lean_dec_ref_known(v___x_6366_, 1);
v___x_6368_ = ((size_t)1ULL);
v___x_6369_ = lean_usize_add(v_i_6356_, v___x_6368_);
v_i_6356_ = v___x_6369_;
v_b_6358_ = v_a_6367_;
goto _start;
}
else
{
return v___x_6366_;
}
}
else
{
lean_object* v___x_6371_; 
v___x_6371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6371_, 0, v_b_6358_);
return v___x_6371_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3___boxed(lean_object* v_as_6372_, lean_object* v_i_6373_, lean_object* v_stop_6374_, lean_object* v_b_6375_, lean_object* v___y_6376_, lean_object* v___y_6377_, lean_object* v___y_6378_, lean_object* v___y_6379_, lean_object* v___y_6380_){
_start:
{
size_t v_i_boxed_6381_; size_t v_stop_boxed_6382_; lean_object* v_res_6383_; 
v_i_boxed_6381_ = lean_unbox_usize(v_i_6373_);
lean_dec(v_i_6373_);
v_stop_boxed_6382_ = lean_unbox_usize(v_stop_6374_);
lean_dec(v_stop_6374_);
v_res_6383_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3(v_as_6372_, v_i_boxed_6381_, v_stop_boxed_6382_, v_b_6375_, v___y_6376_, v___y_6377_, v___y_6378_, v___y_6379_);
lean_dec(v___y_6379_);
lean_dec_ref(v___y_6378_);
lean_dec(v___y_6377_);
lean_dec_ref(v___y_6376_);
lean_dec_ref(v_as_6372_);
return v_res_6383_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(lean_object* v_as_6384_, size_t v_i_6385_, size_t v_stop_6386_, lean_object* v_b_6387_){
_start:
{
uint8_t v___x_6388_; 
v___x_6388_ = lean_usize_dec_eq(v_i_6385_, v_stop_6386_);
if (v___x_6388_ == 0)
{
lean_object* v___x_6389_; lean_object* v___x_6390_; lean_object* v___x_6391_; size_t v___x_6392_; size_t v___x_6393_; 
v___x_6389_ = lean_array_uget_borrowed(v_as_6384_, v_i_6385_);
lean_inc(v___x_6389_);
v___x_6390_ = lean_task_get_own(v___x_6389_);
v___x_6391_ = l_Lean_Meta_LazyDiscrTree_InitResults_append___redArg(v_b_6387_, v___x_6390_);
v___x_6392_ = ((size_t)1ULL);
v___x_6393_ = lean_usize_add(v_i_6385_, v___x_6392_);
v_i_6385_ = v___x_6393_;
v_b_6387_ = v___x_6391_;
goto _start;
}
else
{
return v_b_6387_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_as_6395_, lean_object* v_i_6396_, lean_object* v_stop_6397_, lean_object* v_b_6398_){
_start:
{
size_t v_i_boxed_6399_; size_t v_stop_boxed_6400_; lean_object* v_res_6401_; 
v_i_boxed_6399_ = lean_unbox_usize(v_i_6396_);
lean_dec(v_i_6396_);
v_stop_boxed_6400_ = lean_unbox_usize(v_stop_6397_);
lean_dec(v_stop_6397_);
v_res_6401_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(v_as_6395_, v_i_boxed_6399_, v_stop_boxed_6400_, v_b_6398_);
lean_dec_ref(v_as_6395_);
return v_res_6401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(lean_object* v_z_6402_, lean_object* v_tasks_6403_){
_start:
{
lean_object* v___x_6404_; lean_object* v___x_6405_; uint8_t v___x_6406_; 
v___x_6404_ = lean_unsigned_to_nat(0u);
v___x_6405_ = lean_array_get_size(v_tasks_6403_);
v___x_6406_ = lean_nat_dec_lt(v___x_6404_, v___x_6405_);
if (v___x_6406_ == 0)
{
return v_z_6402_;
}
else
{
size_t v___x_6407_; size_t v___x_6408_; lean_object* v___x_6409_; 
v___x_6407_ = ((size_t)0ULL);
v___x_6408_ = lean_usize_of_nat(v___x_6405_);
v___x_6409_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(v_tasks_6403_, v___x_6407_, v___x_6408_, v_z_6402_);
return v___x_6409_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg___boxed(lean_object* v_z_6410_, lean_object* v_tasks_6411_){
_start:
{
lean_object* v_res_6412_; 
v_res_6412_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(v_z_6410_, v_tasks_6411_);
lean_dec_ref(v_tasks_6411_);
return v_res_6412_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_6413_; lean_object* v___x_6414_; lean_object* v___x_6415_; 
v___x_6413_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
v___x_6414_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2);
v___x_6415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6415_, 0, v___x_6414_);
lean_ctor_set(v___x_6415_, 1, v___x_6413_);
return v___x_6415_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_6416_; lean_object* v___x_6417_; lean_object* v___x_6418_; 
v___x_6416_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
v___x_6417_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0);
v___x_6418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6418_, 0, v___x_6417_);
lean_ctor_set(v___x_6418_, 1, v___x_6416_);
return v___x_6418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(lean_object* v_cctx_6419_, lean_object* v_ngen_6420_, lean_object* v_env_6421_, lean_object* v_act_6422_, lean_object* v_constantsPerTask_6423_, lean_object* v___y_6424_, lean_object* v___y_6425_, lean_object* v___y_6426_, lean_object* v___y_6427_){
_start:
{
lean_object* v___x_6429_; lean_object* v_moduleData_6430_; lean_object* v_n_6431_; lean_object* v___x_6432_; lean_object* v___x_6433_; lean_object* v___x_6434_; lean_object* v_a_6435_; lean_object* v___x_6437_; uint8_t v_isShared_6438_; uint8_t v_isSharedCheck_6470_; 
v___x_6429_ = l_Lean_Environment_header(v_env_6421_);
v_moduleData_6430_ = lean_ctor_get(v___x_6429_, 6);
lean_inc_ref(v_moduleData_6430_);
lean_dec_ref(v___x_6429_);
v_n_6431_ = lean_array_get_size(v_moduleData_6430_);
lean_dec_ref(v_moduleData_6430_);
v___x_6432_ = lean_unsigned_to_nat(0u);
v___x_6433_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
v___x_6434_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(v_cctx_6419_, v_env_6421_, v_act_6422_, v_constantsPerTask_6423_, v_n_6431_, v_ngen_6420_, v___x_6433_, v___x_6432_, v___x_6432_, v___x_6432_);
v_a_6435_ = lean_ctor_get(v___x_6434_, 0);
v_isSharedCheck_6470_ = !lean_is_exclusive(v___x_6434_);
if (v_isSharedCheck_6470_ == 0)
{
v___x_6437_ = v___x_6434_;
v_isShared_6438_ = v_isSharedCheck_6470_;
goto v_resetjp_6436_;
}
else
{
lean_inc(v_a_6435_);
lean_dec(v___x_6434_);
v___x_6437_ = lean_box(0);
v_isShared_6438_ = v_isSharedCheck_6470_;
goto v_resetjp_6436_;
}
v_resetjp_6436_:
{
lean_object* v___x_6439_; lean_object* v_r_6440_; lean_object* v_tree_6441_; lean_object* v_errors_6442_; lean_object* v___x_6443_; uint8_t v___x_6444_; 
v___x_6439_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1);
v_r_6440_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(v___x_6439_, v_a_6435_);
lean_dec(v_a_6435_);
v_tree_6441_ = lean_ctor_get(v_r_6440_, 0);
lean_inc_ref(v_tree_6441_);
v_errors_6442_ = lean_ctor_get(v_r_6440_, 1);
lean_inc_ref(v_errors_6442_);
lean_dec_ref(v_r_6440_);
v___x_6443_ = lean_array_get_size(v_errors_6442_);
v___x_6444_ = lean_nat_dec_lt(v___x_6432_, v___x_6443_);
if (v___x_6444_ == 0)
{
lean_object* v___x_6445_; lean_object* v___x_6447_; 
lean_dec_ref(v_errors_6442_);
v___x_6445_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_tree_6441_);
if (v_isShared_6438_ == 0)
{
lean_ctor_set(v___x_6437_, 0, v___x_6445_);
v___x_6447_ = v___x_6437_;
goto v_reusejp_6446_;
}
else
{
lean_object* v_reuseFailAlloc_6448_; 
v_reuseFailAlloc_6448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6448_, 0, v___x_6445_);
v___x_6447_ = v_reuseFailAlloc_6448_;
goto v_reusejp_6446_;
}
v_reusejp_6446_:
{
return v___x_6447_;
}
}
else
{
lean_object* v___x_6449_; size_t v___x_6450_; size_t v___x_6451_; lean_object* v___x_6452_; 
lean_del_object(v___x_6437_);
v___x_6449_ = lean_box(0);
v___x_6450_ = ((size_t)0ULL);
v___x_6451_ = lean_usize_of_nat(v___x_6443_);
v___x_6452_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3(v_errors_6442_, v___x_6450_, v___x_6451_, v___x_6449_, v___y_6424_, v___y_6425_, v___y_6426_, v___y_6427_);
lean_dec_ref(v_errors_6442_);
if (lean_obj_tag(v___x_6452_) == 0)
{
lean_object* v___x_6454_; uint8_t v_isShared_6455_; uint8_t v_isSharedCheck_6460_; 
v_isSharedCheck_6460_ = !lean_is_exclusive(v___x_6452_);
if (v_isSharedCheck_6460_ == 0)
{
lean_object* v_unused_6461_; 
v_unused_6461_ = lean_ctor_get(v___x_6452_, 0);
lean_dec(v_unused_6461_);
v___x_6454_ = v___x_6452_;
v_isShared_6455_ = v_isSharedCheck_6460_;
goto v_resetjp_6453_;
}
else
{
lean_dec(v___x_6452_);
v___x_6454_ = lean_box(0);
v_isShared_6455_ = v_isSharedCheck_6460_;
goto v_resetjp_6453_;
}
v_resetjp_6453_:
{
lean_object* v___x_6456_; lean_object* v___x_6458_; 
v___x_6456_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_tree_6441_);
if (v_isShared_6455_ == 0)
{
lean_ctor_set(v___x_6454_, 0, v___x_6456_);
v___x_6458_ = v___x_6454_;
goto v_reusejp_6457_;
}
else
{
lean_object* v_reuseFailAlloc_6459_; 
v_reuseFailAlloc_6459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6459_, 0, v___x_6456_);
v___x_6458_ = v_reuseFailAlloc_6459_;
goto v_reusejp_6457_;
}
v_reusejp_6457_:
{
return v___x_6458_;
}
}
}
else
{
lean_object* v_a_6462_; lean_object* v___x_6464_; uint8_t v_isShared_6465_; uint8_t v_isSharedCheck_6469_; 
lean_dec_ref(v_tree_6441_);
v_a_6462_ = lean_ctor_get(v___x_6452_, 0);
v_isSharedCheck_6469_ = !lean_is_exclusive(v___x_6452_);
if (v_isSharedCheck_6469_ == 0)
{
v___x_6464_ = v___x_6452_;
v_isShared_6465_ = v_isSharedCheck_6469_;
goto v_resetjp_6463_;
}
else
{
lean_inc(v_a_6462_);
lean_dec(v___x_6452_);
v___x_6464_ = lean_box(0);
v_isShared_6465_ = v_isSharedCheck_6469_;
goto v_resetjp_6463_;
}
v_resetjp_6463_:
{
lean_object* v___x_6467_; 
if (v_isShared_6465_ == 0)
{
v___x_6467_ = v___x_6464_;
goto v_reusejp_6466_;
}
else
{
lean_object* v_reuseFailAlloc_6468_; 
v_reuseFailAlloc_6468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6468_, 0, v_a_6462_);
v___x_6467_ = v_reuseFailAlloc_6468_;
goto v_reusejp_6466_;
}
v_reusejp_6466_:
{
return v___x_6467_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___boxed(lean_object* v_cctx_6471_, lean_object* v_ngen_6472_, lean_object* v_env_6473_, lean_object* v_act_6474_, lean_object* v_constantsPerTask_6475_, lean_object* v___y_6476_, lean_object* v___y_6477_, lean_object* v___y_6478_, lean_object* v___y_6479_, lean_object* v___y_6480_){
_start:
{
lean_object* v_res_6481_; 
v_res_6481_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(v_cctx_6471_, v_ngen_6472_, v_env_6473_, v_act_6474_, v_constantsPerTask_6475_, v___y_6476_, v___y_6477_, v___y_6478_, v___y_6479_);
lean_dec(v___y_6479_);
lean_dec_ref(v___y_6478_);
lean_dec(v___y_6477_);
lean_dec_ref(v___y_6476_);
lean_dec(v_constantsPerTask_6475_);
return v_res_6481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0(lean_object* v_a_6482_, lean_object* v___x_6483_, lean_object* v_addEntry_6484_, lean_object* v_constantsPerTask_6485_, lean_object* v_droppedEntriesRef_6486_, lean_object* v_droppedKeys_6487_, lean_object* v___y_6488_, lean_object* v___y_6489_, lean_object* v___y_6490_, lean_object* v___y_6491_){
_start:
{
lean_object* v___x_6493_; lean_object* v_env_6494_; lean_object* v___x_6495_; lean_object* v___x_6496_; 
v___x_6493_ = lean_st_ref_get(v___y_6491_);
v_env_6494_ = lean_ctor_get(v___x_6493_, 0);
lean_inc_ref(v_env_6494_);
lean_dec(v___x_6493_);
lean_inc_ref(v_a_6482_);
v___x_6495_ = l_Lean_Meta_LazyDiscrTree_createTreeCtx(v_a_6482_);
v___x_6496_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(v___x_6495_, v___x_6483_, v_env_6494_, v_addEntry_6484_, v_constantsPerTask_6485_, v___y_6488_, v___y_6489_, v___y_6490_, v___y_6491_);
if (lean_obj_tag(v___x_6496_) == 0)
{
if (lean_obj_tag(v_droppedEntriesRef_6486_) == 1)
{
lean_object* v_a_6497_; lean_object* v_val_6498_; lean_object* v___x_6500_; uint8_t v_isShared_6501_; uint8_t v_isSharedCheck_6531_; 
v_a_6497_ = lean_ctor_get(v___x_6496_, 0);
lean_inc(v_a_6497_);
lean_dec_ref_known(v___x_6496_, 1);
v_val_6498_ = lean_ctor_get(v_droppedEntriesRef_6486_, 0);
v_isSharedCheck_6531_ = !lean_is_exclusive(v_droppedEntriesRef_6486_);
if (v_isSharedCheck_6531_ == 0)
{
v___x_6500_ = v_droppedEntriesRef_6486_;
v_isShared_6501_ = v_isSharedCheck_6531_;
goto v_resetjp_6499_;
}
else
{
lean_inc(v_val_6498_);
lean_dec(v_droppedEntriesRef_6486_);
v___x_6500_ = lean_box(0);
v_isShared_6501_ = v_isSharedCheck_6531_;
goto v_resetjp_6499_;
}
v_resetjp_6499_:
{
lean_object* v___x_6502_; 
v___x_6502_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_a_6497_, v_droppedKeys_6487_, v___y_6488_, v___y_6489_, v___y_6490_, v___y_6491_);
lean_dec(v_droppedKeys_6487_);
if (lean_obj_tag(v___x_6502_) == 0)
{
lean_object* v_a_6503_; lean_object* v___x_6505_; uint8_t v_isShared_6506_; uint8_t v_isSharedCheck_6522_; 
v_a_6503_ = lean_ctor_get(v___x_6502_, 0);
v_isSharedCheck_6522_ = !lean_is_exclusive(v___x_6502_);
if (v_isSharedCheck_6522_ == 0)
{
v___x_6505_ = v___x_6502_;
v_isShared_6506_ = v_isSharedCheck_6522_;
goto v_resetjp_6504_;
}
else
{
lean_inc(v_a_6503_);
lean_dec(v___x_6502_);
v___x_6505_ = lean_box(0);
v_isShared_6506_ = v_isSharedCheck_6522_;
goto v_resetjp_6504_;
}
v_resetjp_6504_:
{
lean_object* v_fst_6507_; lean_object* v_snd_6508_; lean_object* v___x_6509_; lean_object* v___y_6511_; 
v_fst_6507_ = lean_ctor_get(v_a_6503_, 0);
lean_inc(v_fst_6507_);
v_snd_6508_ = lean_ctor_get(v_a_6503_, 1);
lean_inc(v_snd_6508_);
lean_dec(v_a_6503_);
v___x_6509_ = lean_st_ref_get(v_val_6498_);
if (lean_obj_tag(v___x_6509_) == 0)
{
lean_object* v___x_6520_; 
v___x_6520_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___y_6511_ = v___x_6520_;
goto v___jp_6510_;
}
else
{
lean_object* v_val_6521_; 
v_val_6521_ = lean_ctor_get(v___x_6509_, 0);
lean_inc(v_val_6521_);
lean_dec_ref_known(v___x_6509_, 1);
v___y_6511_ = v_val_6521_;
goto v___jp_6510_;
}
v___jp_6510_:
{
lean_object* v___x_6512_; lean_object* v___x_6514_; 
v___x_6512_ = l_Array_append___redArg(v___y_6511_, v_fst_6507_);
lean_dec(v_fst_6507_);
if (v_isShared_6501_ == 0)
{
lean_ctor_set(v___x_6500_, 0, v___x_6512_);
v___x_6514_ = v___x_6500_;
goto v_reusejp_6513_;
}
else
{
lean_object* v_reuseFailAlloc_6519_; 
v_reuseFailAlloc_6519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6519_, 0, v___x_6512_);
v___x_6514_ = v_reuseFailAlloc_6519_;
goto v_reusejp_6513_;
}
v_reusejp_6513_:
{
lean_object* v___x_6515_; lean_object* v___x_6517_; 
v___x_6515_ = lean_st_ref_swap(v_val_6498_, v___x_6514_);
lean_dec(v_val_6498_);
lean_dec(v___x_6515_);
if (v_isShared_6506_ == 0)
{
lean_ctor_set(v___x_6505_, 0, v_snd_6508_);
v___x_6517_ = v___x_6505_;
goto v_reusejp_6516_;
}
else
{
lean_object* v_reuseFailAlloc_6518_; 
v_reuseFailAlloc_6518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6518_, 0, v_snd_6508_);
v___x_6517_ = v_reuseFailAlloc_6518_;
goto v_reusejp_6516_;
}
v_reusejp_6516_:
{
return v___x_6517_;
}
}
}
}
}
else
{
lean_object* v_a_6523_; lean_object* v___x_6525_; uint8_t v_isShared_6526_; uint8_t v_isSharedCheck_6530_; 
lean_del_object(v___x_6500_);
lean_dec(v_val_6498_);
v_a_6523_ = lean_ctor_get(v___x_6502_, 0);
v_isSharedCheck_6530_ = !lean_is_exclusive(v___x_6502_);
if (v_isSharedCheck_6530_ == 0)
{
v___x_6525_ = v___x_6502_;
v_isShared_6526_ = v_isSharedCheck_6530_;
goto v_resetjp_6524_;
}
else
{
lean_inc(v_a_6523_);
lean_dec(v___x_6502_);
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
}
else
{
lean_object* v_a_6532_; lean_object* v___x_6533_; 
lean_dec(v_droppedEntriesRef_6486_);
v_a_6532_ = lean_ctor_get(v___x_6496_, 0);
lean_inc(v_a_6532_);
lean_dec_ref_known(v___x_6496_, 1);
v___x_6533_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_a_6532_, v_droppedKeys_6487_, v___y_6488_, v___y_6489_, v___y_6490_, v___y_6491_);
return v___x_6533_;
}
}
else
{
lean_dec(v_droppedKeys_6487_);
lean_dec(v_droppedEntriesRef_6486_);
return v___x_6496_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0___boxed(lean_object* v_a_6534_, lean_object* v___x_6535_, lean_object* v_addEntry_6536_, lean_object* v_constantsPerTask_6537_, lean_object* v_droppedEntriesRef_6538_, lean_object* v_droppedKeys_6539_, lean_object* v___y_6540_, lean_object* v___y_6541_, lean_object* v___y_6542_, lean_object* v___y_6543_, lean_object* v___y_6544_){
_start:
{
lean_object* v_res_6545_; 
v_res_6545_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0(v_a_6534_, v___x_6535_, v_addEntry_6536_, v_constantsPerTask_6537_, v_droppedEntriesRef_6538_, v_droppedKeys_6539_, v___y_6540_, v___y_6541_, v___y_6542_, v___y_6543_);
lean_dec(v___y_6543_);
lean_dec_ref(v___y_6542_);
lean_dec(v___y_6541_);
lean_dec_ref(v___y_6540_);
lean_dec(v_constantsPerTask_6537_);
lean_dec_ref(v_a_6534_);
return v_res_6545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(lean_object* v_ref_6547_, lean_object* v_addEntry_6548_, lean_object* v_droppedKeys_6549_, lean_object* v_constantsPerTask_6550_, lean_object* v_droppedEntriesRef_6551_, lean_object* v_ty_6552_, lean_object* v_a_6553_, lean_object* v_a_6554_, lean_object* v_a_6555_, lean_object* v_a_6556_){
_start:
{
lean_object* v_a_6559_; lean_object* v___x_6581_; lean_object* v_ngen_6582_; lean_object* v_namePrefix_6583_; lean_object* v_idx_6584_; lean_object* v___x_6586_; uint8_t v_isShared_6587_; uint8_t v_isSharedCheck_6630_; 
v___x_6581_ = lean_st_ref_get(v_a_6556_);
v_ngen_6582_ = lean_ctor_get(v___x_6581_, 2);
lean_inc_ref(v_ngen_6582_);
lean_dec(v___x_6581_);
v_namePrefix_6583_ = lean_ctor_get(v_ngen_6582_, 0);
v_idx_6584_ = lean_ctor_get(v_ngen_6582_, 1);
v_isSharedCheck_6630_ = !lean_is_exclusive(v_ngen_6582_);
if (v_isSharedCheck_6630_ == 0)
{
v___x_6586_ = v_ngen_6582_;
v_isShared_6587_ = v_isSharedCheck_6630_;
goto v_resetjp_6585_;
}
else
{
lean_inc(v_idx_6584_);
lean_inc(v_namePrefix_6583_);
lean_dec(v_ngen_6582_);
v___x_6586_ = lean_box(0);
v_isShared_6587_ = v_isSharedCheck_6630_;
goto v_resetjp_6585_;
}
v___jp_6558_:
{
lean_object* v___x_6560_; 
v___x_6560_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v_a_6559_, v_ty_6552_, v_a_6553_, v_a_6554_, v_a_6555_, v_a_6556_);
if (lean_obj_tag(v___x_6560_) == 0)
{
lean_object* v_a_6561_; lean_object* v___x_6563_; uint8_t v_isShared_6564_; uint8_t v_isSharedCheck_6572_; 
v_a_6561_ = lean_ctor_get(v___x_6560_, 0);
v_isSharedCheck_6572_ = !lean_is_exclusive(v___x_6560_);
if (v_isSharedCheck_6572_ == 0)
{
v___x_6563_ = v___x_6560_;
v_isShared_6564_ = v_isSharedCheck_6572_;
goto v_resetjp_6562_;
}
else
{
lean_inc(v_a_6561_);
lean_dec(v___x_6560_);
v___x_6563_ = lean_box(0);
v_isShared_6564_ = v_isSharedCheck_6572_;
goto v_resetjp_6562_;
}
v_resetjp_6562_:
{
lean_object* v_fst_6565_; lean_object* v_snd_6566_; lean_object* v___x_6567_; lean_object* v___x_6568_; lean_object* v___x_6570_; 
v_fst_6565_ = lean_ctor_get(v_a_6561_, 0);
lean_inc(v_fst_6565_);
v_snd_6566_ = lean_ctor_get(v_a_6561_, 1);
lean_inc(v_snd_6566_);
lean_dec(v_a_6561_);
v___x_6567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6567_, 0, v_snd_6566_);
v___x_6568_ = lean_st_ref_swap(v_ref_6547_, v___x_6567_);
lean_dec(v___x_6568_);
if (v_isShared_6564_ == 0)
{
lean_ctor_set(v___x_6563_, 0, v_fst_6565_);
v___x_6570_ = v___x_6563_;
goto v_reusejp_6569_;
}
else
{
lean_object* v_reuseFailAlloc_6571_; 
v_reuseFailAlloc_6571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6571_, 0, v_fst_6565_);
v___x_6570_ = v_reuseFailAlloc_6571_;
goto v_reusejp_6569_;
}
v_reusejp_6569_:
{
return v___x_6570_;
}
}
}
else
{
lean_object* v_a_6573_; lean_object* v___x_6575_; uint8_t v_isShared_6576_; uint8_t v_isSharedCheck_6580_; 
v_a_6573_ = lean_ctor_get(v___x_6560_, 0);
v_isSharedCheck_6580_ = !lean_is_exclusive(v___x_6560_);
if (v_isSharedCheck_6580_ == 0)
{
v___x_6575_ = v___x_6560_;
v_isShared_6576_ = v_isSharedCheck_6580_;
goto v_resetjp_6574_;
}
else
{
lean_inc(v_a_6573_);
lean_dec(v___x_6560_);
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
v_resetjp_6585_:
{
lean_object* v___x_6588_; lean_object* v___x_6589_; lean_object* v___x_6591_; 
lean_inc(v_idx_6584_);
lean_inc(v_namePrefix_6583_);
v___x_6588_ = l_Lean_Name_num___override(v_namePrefix_6583_, v_idx_6584_);
v___x_6589_ = lean_unsigned_to_nat(1u);
if (v_isShared_6587_ == 0)
{
lean_ctor_set(v___x_6586_, 1, v___x_6589_);
lean_ctor_set(v___x_6586_, 0, v___x_6588_);
v___x_6591_ = v___x_6586_;
goto v_reusejp_6590_;
}
else
{
lean_object* v_reuseFailAlloc_6629_; 
v_reuseFailAlloc_6629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6629_, 0, v___x_6588_);
lean_ctor_set(v_reuseFailAlloc_6629_, 1, v___x_6589_);
v___x_6591_ = v_reuseFailAlloc_6629_;
goto v_reusejp_6590_;
}
v_reusejp_6590_:
{
lean_object* v___f_6592_; lean_object* v___x_6593_; lean_object* v___x_6594_; lean_object* v___x_6595_; lean_object* v_env_6596_; lean_object* v_nextMacroScope_6597_; lean_object* v_auxDeclNGen_6598_; lean_object* v_traceState_6599_; lean_object* v_cache_6600_; lean_object* v_recordedDeps_6601_; lean_object* v_messages_6602_; lean_object* v_infoState_6603_; lean_object* v_snapshotTasks_6604_; lean_object* v___x_6606_; uint8_t v_isShared_6607_; uint8_t v_isSharedCheck_6627_; 
lean_inc_ref(v_a_6555_);
v___f_6592_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_6592_, 0, v_a_6555_);
lean_closure_set(v___f_6592_, 1, v___x_6591_);
lean_closure_set(v___f_6592_, 2, v_addEntry_6548_);
lean_closure_set(v___f_6592_, 3, v_constantsPerTask_6550_);
lean_closure_set(v___f_6592_, 4, v_droppedEntriesRef_6551_);
lean_closure_set(v___f_6592_, 5, v_droppedKeys_6549_);
v___x_6593_ = lean_nat_add(v_idx_6584_, v___x_6589_);
lean_dec(v_idx_6584_);
v___x_6594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6594_, 0, v_namePrefix_6583_);
lean_ctor_set(v___x_6594_, 1, v___x_6593_);
v___x_6595_ = lean_st_ref_take(v_a_6556_);
v_env_6596_ = lean_ctor_get(v___x_6595_, 0);
v_nextMacroScope_6597_ = lean_ctor_get(v___x_6595_, 1);
v_auxDeclNGen_6598_ = lean_ctor_get(v___x_6595_, 3);
v_traceState_6599_ = lean_ctor_get(v___x_6595_, 4);
v_cache_6600_ = lean_ctor_get(v___x_6595_, 5);
v_recordedDeps_6601_ = lean_ctor_get(v___x_6595_, 6);
v_messages_6602_ = lean_ctor_get(v___x_6595_, 7);
v_infoState_6603_ = lean_ctor_get(v___x_6595_, 8);
v_snapshotTasks_6604_ = lean_ctor_get(v___x_6595_, 9);
v_isSharedCheck_6627_ = !lean_is_exclusive(v___x_6595_);
if (v_isSharedCheck_6627_ == 0)
{
lean_object* v_unused_6628_; 
v_unused_6628_ = lean_ctor_get(v___x_6595_, 2);
lean_dec(v_unused_6628_);
v___x_6606_ = v___x_6595_;
v_isShared_6607_ = v_isSharedCheck_6627_;
goto v_resetjp_6605_;
}
else
{
lean_inc(v_snapshotTasks_6604_);
lean_inc(v_infoState_6603_);
lean_inc(v_messages_6602_);
lean_inc(v_recordedDeps_6601_);
lean_inc(v_cache_6600_);
lean_inc(v_traceState_6599_);
lean_inc(v_auxDeclNGen_6598_);
lean_inc(v_nextMacroScope_6597_);
lean_inc(v_env_6596_);
lean_dec(v___x_6595_);
v___x_6606_ = lean_box(0);
v_isShared_6607_ = v_isSharedCheck_6627_;
goto v_resetjp_6605_;
}
v_resetjp_6605_:
{
lean_object* v___x_6609_; 
if (v_isShared_6607_ == 0)
{
lean_ctor_set(v___x_6606_, 2, v___x_6594_);
v___x_6609_ = v___x_6606_;
goto v_reusejp_6608_;
}
else
{
lean_object* v_reuseFailAlloc_6626_; 
v_reuseFailAlloc_6626_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6626_, 0, v_env_6596_);
lean_ctor_set(v_reuseFailAlloc_6626_, 1, v_nextMacroScope_6597_);
lean_ctor_set(v_reuseFailAlloc_6626_, 2, v___x_6594_);
lean_ctor_set(v_reuseFailAlloc_6626_, 3, v_auxDeclNGen_6598_);
lean_ctor_set(v_reuseFailAlloc_6626_, 4, v_traceState_6599_);
lean_ctor_set(v_reuseFailAlloc_6626_, 5, v_cache_6600_);
lean_ctor_set(v_reuseFailAlloc_6626_, 6, v_recordedDeps_6601_);
lean_ctor_set(v_reuseFailAlloc_6626_, 7, v_messages_6602_);
lean_ctor_set(v_reuseFailAlloc_6626_, 8, v_infoState_6603_);
lean_ctor_set(v_reuseFailAlloc_6626_, 9, v_snapshotTasks_6604_);
v___x_6609_ = v_reuseFailAlloc_6626_;
goto v_reusejp_6608_;
}
v_reusejp_6608_:
{
lean_object* v___x_6610_; lean_object* v___x_6611_; 
v___x_6610_ = lean_st_ref_put(v_a_6556_, v___x_6609_);
v___x_6611_ = lean_st_ref_get(v_ref_6547_);
if (lean_obj_tag(v___x_6611_) == 0)
{
lean_object* v___x_6612_; lean_object* v___x_6613_; lean_object* v___x_6614_; lean_object* v___x_6615_; 
v___x_6612_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_6555_);
v___x_6613_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___closed__0));
v___x_6614_ = lean_box(0);
v___x_6615_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v___x_6613_, v___x_6612_, v___f_6592_, v___x_6614_, v_a_6553_, v_a_6554_, v_a_6555_, v_a_6556_);
lean_dec_ref(v___x_6612_);
if (lean_obj_tag(v___x_6615_) == 0)
{
lean_object* v_a_6616_; 
v_a_6616_ = lean_ctor_get(v___x_6615_, 0);
lean_inc(v_a_6616_);
lean_dec_ref_known(v___x_6615_, 1);
v_a_6559_ = v_a_6616_;
goto v___jp_6558_;
}
else
{
lean_object* v_a_6617_; lean_object* v___x_6619_; uint8_t v_isShared_6620_; uint8_t v_isSharedCheck_6624_; 
lean_dec_ref(v_ty_6552_);
v_a_6617_ = lean_ctor_get(v___x_6615_, 0);
v_isSharedCheck_6624_ = !lean_is_exclusive(v___x_6615_);
if (v_isSharedCheck_6624_ == 0)
{
v___x_6619_ = v___x_6615_;
v_isShared_6620_ = v_isSharedCheck_6624_;
goto v_resetjp_6618_;
}
else
{
lean_inc(v_a_6617_);
lean_dec(v___x_6615_);
v___x_6619_ = lean_box(0);
v_isShared_6620_ = v_isSharedCheck_6624_;
goto v_resetjp_6618_;
}
v_resetjp_6618_:
{
lean_object* v___x_6622_; 
if (v_isShared_6620_ == 0)
{
v___x_6622_ = v___x_6619_;
goto v_reusejp_6621_;
}
else
{
lean_object* v_reuseFailAlloc_6623_; 
v_reuseFailAlloc_6623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6623_, 0, v_a_6617_);
v___x_6622_ = v_reuseFailAlloc_6623_;
goto v_reusejp_6621_;
}
v_reusejp_6621_:
{
return v___x_6622_;
}
}
}
}
else
{
lean_object* v_val_6625_; 
lean_dec_ref(v___f_6592_);
v_val_6625_ = lean_ctor_get(v___x_6611_, 0);
lean_inc(v_val_6625_);
lean_dec_ref_known(v___x_6611_, 1);
v_a_6559_ = v_val_6625_;
goto v___jp_6558_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___boxed(lean_object* v_ref_6631_, lean_object* v_addEntry_6632_, lean_object* v_droppedKeys_6633_, lean_object* v_constantsPerTask_6634_, lean_object* v_droppedEntriesRef_6635_, lean_object* v_ty_6636_, lean_object* v_a_6637_, lean_object* v_a_6638_, lean_object* v_a_6639_, lean_object* v_a_6640_, lean_object* v_a_6641_){
_start:
{
lean_object* v_res_6642_; 
v_res_6642_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(v_ref_6631_, v_addEntry_6632_, v_droppedKeys_6633_, v_constantsPerTask_6634_, v_droppedEntriesRef_6635_, v_ty_6636_, v_a_6637_, v_a_6638_, v_a_6639_, v_a_6640_);
lean_dec(v_a_6640_);
lean_dec_ref(v_a_6639_);
lean_dec(v_a_6638_);
lean_dec_ref(v_a_6637_);
lean_dec(v_ref_6631_);
return v_res_6642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches(lean_object* v_00_u03b1_6643_, lean_object* v_ref_6644_, lean_object* v_addEntry_6645_, lean_object* v_droppedKeys_6646_, lean_object* v_constantsPerTask_6647_, lean_object* v_droppedEntriesRef_6648_, lean_object* v_ty_6649_, lean_object* v_a_6650_, lean_object* v_a_6651_, lean_object* v_a_6652_, lean_object* v_a_6653_){
_start:
{
lean_object* v___x_6655_; 
v___x_6655_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(v_ref_6644_, v_addEntry_6645_, v_droppedKeys_6646_, v_constantsPerTask_6647_, v_droppedEntriesRef_6648_, v_ty_6649_, v_a_6650_, v_a_6651_, v_a_6652_, v_a_6653_);
return v___x_6655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___boxed(lean_object* v_00_u03b1_6656_, lean_object* v_ref_6657_, lean_object* v_addEntry_6658_, lean_object* v_droppedKeys_6659_, lean_object* v_constantsPerTask_6660_, lean_object* v_droppedEntriesRef_6661_, lean_object* v_ty_6662_, lean_object* v_a_6663_, lean_object* v_a_6664_, lean_object* v_a_6665_, lean_object* v_a_6666_, lean_object* v_a_6667_){
_start:
{
lean_object* v_res_6668_; 
v_res_6668_ = l_Lean_Meta_LazyDiscrTree_findImportMatches(v_00_u03b1_6656_, v_ref_6657_, v_addEntry_6658_, v_droppedKeys_6659_, v_constantsPerTask_6660_, v_droppedEntriesRef_6661_, v_ty_6662_, v_a_6663_, v_a_6664_, v_a_6665_, v_a_6666_);
lean_dec(v_a_6666_);
lean_dec_ref(v_a_6665_);
lean_dec(v_a_6664_);
lean_dec_ref(v_a_6663_);
lean_dec(v_ref_6657_);
return v_res_6668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0(lean_object* v_00_u03b1_6669_, lean_object* v_cctx_6670_, lean_object* v_ngen_6671_, lean_object* v_env_6672_, lean_object* v_act_6673_, lean_object* v_constantsPerTask_6674_, lean_object* v___y_6675_, lean_object* v___y_6676_, lean_object* v___y_6677_, lean_object* v___y_6678_){
_start:
{
lean_object* v___x_6680_; 
v___x_6680_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(v_cctx_6670_, v_ngen_6671_, v_env_6672_, v_act_6673_, v_constantsPerTask_6674_, v___y_6675_, v___y_6676_, v___y_6677_, v___y_6678_);
return v___x_6680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___boxed(lean_object* v_00_u03b1_6681_, lean_object* v_cctx_6682_, lean_object* v_ngen_6683_, lean_object* v_env_6684_, lean_object* v_act_6685_, lean_object* v_constantsPerTask_6686_, lean_object* v___y_6687_, lean_object* v___y_6688_, lean_object* v___y_6689_, lean_object* v___y_6690_, lean_object* v___y_6691_){
_start:
{
lean_object* v_res_6692_; 
v_res_6692_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0(v_00_u03b1_6681_, v_cctx_6682_, v_ngen_6683_, v_env_6684_, v_act_6685_, v_constantsPerTask_6686_, v___y_6687_, v___y_6688_, v___y_6689_, v___y_6690_);
lean_dec(v___y_6690_);
lean_dec_ref(v___y_6689_);
lean_dec(v___y_6688_);
lean_dec_ref(v___y_6687_);
lean_dec(v_constantsPerTask_6686_);
return v_res_6692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1(lean_object* v_00_u03b1_6693_, lean_object* v_cctx_6694_, lean_object* v_env_6695_, lean_object* v_act_6696_, lean_object* v_constantsPerTask_6697_, lean_object* v_n_6698_, lean_object* v_ngen_6699_, lean_object* v_tasks_6700_, lean_object* v_start_6701_, lean_object* v_cnt_6702_, lean_object* v_idx_6703_, lean_object* v___y_6704_, lean_object* v___y_6705_, lean_object* v___y_6706_, lean_object* v___y_6707_){
_start:
{
lean_object* v___x_6709_; 
v___x_6709_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(v_cctx_6694_, v_env_6695_, v_act_6696_, v_constantsPerTask_6697_, v_n_6698_, v_ngen_6699_, v_tasks_6700_, v_start_6701_, v_cnt_6702_, v_idx_6703_);
return v___x_6709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___boxed(lean_object* v_00_u03b1_6710_, lean_object* v_cctx_6711_, lean_object* v_env_6712_, lean_object* v_act_6713_, lean_object* v_constantsPerTask_6714_, lean_object* v_n_6715_, lean_object* v_ngen_6716_, lean_object* v_tasks_6717_, lean_object* v_start_6718_, lean_object* v_cnt_6719_, lean_object* v_idx_6720_, lean_object* v___y_6721_, lean_object* v___y_6722_, lean_object* v___y_6723_, lean_object* v___y_6724_, lean_object* v___y_6725_){
_start:
{
lean_object* v_res_6726_; 
v_res_6726_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1(v_00_u03b1_6710_, v_cctx_6711_, v_env_6712_, v_act_6713_, v_constantsPerTask_6714_, v_n_6715_, v_ngen_6716_, v_tasks_6717_, v_start_6718_, v_cnt_6719_, v_idx_6720_, v___y_6721_, v___y_6722_, v___y_6723_, v___y_6724_);
lean_dec(v___y_6724_);
lean_dec_ref(v___y_6723_);
lean_dec(v___y_6722_);
lean_dec_ref(v___y_6721_);
lean_dec(v_constantsPerTask_6714_);
return v_res_6726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2(lean_object* v_00_u03b1_6727_, lean_object* v_z_6728_, lean_object* v_tasks_6729_){
_start:
{
lean_object* v___x_6730_; 
v___x_6730_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(v_z_6728_, v_tasks_6729_);
return v___x_6730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___boxed(lean_object* v_00_u03b1_6731_, lean_object* v_z_6732_, lean_object* v_tasks_6733_){
_start:
{
lean_object* v_res_6734_; 
v_res_6734_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2(v_00_u03b1_6731_, v_z_6732_, v_tasks_6733_);
lean_dec_ref(v_tasks_6733_);
return v_res_6734_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5(lean_object* v_00_u03b1_6735_, lean_object* v_as_6736_, size_t v_i_6737_, size_t v_stop_6738_, lean_object* v_b_6739_){
_start:
{
lean_object* v___x_6740_; 
v___x_6740_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(v_as_6736_, v_i_6737_, v_stop_6738_, v_b_6739_);
return v___x_6740_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b1_6741_, lean_object* v_as_6742_, lean_object* v_i_6743_, lean_object* v_stop_6744_, lean_object* v_b_6745_){
_start:
{
size_t v_i_boxed_6746_; size_t v_stop_boxed_6747_; lean_object* v_res_6748_; 
v_i_boxed_6746_ = lean_unbox_usize(v_i_6743_);
lean_dec(v_i_6743_);
v_stop_boxed_6747_ = lean_unbox_usize(v_stop_6744_);
lean_dec(v_stop_6744_);
v_res_6748_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5(v_00_u03b1_6741_, v_as_6742_, v_i_boxed_6746_, v_stop_boxed_6747_, v_b_6745_);
lean_dec_ref(v_as_6742_);
return v_res_6748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(lean_object* v___y_6749_){
_start:
{
lean_object* v___x_6751_; lean_object* v_ngen_6752_; lean_object* v_namePrefix_6753_; lean_object* v_idx_6754_; lean_object* v___x_6756_; uint8_t v_isShared_6757_; uint8_t v_isSharedCheck_6785_; 
v___x_6751_ = lean_st_ref_get(v___y_6749_);
v_ngen_6752_ = lean_ctor_get(v___x_6751_, 2);
lean_inc_ref(v_ngen_6752_);
lean_dec(v___x_6751_);
v_namePrefix_6753_ = lean_ctor_get(v_ngen_6752_, 0);
v_idx_6754_ = lean_ctor_get(v_ngen_6752_, 1);
v_isSharedCheck_6785_ = !lean_is_exclusive(v_ngen_6752_);
if (v_isSharedCheck_6785_ == 0)
{
v___x_6756_ = v_ngen_6752_;
v_isShared_6757_ = v_isSharedCheck_6785_;
goto v_resetjp_6755_;
}
else
{
lean_inc(v_idx_6754_);
lean_inc(v_namePrefix_6753_);
lean_dec(v_ngen_6752_);
v___x_6756_ = lean_box(0);
v_isShared_6757_ = v_isSharedCheck_6785_;
goto v_resetjp_6755_;
}
v_resetjp_6755_:
{
lean_object* v___x_6758_; lean_object* v___x_6759_; lean_object* v___x_6761_; 
lean_inc(v_idx_6754_);
lean_inc(v_namePrefix_6753_);
v___x_6758_ = l_Lean_Name_num___override(v_namePrefix_6753_, v_idx_6754_);
v___x_6759_ = lean_unsigned_to_nat(1u);
if (v_isShared_6757_ == 0)
{
lean_ctor_set(v___x_6756_, 1, v___x_6759_);
lean_ctor_set(v___x_6756_, 0, v___x_6758_);
v___x_6761_ = v___x_6756_;
goto v_reusejp_6760_;
}
else
{
lean_object* v_reuseFailAlloc_6784_; 
v_reuseFailAlloc_6784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6784_, 0, v___x_6758_);
lean_ctor_set(v_reuseFailAlloc_6784_, 1, v___x_6759_);
v___x_6761_ = v_reuseFailAlloc_6784_;
goto v_reusejp_6760_;
}
v_reusejp_6760_:
{
lean_object* v___x_6762_; lean_object* v___x_6763_; lean_object* v___x_6764_; lean_object* v_env_6765_; lean_object* v_nextMacroScope_6766_; lean_object* v_auxDeclNGen_6767_; lean_object* v_traceState_6768_; lean_object* v_cache_6769_; lean_object* v_recordedDeps_6770_; lean_object* v_messages_6771_; lean_object* v_infoState_6772_; lean_object* v_snapshotTasks_6773_; lean_object* v___x_6775_; uint8_t v_isShared_6776_; uint8_t v_isSharedCheck_6782_; 
v___x_6762_ = lean_nat_add(v_idx_6754_, v___x_6759_);
lean_dec(v_idx_6754_);
v___x_6763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6763_, 0, v_namePrefix_6753_);
lean_ctor_set(v___x_6763_, 1, v___x_6762_);
v___x_6764_ = lean_st_ref_take(v___y_6749_);
v_env_6765_ = lean_ctor_get(v___x_6764_, 0);
v_nextMacroScope_6766_ = lean_ctor_get(v___x_6764_, 1);
v_auxDeclNGen_6767_ = lean_ctor_get(v___x_6764_, 3);
v_traceState_6768_ = lean_ctor_get(v___x_6764_, 4);
v_cache_6769_ = lean_ctor_get(v___x_6764_, 5);
v_recordedDeps_6770_ = lean_ctor_get(v___x_6764_, 6);
v_messages_6771_ = lean_ctor_get(v___x_6764_, 7);
v_infoState_6772_ = lean_ctor_get(v___x_6764_, 8);
v_snapshotTasks_6773_ = lean_ctor_get(v___x_6764_, 9);
v_isSharedCheck_6782_ = !lean_is_exclusive(v___x_6764_);
if (v_isSharedCheck_6782_ == 0)
{
lean_object* v_unused_6783_; 
v_unused_6783_ = lean_ctor_get(v___x_6764_, 2);
lean_dec(v_unused_6783_);
v___x_6775_ = v___x_6764_;
v_isShared_6776_ = v_isSharedCheck_6782_;
goto v_resetjp_6774_;
}
else
{
lean_inc(v_snapshotTasks_6773_);
lean_inc(v_infoState_6772_);
lean_inc(v_messages_6771_);
lean_inc(v_recordedDeps_6770_);
lean_inc(v_cache_6769_);
lean_inc(v_traceState_6768_);
lean_inc(v_auxDeclNGen_6767_);
lean_inc(v_nextMacroScope_6766_);
lean_inc(v_env_6765_);
lean_dec(v___x_6764_);
v___x_6775_ = lean_box(0);
v_isShared_6776_ = v_isSharedCheck_6782_;
goto v_resetjp_6774_;
}
v_resetjp_6774_:
{
lean_object* v___x_6778_; 
if (v_isShared_6776_ == 0)
{
lean_ctor_set(v___x_6775_, 2, v___x_6763_);
v___x_6778_ = v___x_6775_;
goto v_reusejp_6777_;
}
else
{
lean_object* v_reuseFailAlloc_6781_; 
v_reuseFailAlloc_6781_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6781_, 0, v_env_6765_);
lean_ctor_set(v_reuseFailAlloc_6781_, 1, v_nextMacroScope_6766_);
lean_ctor_set(v_reuseFailAlloc_6781_, 2, v___x_6763_);
lean_ctor_set(v_reuseFailAlloc_6781_, 3, v_auxDeclNGen_6767_);
lean_ctor_set(v_reuseFailAlloc_6781_, 4, v_traceState_6768_);
lean_ctor_set(v_reuseFailAlloc_6781_, 5, v_cache_6769_);
lean_ctor_set(v_reuseFailAlloc_6781_, 6, v_recordedDeps_6770_);
lean_ctor_set(v_reuseFailAlloc_6781_, 7, v_messages_6771_);
lean_ctor_set(v_reuseFailAlloc_6781_, 8, v_infoState_6772_);
lean_ctor_set(v_reuseFailAlloc_6781_, 9, v_snapshotTasks_6773_);
v___x_6778_ = v_reuseFailAlloc_6781_;
goto v_reusejp_6777_;
}
v_reusejp_6777_:
{
lean_object* v___x_6779_; lean_object* v___x_6780_; 
v___x_6779_ = lean_st_ref_put(v___y_6749_, v___x_6778_);
v___x_6780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6780_, 0, v___x_6761_);
return v___x_6780_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg___boxed(lean_object* v___y_6786_, lean_object* v___y_6787_){
_start:
{
lean_object* v_res_6788_; 
v_res_6788_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(v___y_6786_);
lean_dec(v___y_6786_);
return v_res_6788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1(lean_object* v___y_6789_, lean_object* v___y_6790_){
_start:
{
lean_object* v___x_6792_; 
v___x_6792_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(v___y_6790_);
return v___x_6792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___boxed(lean_object* v___y_6793_, lean_object* v___y_6794_, lean_object* v___y_6795_){
_start:
{
lean_object* v_res_6796_; 
v_res_6796_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1(v___y_6793_, v___y_6794_);
lean_dec(v___y_6794_);
lean_dec_ref(v___y_6793_);
return v_res_6796_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0(void){
_start:
{
lean_object* v___x_6797_; lean_object* v___x_6798_; lean_object* v___x_6799_; 
v___x_6797_ = lean_unsigned_to_nat(32u);
v___x_6798_ = lean_mk_empty_array_with_capacity(v___x_6797_);
v___x_6799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6799_, 0, v___x_6798_);
return v___x_6799_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1(void){
_start:
{
size_t v___x_6800_; lean_object* v___x_6801_; lean_object* v___x_6802_; lean_object* v___x_6803_; lean_object* v___x_6804_; lean_object* v___x_6805_; 
v___x_6800_ = ((size_t)5ULL);
v___x_6801_ = lean_unsigned_to_nat(0u);
v___x_6802_ = lean_unsigned_to_nat(32u);
v___x_6803_ = lean_mk_empty_array_with_capacity(v___x_6802_);
v___x_6804_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0);
v___x_6805_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_6805_, 0, v___x_6804_);
lean_ctor_set(v___x_6805_, 1, v___x_6803_);
lean_ctor_set(v___x_6805_, 2, v___x_6801_);
lean_ctor_set(v___x_6805_, 3, v___x_6801_);
lean_ctor_set_usize(v___x_6805_, 4, v___x_6800_);
return v___x_6805_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2(void){
_start:
{
lean_object* v___x_6806_; lean_object* v___x_6807_; lean_object* v___x_6808_; lean_object* v___x_6809_; 
v___x_6806_ = lean_box(1);
v___x_6807_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1);
v___x_6808_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0);
v___x_6809_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6809_, 0, v___x_6808_);
lean_ctor_set(v___x_6809_, 1, v___x_6807_);
lean_ctor_set(v___x_6809_, 2, v___x_6806_);
return v___x_6809_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_msgData_6810_, lean_object* v___y_6811_, lean_object* v___y_6812_){
_start:
{
lean_object* v___x_6814_; lean_object* v_toCold_6815_; lean_object* v_env_6816_; lean_object* v_options_6817_; lean_object* v___x_6818_; lean_object* v___x_6819_; lean_object* v___x_6820_; lean_object* v___x_6821_; lean_object* v___x_6822_; 
v___x_6814_ = lean_st_ref_get(v___y_6812_);
v_toCold_6815_ = lean_ctor_get(v___y_6811_, 0);
v_env_6816_ = lean_ctor_get(v___x_6814_, 0);
lean_inc_ref(v_env_6816_);
lean_dec(v___x_6814_);
v_options_6817_ = lean_ctor_get(v_toCold_6815_, 2);
v___x_6818_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_6819_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2);
lean_inc_ref(v_options_6817_);
v___x_6820_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6820_, 0, v_env_6816_);
lean_ctor_set(v___x_6820_, 1, v___x_6818_);
lean_ctor_set(v___x_6820_, 2, v___x_6819_);
lean_ctor_set(v___x_6820_, 3, v_options_6817_);
v___x_6821_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_6821_, 0, v___x_6820_);
lean_ctor_set(v___x_6821_, 1, v_msgData_6810_);
v___x_6822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6822_, 0, v___x_6821_);
return v___x_6822_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(lean_object* v_msgData_6823_, lean_object* v___y_6824_, lean_object* v___y_6825_, lean_object* v___y_6826_){
_start:
{
lean_object* v_res_6827_; 
v_res_6827_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5(v_msgData_6823_, v___y_6824_, v___y_6825_);
lean_dec(v___y_6825_);
lean_dec_ref(v___y_6824_);
return v_res_6827_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4(lean_object* v_ref_6828_, lean_object* v_msgData_6829_, uint8_t v_severity_6830_, uint8_t v_isSilent_6831_, lean_object* v___y_6832_, lean_object* v___y_6833_){
_start:
{
lean_object* v___y_6836_; uint8_t v___y_6837_; lean_object* v___y_6838_; lean_object* v___y_6839_; lean_object* v___y_6840_; uint8_t v___y_6841_; lean_object* v___y_6842_; lean_object* v_toCold_6843_; lean_object* v___y_6844_; lean_object* v___y_6873_; lean_object* v___y_6874_; uint8_t v___y_6875_; uint8_t v___y_6876_; lean_object* v___y_6877_; uint8_t v___y_6878_; lean_object* v___y_6879_; lean_object* v___y_6880_; lean_object* v___y_6900_; uint8_t v___y_6901_; lean_object* v___y_6902_; uint8_t v___y_6903_; lean_object* v___y_6904_; uint8_t v___y_6905_; lean_object* v___y_6906_; uint8_t v___y_6910_; uint8_t v___y_6911_; uint8_t v___y_6912_; uint8_t v___x_6923_; uint8_t v___y_6925_; uint8_t v___y_6926_; uint8_t v___y_6927_; uint8_t v___y_6929_; uint8_t v___x_6937_; 
v___x_6923_ = 2;
v___x_6937_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6830_, v___x_6923_);
if (v___x_6937_ == 0)
{
v___y_6929_ = v___x_6937_;
goto v___jp_6928_;
}
else
{
uint8_t v___x_6938_; 
lean_inc_ref(v_msgData_6829_);
v___x_6938_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_6829_);
v___y_6929_ = v___x_6938_;
goto v___jp_6928_;
}
v___jp_6835_:
{
lean_object* v_currNamespace_6845_; lean_object* v_openDecls_6846_; lean_object* v___x_6847_; lean_object* v___x_6848_; lean_object* v___x_6849_; lean_object* v___x_6850_; lean_object* v_env_6851_; lean_object* v_nextMacroScope_6852_; lean_object* v_ngen_6853_; lean_object* v_auxDeclNGen_6854_; lean_object* v_traceState_6855_; lean_object* v_cache_6856_; lean_object* v_recordedDeps_6857_; lean_object* v_messages_6858_; lean_object* v_infoState_6859_; lean_object* v_snapshotTasks_6860_; lean_object* v___x_6862_; uint8_t v_isShared_6863_; uint8_t v_isSharedCheck_6871_; 
v_currNamespace_6845_ = lean_ctor_get(v_toCold_6843_, 4);
v_openDecls_6846_ = lean_ctor_get(v_toCold_6843_, 5);
lean_inc(v_openDecls_6846_);
lean_inc(v_currNamespace_6845_);
v___x_6847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6847_, 0, v_currNamespace_6845_);
lean_ctor_set(v___x_6847_, 1, v_openDecls_6846_);
v___x_6848_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6848_, 0, v___x_6847_);
lean_ctor_set(v___x_6848_, 1, v___y_6838_);
lean_inc_ref(v___y_6839_);
lean_inc_ref(v___y_6840_);
v___x_6849_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_6849_, 0, v___y_6840_);
lean_ctor_set(v___x_6849_, 1, v___y_6836_);
lean_ctor_set(v___x_6849_, 2, v___y_6842_);
lean_ctor_set(v___x_6849_, 3, v___y_6839_);
lean_ctor_set(v___x_6849_, 4, v___x_6848_);
lean_ctor_set_uint8(v___x_6849_, sizeof(void*)*5, v___y_6837_);
lean_ctor_set_uint8(v___x_6849_, sizeof(void*)*5 + 1, v___y_6841_);
lean_ctor_set_uint8(v___x_6849_, sizeof(void*)*5 + 2, v_isSilent_6831_);
v___x_6850_ = lean_st_ref_take(v___y_6844_);
v_env_6851_ = lean_ctor_get(v___x_6850_, 0);
v_nextMacroScope_6852_ = lean_ctor_get(v___x_6850_, 1);
v_ngen_6853_ = lean_ctor_get(v___x_6850_, 2);
v_auxDeclNGen_6854_ = lean_ctor_get(v___x_6850_, 3);
v_traceState_6855_ = lean_ctor_get(v___x_6850_, 4);
v_cache_6856_ = lean_ctor_get(v___x_6850_, 5);
v_recordedDeps_6857_ = lean_ctor_get(v___x_6850_, 6);
v_messages_6858_ = lean_ctor_get(v___x_6850_, 7);
v_infoState_6859_ = lean_ctor_get(v___x_6850_, 8);
v_snapshotTasks_6860_ = lean_ctor_get(v___x_6850_, 9);
v_isSharedCheck_6871_ = !lean_is_exclusive(v___x_6850_);
if (v_isSharedCheck_6871_ == 0)
{
v___x_6862_ = v___x_6850_;
v_isShared_6863_ = v_isSharedCheck_6871_;
goto v_resetjp_6861_;
}
else
{
lean_inc(v_snapshotTasks_6860_);
lean_inc(v_infoState_6859_);
lean_inc(v_messages_6858_);
lean_inc(v_recordedDeps_6857_);
lean_inc(v_cache_6856_);
lean_inc(v_traceState_6855_);
lean_inc(v_auxDeclNGen_6854_);
lean_inc(v_ngen_6853_);
lean_inc(v_nextMacroScope_6852_);
lean_inc(v_env_6851_);
lean_dec(v___x_6850_);
v___x_6862_ = lean_box(0);
v_isShared_6863_ = v_isSharedCheck_6871_;
goto v_resetjp_6861_;
}
v_resetjp_6861_:
{
lean_object* v___x_6864_; lean_object* v___x_6865_; lean_object* v___x_6867_; 
v___x_6864_ = lean_box(0);
v___x_6865_ = l_Lean_MessageLog_add(v___x_6849_, v_messages_6858_);
if (v_isShared_6863_ == 0)
{
lean_ctor_set(v___x_6862_, 7, v___x_6865_);
v___x_6867_ = v___x_6862_;
goto v_reusejp_6866_;
}
else
{
lean_object* v_reuseFailAlloc_6870_; 
v_reuseFailAlloc_6870_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6870_, 0, v_env_6851_);
lean_ctor_set(v_reuseFailAlloc_6870_, 1, v_nextMacroScope_6852_);
lean_ctor_set(v_reuseFailAlloc_6870_, 2, v_ngen_6853_);
lean_ctor_set(v_reuseFailAlloc_6870_, 3, v_auxDeclNGen_6854_);
lean_ctor_set(v_reuseFailAlloc_6870_, 4, v_traceState_6855_);
lean_ctor_set(v_reuseFailAlloc_6870_, 5, v_cache_6856_);
lean_ctor_set(v_reuseFailAlloc_6870_, 6, v_recordedDeps_6857_);
lean_ctor_set(v_reuseFailAlloc_6870_, 7, v___x_6865_);
lean_ctor_set(v_reuseFailAlloc_6870_, 8, v_infoState_6859_);
lean_ctor_set(v_reuseFailAlloc_6870_, 9, v_snapshotTasks_6860_);
v___x_6867_ = v_reuseFailAlloc_6870_;
goto v_reusejp_6866_;
}
v_reusejp_6866_:
{
lean_object* v___x_6868_; lean_object* v___x_6869_; 
v___x_6868_ = lean_st_ref_put(v___y_6844_, v___x_6867_);
v___x_6869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6869_, 0, v___x_6864_);
return v___x_6869_;
}
}
}
v___jp_6872_:
{
lean_object* v_fileName_6881_; lean_object* v_fileMap_6882_; lean_object* v___x_6883_; lean_object* v___x_6884_; lean_object* v_a_6885_; lean_object* v___x_6887_; uint8_t v_isShared_6888_; uint8_t v_isSharedCheck_6898_; 
v_fileName_6881_ = lean_ctor_get(v___y_6879_, 0);
v_fileMap_6882_ = lean_ctor_get(v___y_6879_, 1);
v___x_6883_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_6829_);
v___x_6884_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5(v___x_6883_, v___y_6832_, v___y_6833_);
v_a_6885_ = lean_ctor_get(v___x_6884_, 0);
v_isSharedCheck_6898_ = !lean_is_exclusive(v___x_6884_);
if (v_isSharedCheck_6898_ == 0)
{
v___x_6887_ = v___x_6884_;
v_isShared_6888_ = v_isSharedCheck_6898_;
goto v_resetjp_6886_;
}
else
{
lean_inc(v_a_6885_);
lean_dec(v___x_6884_);
v___x_6887_ = lean_box(0);
v_isShared_6888_ = v_isSharedCheck_6898_;
goto v_resetjp_6886_;
}
v_resetjp_6886_:
{
lean_object* v___x_6889_; lean_object* v___x_6890_; lean_object* v___x_6891_; lean_object* v___x_6892_; 
lean_inc_ref_n(v_fileMap_6882_, 2);
v___x_6889_ = l_Lean_FileMap_toPosition(v_fileMap_6882_, v___y_6877_);
lean_dec(v___y_6877_);
v___x_6890_ = l_Lean_FileMap_toPosition(v_fileMap_6882_, v___y_6880_);
lean_dec(v___y_6880_);
v___x_6891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6891_, 0, v___x_6890_);
v___x_6892_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___closed__0));
if (v___y_6875_ == 0)
{
lean_del_object(v___x_6887_);
lean_dec_ref(v___y_6873_);
v___y_6836_ = v___x_6889_;
v___y_6837_ = v___y_6876_;
v___y_6838_ = v_a_6885_;
v___y_6839_ = v___x_6892_;
v___y_6840_ = v_fileName_6881_;
v___y_6841_ = v___y_6878_;
v___y_6842_ = v___x_6891_;
v_toCold_6843_ = v___y_6874_;
v___y_6844_ = v___y_6833_;
goto v___jp_6835_;
}
else
{
uint8_t v___x_6893_; 
lean_inc(v_a_6885_);
v___x_6893_ = l_Lean_MessageData_hasTag(v___y_6873_, v_a_6885_);
if (v___x_6893_ == 0)
{
lean_object* v___x_6894_; lean_object* v___x_6896_; 
lean_dec_ref_known(v___x_6891_, 1);
lean_dec_ref(v___x_6889_);
lean_dec(v_a_6885_);
v___x_6894_ = lean_box(0);
if (v_isShared_6888_ == 0)
{
lean_ctor_set(v___x_6887_, 0, v___x_6894_);
v___x_6896_ = v___x_6887_;
goto v_reusejp_6895_;
}
else
{
lean_object* v_reuseFailAlloc_6897_; 
v_reuseFailAlloc_6897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6897_, 0, v___x_6894_);
v___x_6896_ = v_reuseFailAlloc_6897_;
goto v_reusejp_6895_;
}
v_reusejp_6895_:
{
return v___x_6896_;
}
}
else
{
lean_del_object(v___x_6887_);
v___y_6836_ = v___x_6889_;
v___y_6837_ = v___y_6876_;
v___y_6838_ = v_a_6885_;
v___y_6839_ = v___x_6892_;
v___y_6840_ = v_fileName_6881_;
v___y_6841_ = v___y_6878_;
v___y_6842_ = v___x_6891_;
v_toCold_6843_ = v___y_6874_;
v___y_6844_ = v___y_6833_;
goto v___jp_6835_;
}
}
}
}
v___jp_6899_:
{
lean_object* v___x_6907_; 
v___x_6907_ = l_Lean_Syntax_getTailPos_x3f(v___y_6904_, v___y_6903_);
lean_dec(v___y_6904_);
if (lean_obj_tag(v___x_6907_) == 0)
{
lean_inc(v___y_6906_);
v___y_6873_ = v___y_6900_;
v___y_6874_ = v___y_6902_;
v___y_6875_ = v___y_6901_;
v___y_6876_ = v___y_6903_;
v___y_6877_ = v___y_6906_;
v___y_6878_ = v___y_6905_;
v___y_6879_ = v___y_6902_;
v___y_6880_ = v___y_6906_;
goto v___jp_6872_;
}
else
{
lean_object* v_val_6908_; 
v_val_6908_ = lean_ctor_get(v___x_6907_, 0);
lean_inc(v_val_6908_);
lean_dec_ref_known(v___x_6907_, 1);
v___y_6873_ = v___y_6900_;
v___y_6874_ = v___y_6902_;
v___y_6875_ = v___y_6901_;
v___y_6876_ = v___y_6903_;
v___y_6877_ = v___y_6906_;
v___y_6878_ = v___y_6905_;
v___y_6879_ = v___y_6902_;
v___y_6880_ = v_val_6908_;
goto v___jp_6872_;
}
}
v___jp_6909_:
{
lean_object* v_toCold_6913_; lean_object* v_ref_6914_; uint8_t v_suppressElabErrors_6915_; lean_object* v___x_6916_; lean_object* v___x_6917_; lean_object* v___f_6918_; lean_object* v_ref_6919_; lean_object* v___x_6920_; 
v_toCold_6913_ = lean_ctor_get(v___y_6832_, 0);
v_ref_6914_ = lean_ctor_get(v___y_6832_, 2);
v_suppressElabErrors_6915_ = lean_ctor_get_uint8(v___y_6832_, sizeof(void*)*3 + 2);
v___x_6916_ = lean_box(v_suppressElabErrors_6915_);
v___x_6917_ = lean_box(v___y_6910_);
v___f_6918_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_6918_, 0, v___x_6916_);
lean_closure_set(v___f_6918_, 1, v___x_6917_);
v_ref_6919_ = l_Lean_replaceRef(v_ref_6828_, v_ref_6914_);
v___x_6920_ = l_Lean_Syntax_getPos_x3f(v_ref_6919_, v___y_6911_);
if (lean_obj_tag(v___x_6920_) == 0)
{
lean_object* v___x_6921_; 
v___x_6921_ = lean_unsigned_to_nat(0u);
v___y_6900_ = v___f_6918_;
v___y_6901_ = v_suppressElabErrors_6915_;
v___y_6902_ = v_toCold_6913_;
v___y_6903_ = v___y_6911_;
v___y_6904_ = v_ref_6919_;
v___y_6905_ = v___y_6912_;
v___y_6906_ = v___x_6921_;
goto v___jp_6899_;
}
else
{
lean_object* v_val_6922_; 
v_val_6922_ = lean_ctor_get(v___x_6920_, 0);
lean_inc(v_val_6922_);
lean_dec_ref_known(v___x_6920_, 1);
v___y_6900_ = v___f_6918_;
v___y_6901_ = v_suppressElabErrors_6915_;
v___y_6902_ = v_toCold_6913_;
v___y_6903_ = v___y_6911_;
v___y_6904_ = v_ref_6919_;
v___y_6905_ = v___y_6912_;
v___y_6906_ = v_val_6922_;
goto v___jp_6899_;
}
}
v___jp_6924_:
{
if (v___y_6927_ == 0)
{
v___y_6910_ = v___y_6925_;
v___y_6911_ = v___y_6926_;
v___y_6912_ = v_severity_6830_;
goto v___jp_6909_;
}
else
{
v___y_6910_ = v___y_6925_;
v___y_6911_ = v___y_6926_;
v___y_6912_ = v___x_6923_;
goto v___jp_6909_;
}
}
v___jp_6928_:
{
if (v___y_6929_ == 0)
{
uint8_t v___x_6930_; uint8_t v___x_6931_; 
v___x_6930_ = 1;
v___x_6931_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6830_, v___x_6930_);
if (v___x_6931_ == 0)
{
v___y_6925_ = v___y_6929_;
v___y_6926_ = v___y_6929_;
v___y_6927_ = v___x_6931_;
goto v___jp_6924_;
}
else
{
lean_object* v___x_6932_; lean_object* v___x_6933_; uint8_t v___x_6934_; 
v___x_6932_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_6832_);
v___x_6933_ = l_Lean_warningAsError;
v___x_6934_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7_spec__9(v___x_6932_, v___x_6933_);
lean_dec_ref(v___x_6932_);
v___y_6925_ = v___y_6929_;
v___y_6926_ = v___y_6929_;
v___y_6927_ = v___x_6934_;
goto v___jp_6924_;
}
}
else
{
lean_object* v___x_6935_; lean_object* v___x_6936_; 
lean_dec_ref(v_msgData_6829_);
v___x_6935_ = lean_box(0);
v___x_6936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6936_, 0, v___x_6935_);
return v___x_6936_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_ref_6939_, lean_object* v_msgData_6940_, lean_object* v_severity_6941_, lean_object* v_isSilent_6942_, lean_object* v___y_6943_, lean_object* v___y_6944_, lean_object* v___y_6945_){
_start:
{
uint8_t v_severity_boxed_6946_; uint8_t v_isSilent_boxed_6947_; lean_object* v_res_6948_; 
v_severity_boxed_6946_ = lean_unbox(v_severity_6941_);
v_isSilent_boxed_6947_ = lean_unbox(v_isSilent_6942_);
v_res_6948_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4(v_ref_6939_, v_msgData_6940_, v_severity_boxed_6946_, v_isSilent_boxed_6947_, v___y_6943_, v___y_6944_);
lean_dec(v___y_6944_);
lean_dec_ref(v___y_6943_);
lean_dec(v_ref_6939_);
return v_res_6948_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2(lean_object* v_msgData_6949_, uint8_t v_severity_6950_, uint8_t v_isSilent_6951_, lean_object* v___y_6952_, lean_object* v___y_6953_){
_start:
{
lean_object* v_ref_6955_; lean_object* v___x_6956_; 
v_ref_6955_ = lean_ctor_get(v___y_6952_, 2);
v___x_6956_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4(v_ref_6955_, v_msgData_6949_, v_severity_6950_, v_isSilent_6951_, v___y_6952_, v___y_6953_);
return v___x_6956_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_6957_, lean_object* v_severity_6958_, lean_object* v_isSilent_6959_, lean_object* v___y_6960_, lean_object* v___y_6961_, lean_object* v___y_6962_){
_start:
{
uint8_t v_severity_boxed_6963_; uint8_t v_isSilent_boxed_6964_; lean_object* v_res_6965_; 
v_severity_boxed_6963_ = lean_unbox(v_severity_6958_);
v_isSilent_boxed_6964_ = lean_unbox(v_isSilent_6959_);
v_res_6965_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2(v_msgData_6957_, v_severity_boxed_6963_, v_isSilent_boxed_6964_, v___y_6960_, v___y_6961_);
lean_dec(v___y_6961_);
lean_dec_ref(v___y_6960_);
return v_res_6965_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0(lean_object* v_msgData_6966_, lean_object* v___y_6967_, lean_object* v___y_6968_){
_start:
{
uint8_t v___x_6970_; uint8_t v___x_6971_; lean_object* v___x_6972_; 
v___x_6970_ = 2;
v___x_6971_ = 0;
v___x_6972_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2(v_msgData_6966_, v___x_6970_, v___x_6971_, v___y_6967_, v___y_6968_);
return v___x_6972_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0___boxed(lean_object* v_msgData_6973_, lean_object* v___y_6974_, lean_object* v___y_6975_, lean_object* v___y_6976_){
_start:
{
lean_object* v_res_6977_; 
v_res_6977_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0(v_msgData_6973_, v___y_6974_, v___y_6975_);
lean_dec(v___y_6975_);
lean_dec_ref(v___y_6974_);
return v_res_6977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0(lean_object* v_f_6978_, lean_object* v___y_6979_, lean_object* v___y_6980_){
_start:
{
lean_object* v_module_6982_; lean_object* v_const_6983_; lean_object* v_exception_6984_; lean_object* v___x_6985_; lean_object* v___x_6986_; lean_object* v___x_6987_; lean_object* v___x_6988_; lean_object* v___x_6989_; lean_object* v___x_6990_; lean_object* v___x_6991_; lean_object* v___x_6992_; lean_object* v___x_6993_; lean_object* v___x_6994_; lean_object* v___x_6995_; lean_object* v___x_6996_; 
v_module_6982_ = lean_ctor_get(v_f_6978_, 0);
lean_inc(v_module_6982_);
v_const_6983_ = lean_ctor_get(v_f_6978_, 1);
lean_inc(v_const_6983_);
v_exception_6984_ = lean_ctor_get(v_f_6978_, 2);
lean_inc_ref(v_exception_6984_);
lean_dec_ref(v_f_6978_);
v___x_6985_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1);
v___x_6986_ = l_Lean_MessageData_ofName(v_const_6983_);
v___x_6987_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6987_, 0, v___x_6985_);
lean_ctor_set(v___x_6987_, 1, v___x_6986_);
v___x_6988_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3);
v___x_6989_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6989_, 0, v___x_6987_);
lean_ctor_set(v___x_6989_, 1, v___x_6988_);
v___x_6990_ = l_Lean_MessageData_ofName(v_module_6982_);
v___x_6991_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6991_, 0, v___x_6989_);
lean_ctor_set(v___x_6991_, 1, v___x_6990_);
v___x_6992_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5);
v___x_6993_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6993_, 0, v___x_6991_);
lean_ctor_set(v___x_6993_, 1, v___x_6992_);
v___x_6994_ = l_Lean_Exception_toMessageData(v_exception_6984_);
v___x_6995_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6995_, 0, v___x_6993_);
lean_ctor_set(v___x_6995_, 1, v___x_6994_);
v___x_6996_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0(v___x_6995_, v___y_6979_, v___y_6980_);
return v___x_6996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0___boxed(lean_object* v_f_6997_, lean_object* v___y_6998_, lean_object* v___y_6999_, lean_object* v___y_7000_){
_start:
{
lean_object* v_res_7001_; 
v_res_7001_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0(v_f_6997_, v___y_6998_, v___y_6999_);
lean_dec(v___y_6999_);
lean_dec_ref(v___y_6998_);
return v_res_7001_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2(lean_object* v_as_7002_, size_t v_i_7003_, size_t v_stop_7004_, lean_object* v_b_7005_, lean_object* v___y_7006_, lean_object* v___y_7007_){
_start:
{
uint8_t v___x_7009_; 
v___x_7009_ = lean_usize_dec_eq(v_i_7003_, v_stop_7004_);
if (v___x_7009_ == 0)
{
lean_object* v___x_7010_; lean_object* v___x_7011_; 
v___x_7010_ = lean_array_uget_borrowed(v_as_7002_, v_i_7003_);
lean_inc(v___x_7010_);
v___x_7011_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0(v___x_7010_, v___y_7006_, v___y_7007_);
if (lean_obj_tag(v___x_7011_) == 0)
{
lean_object* v_a_7012_; size_t v___x_7013_; size_t v___x_7014_; 
v_a_7012_ = lean_ctor_get(v___x_7011_, 0);
lean_inc(v_a_7012_);
lean_dec_ref_known(v___x_7011_, 1);
v___x_7013_ = ((size_t)1ULL);
v___x_7014_ = lean_usize_add(v_i_7003_, v___x_7013_);
v_i_7003_ = v___x_7014_;
v_b_7005_ = v_a_7012_;
goto _start;
}
else
{
return v___x_7011_;
}
}
else
{
lean_object* v___x_7016_; 
v___x_7016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7016_, 0, v_b_7005_);
return v___x_7016_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2___boxed(lean_object* v_as_7017_, lean_object* v_i_7018_, lean_object* v_stop_7019_, lean_object* v_b_7020_, lean_object* v___y_7021_, lean_object* v___y_7022_, lean_object* v___y_7023_){
_start:
{
size_t v_i_boxed_7024_; size_t v_stop_boxed_7025_; lean_object* v_res_7026_; 
v_i_boxed_7024_ = lean_unbox_usize(v_i_7018_);
lean_dec(v_i_7018_);
v_stop_boxed_7025_ = lean_unbox_usize(v_stop_7019_);
lean_dec(v_stop_7019_);
v_res_7026_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2(v_as_7017_, v_i_boxed_7024_, v_stop_boxed_7025_, v_b_7020_, v___y_7021_, v___y_7022_);
lean_dec(v___y_7022_);
lean_dec_ref(v___y_7021_);
lean_dec_ref(v_as_7017_);
return v_res_7026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(lean_object* v_entriesForConst_7027_, lean_object* v_a_7028_, lean_object* v_a_7029_){
_start:
{
lean_object* v___x_7031_; lean_object* v_env_7032_; lean_object* v___x_7033_; lean_object* v_a_7034_; lean_object* v___x_7036_; uint8_t v_isShared_7037_; uint8_t v_isSharedCheck_7067_; 
v___x_7031_ = lean_st_ref_get(v_a_7029_);
v_env_7032_ = lean_ctor_get(v___x_7031_, 0);
lean_inc_ref(v_env_7032_);
lean_dec(v___x_7031_);
v___x_7033_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(v_a_7029_);
v_a_7034_ = lean_ctor_get(v___x_7033_, 0);
v_isSharedCheck_7067_ = !lean_is_exclusive(v___x_7033_);
if (v_isSharedCheck_7067_ == 0)
{
v___x_7036_ = v___x_7033_;
v_isShared_7037_ = v_isSharedCheck_7067_;
goto v_resetjp_7035_;
}
else
{
lean_inc(v_a_7034_);
lean_dec(v___x_7033_);
v___x_7036_ = lean_box(0);
v_isShared_7037_ = v_isSharedCheck_7067_;
goto v_resetjp_7035_;
}
v_resetjp_7035_:
{
lean_object* v___x_7038_; lean_object* v___x_7039_; lean_object* v___y_7046_; lean_object* v___x_7055_; lean_object* v___x_7056_; lean_object* v___x_7057_; uint8_t v___x_7058_; 
v___x_7038_ = l_Lean_Meta_LazyDiscrTree_ImportData_new();
lean_inc_ref(v_a_7028_);
v___x_7039_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(v_a_7028_, v_a_7034_, v_env_7032_, v___x_7038_, v_entriesForConst_7027_);
v___x_7055_ = lean_st_ref_get(v___x_7038_);
lean_dec(v___x_7038_);
v___x_7056_ = lean_unsigned_to_nat(0u);
v___x_7057_ = lean_array_get_size(v___x_7055_);
v___x_7058_ = lean_nat_dec_lt(v___x_7056_, v___x_7057_);
if (v___x_7058_ == 0)
{
lean_dec(v___x_7055_);
goto v___jp_7040_;
}
else
{
lean_object* v___x_7059_; uint8_t v___x_7060_; 
v___x_7059_ = lean_box(0);
v___x_7060_ = lean_nat_dec_le(v___x_7057_, v___x_7057_);
if (v___x_7060_ == 0)
{
if (v___x_7058_ == 0)
{
lean_dec(v___x_7055_);
goto v___jp_7040_;
}
else
{
size_t v___x_7061_; size_t v___x_7062_; lean_object* v___x_7063_; 
v___x_7061_ = ((size_t)0ULL);
v___x_7062_ = lean_usize_of_nat(v___x_7057_);
v___x_7063_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2(v___x_7055_, v___x_7061_, v___x_7062_, v___x_7059_, v_a_7028_, v_a_7029_);
lean_dec(v___x_7055_);
v___y_7046_ = v___x_7063_;
goto v___jp_7045_;
}
}
else
{
size_t v___x_7064_; size_t v___x_7065_; lean_object* v___x_7066_; 
v___x_7064_ = ((size_t)0ULL);
v___x_7065_ = lean_usize_of_nat(v___x_7057_);
v___x_7066_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2(v___x_7055_, v___x_7064_, v___x_7065_, v___x_7059_, v_a_7028_, v_a_7029_);
lean_dec(v___x_7055_);
v___y_7046_ = v___x_7066_;
goto v___jp_7045_;
}
}
v___jp_7040_:
{
lean_object* v___x_7041_; lean_object* v___x_7043_; 
v___x_7041_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v___x_7039_);
if (v_isShared_7037_ == 0)
{
lean_ctor_set(v___x_7036_, 0, v___x_7041_);
v___x_7043_ = v___x_7036_;
goto v_reusejp_7042_;
}
else
{
lean_object* v_reuseFailAlloc_7044_; 
v_reuseFailAlloc_7044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7044_, 0, v___x_7041_);
v___x_7043_ = v_reuseFailAlloc_7044_;
goto v_reusejp_7042_;
}
v_reusejp_7042_:
{
return v___x_7043_;
}
}
v___jp_7045_:
{
if (lean_obj_tag(v___y_7046_) == 0)
{
lean_dec_ref_known(v___y_7046_, 1);
goto v___jp_7040_;
}
else
{
lean_object* v_a_7047_; lean_object* v___x_7049_; uint8_t v_isShared_7050_; uint8_t v_isSharedCheck_7054_; 
lean_dec_ref(v___x_7039_);
lean_del_object(v___x_7036_);
v_a_7047_ = lean_ctor_get(v___y_7046_, 0);
v_isSharedCheck_7054_ = !lean_is_exclusive(v___y_7046_);
if (v_isSharedCheck_7054_ == 0)
{
v___x_7049_ = v___y_7046_;
v_isShared_7050_ = v_isSharedCheck_7054_;
goto v_resetjp_7048_;
}
else
{
lean_inc(v_a_7047_);
lean_dec(v___y_7046_);
v___x_7049_ = lean_box(0);
v_isShared_7050_ = v_isSharedCheck_7054_;
goto v_resetjp_7048_;
}
v_resetjp_7048_:
{
lean_object* v___x_7052_; 
if (v_isShared_7050_ == 0)
{
v___x_7052_ = v___x_7049_;
goto v_reusejp_7051_;
}
else
{
lean_object* v_reuseFailAlloc_7053_; 
v_reuseFailAlloc_7053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7053_, 0, v_a_7047_);
v___x_7052_ = v_reuseFailAlloc_7053_;
goto v_reusejp_7051_;
}
v_reusejp_7051_:
{
return v___x_7052_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg___boxed(lean_object* v_entriesForConst_7068_, lean_object* v_a_7069_, lean_object* v_a_7070_, lean_object* v_a_7071_){
_start:
{
lean_object* v_res_7072_; 
v_res_7072_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(v_entriesForConst_7068_, v_a_7069_, v_a_7070_);
lean_dec(v_a_7070_);
lean_dec_ref(v_a_7069_);
return v_res_7072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree(lean_object* v_00_u03b1_7073_, lean_object* v_entriesForConst_7074_, lean_object* v_a_7075_, lean_object* v_a_7076_){
_start:
{
lean_object* v___x_7078_; 
v___x_7078_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(v_entriesForConst_7074_, v_a_7075_, v_a_7076_);
return v___x_7078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___boxed(lean_object* v_00_u03b1_7079_, lean_object* v_entriesForConst_7080_, lean_object* v_a_7081_, lean_object* v_a_7082_, lean_object* v_a_7083_){
_start:
{
lean_object* v_res_7084_; 
v_res_7084_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree(v_00_u03b1_7079_, v_entriesForConst_7080_, v_a_7081_, v_a_7082_);
lean_dec(v_a_7082_);
lean_dec_ref(v_a_7081_);
return v_res_7084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0(lean_object* v_entriesForConst_7085_, lean_object* v_droppedEntriesRef_7086_, lean_object* v_droppedKeys_7087_, lean_object* v___y_7088_, lean_object* v___y_7089_, lean_object* v___y_7090_, lean_object* v___y_7091_){
_start:
{
lean_object* v_t_7094_; lean_object* v___x_7097_; 
v___x_7097_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(v_entriesForConst_7085_, v___y_7090_, v___y_7091_);
if (lean_obj_tag(v___x_7097_) == 0)
{
if (lean_obj_tag(v_droppedEntriesRef_7086_) == 1)
{
lean_object* v_a_7098_; lean_object* v_val_7099_; lean_object* v___x_7101_; uint8_t v_isShared_7102_; uint8_t v_isSharedCheck_7125_; 
v_a_7098_ = lean_ctor_get(v___x_7097_, 0);
lean_inc(v_a_7098_);
lean_dec_ref_known(v___x_7097_, 1);
v_val_7099_ = lean_ctor_get(v_droppedEntriesRef_7086_, 0);
v_isSharedCheck_7125_ = !lean_is_exclusive(v_droppedEntriesRef_7086_);
if (v_isSharedCheck_7125_ == 0)
{
v___x_7101_ = v_droppedEntriesRef_7086_;
v_isShared_7102_ = v_isSharedCheck_7125_;
goto v_resetjp_7100_;
}
else
{
lean_inc(v_val_7099_);
lean_dec(v_droppedEntriesRef_7086_);
v___x_7101_ = lean_box(0);
v_isShared_7102_ = v_isSharedCheck_7125_;
goto v_resetjp_7100_;
}
v_resetjp_7100_:
{
lean_object* v___x_7103_; 
v___x_7103_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_a_7098_, v_droppedKeys_7087_, v___y_7088_, v___y_7089_, v___y_7090_, v___y_7091_);
lean_dec(v_droppedKeys_7087_);
if (lean_obj_tag(v___x_7103_) == 0)
{
lean_object* v_a_7104_; lean_object* v_fst_7105_; lean_object* v_snd_7106_; lean_object* v___x_7107_; lean_object* v___y_7109_; 
v_a_7104_ = lean_ctor_get(v___x_7103_, 0);
lean_inc(v_a_7104_);
lean_dec_ref_known(v___x_7103_, 1);
v_fst_7105_ = lean_ctor_get(v_a_7104_, 0);
lean_inc(v_fst_7105_);
v_snd_7106_ = lean_ctor_get(v_a_7104_, 1);
lean_inc(v_snd_7106_);
lean_dec(v_a_7104_);
v___x_7107_ = lean_st_ref_get(v_val_7099_);
if (lean_obj_tag(v___x_7107_) == 0)
{
lean_object* v___x_7115_; 
v___x_7115_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___y_7109_ = v___x_7115_;
goto v___jp_7108_;
}
else
{
lean_object* v_val_7116_; 
v_val_7116_ = lean_ctor_get(v___x_7107_, 0);
lean_inc(v_val_7116_);
lean_dec_ref_known(v___x_7107_, 1);
v___y_7109_ = v_val_7116_;
goto v___jp_7108_;
}
v___jp_7108_:
{
lean_object* v___x_7110_; lean_object* v___x_7112_; 
v___x_7110_ = l_Array_append___redArg(v___y_7109_, v_fst_7105_);
lean_dec(v_fst_7105_);
if (v_isShared_7102_ == 0)
{
lean_ctor_set(v___x_7101_, 0, v___x_7110_);
v___x_7112_ = v___x_7101_;
goto v_reusejp_7111_;
}
else
{
lean_object* v_reuseFailAlloc_7114_; 
v_reuseFailAlloc_7114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7114_, 0, v___x_7110_);
v___x_7112_ = v_reuseFailAlloc_7114_;
goto v_reusejp_7111_;
}
v_reusejp_7111_:
{
lean_object* v___x_7113_; 
v___x_7113_ = lean_st_ref_swap(v_val_7099_, v___x_7112_);
lean_dec(v_val_7099_);
lean_dec(v___x_7113_);
v_t_7094_ = v_snd_7106_;
goto v___jp_7093_;
}
}
}
else
{
lean_object* v_a_7117_; lean_object* v___x_7119_; uint8_t v_isShared_7120_; uint8_t v_isSharedCheck_7124_; 
lean_del_object(v___x_7101_);
lean_dec(v_val_7099_);
v_a_7117_ = lean_ctor_get(v___x_7103_, 0);
v_isSharedCheck_7124_ = !lean_is_exclusive(v___x_7103_);
if (v_isSharedCheck_7124_ == 0)
{
v___x_7119_ = v___x_7103_;
v_isShared_7120_ = v_isSharedCheck_7124_;
goto v_resetjp_7118_;
}
else
{
lean_inc(v_a_7117_);
lean_dec(v___x_7103_);
v___x_7119_ = lean_box(0);
v_isShared_7120_ = v_isSharedCheck_7124_;
goto v_resetjp_7118_;
}
v_resetjp_7118_:
{
lean_object* v___x_7122_; 
if (v_isShared_7120_ == 0)
{
v___x_7122_ = v___x_7119_;
goto v_reusejp_7121_;
}
else
{
lean_object* v_reuseFailAlloc_7123_; 
v_reuseFailAlloc_7123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7123_, 0, v_a_7117_);
v___x_7122_ = v_reuseFailAlloc_7123_;
goto v_reusejp_7121_;
}
v_reusejp_7121_:
{
return v___x_7122_;
}
}
}
}
}
else
{
lean_object* v_a_7126_; lean_object* v___x_7127_; 
lean_dec(v_droppedEntriesRef_7086_);
v_a_7126_ = lean_ctor_get(v___x_7097_, 0);
lean_inc(v_a_7126_);
lean_dec_ref_known(v___x_7097_, 1);
v___x_7127_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_a_7126_, v_droppedKeys_7087_, v___y_7088_, v___y_7089_, v___y_7090_, v___y_7091_);
if (lean_obj_tag(v___x_7127_) == 0)
{
lean_object* v_a_7128_; 
v_a_7128_ = lean_ctor_get(v___x_7127_, 0);
lean_inc(v_a_7128_);
lean_dec_ref_known(v___x_7127_, 1);
v_t_7094_ = v_a_7128_;
goto v___jp_7093_;
}
else
{
lean_object* v_a_7129_; lean_object* v___x_7131_; uint8_t v_isShared_7132_; uint8_t v_isSharedCheck_7136_; 
v_a_7129_ = lean_ctor_get(v___x_7127_, 0);
v_isSharedCheck_7136_ = !lean_is_exclusive(v___x_7127_);
if (v_isSharedCheck_7136_ == 0)
{
v___x_7131_ = v___x_7127_;
v_isShared_7132_ = v_isSharedCheck_7136_;
goto v_resetjp_7130_;
}
else
{
lean_inc(v_a_7129_);
lean_dec(v___x_7127_);
v___x_7131_ = lean_box(0);
v_isShared_7132_ = v_isSharedCheck_7136_;
goto v_resetjp_7130_;
}
v_resetjp_7130_:
{
lean_object* v___x_7134_; 
if (v_isShared_7132_ == 0)
{
v___x_7134_ = v___x_7131_;
goto v_reusejp_7133_;
}
else
{
lean_object* v_reuseFailAlloc_7135_; 
v_reuseFailAlloc_7135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7135_, 0, v_a_7129_);
v___x_7134_ = v_reuseFailAlloc_7135_;
goto v_reusejp_7133_;
}
v_reusejp_7133_:
{
return v___x_7134_;
}
}
}
}
}
else
{
lean_object* v_a_7137_; lean_object* v___x_7139_; uint8_t v_isShared_7140_; uint8_t v_isSharedCheck_7144_; 
lean_dec(v_droppedKeys_7087_);
lean_dec(v_droppedEntriesRef_7086_);
v_a_7137_ = lean_ctor_get(v___x_7097_, 0);
v_isSharedCheck_7144_ = !lean_is_exclusive(v___x_7097_);
if (v_isSharedCheck_7144_ == 0)
{
v___x_7139_ = v___x_7097_;
v_isShared_7140_ = v_isSharedCheck_7144_;
goto v_resetjp_7138_;
}
else
{
lean_inc(v_a_7137_);
lean_dec(v___x_7097_);
v___x_7139_ = lean_box(0);
v_isShared_7140_ = v_isSharedCheck_7144_;
goto v_resetjp_7138_;
}
v_resetjp_7138_:
{
lean_object* v___x_7142_; 
if (v_isShared_7140_ == 0)
{
v___x_7142_ = v___x_7139_;
goto v_reusejp_7141_;
}
else
{
lean_object* v_reuseFailAlloc_7143_; 
v_reuseFailAlloc_7143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7143_, 0, v_a_7137_);
v___x_7142_ = v_reuseFailAlloc_7143_;
goto v_reusejp_7141_;
}
v_reusejp_7141_:
{
return v___x_7142_;
}
}
}
v___jp_7093_:
{
lean_object* v___x_7095_; lean_object* v___x_7096_; 
v___x_7095_ = lean_st_mk_ref(v_t_7094_);
v___x_7096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7096_, 0, v___x_7095_);
return v___x_7096_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0___boxed(lean_object* v_entriesForConst_7145_, lean_object* v_droppedEntriesRef_7146_, lean_object* v_droppedKeys_7147_, lean_object* v___y_7148_, lean_object* v___y_7149_, lean_object* v___y_7150_, lean_object* v___y_7151_, lean_object* v___y_7152_){
_start:
{
lean_object* v_res_7153_; 
v_res_7153_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0(v_entriesForConst_7145_, v_droppedEntriesRef_7146_, v_droppedKeys_7147_, v___y_7148_, v___y_7149_, v___y_7150_, v___y_7151_);
lean_dec(v___y_7151_);
lean_dec_ref(v___y_7150_);
lean_dec(v___y_7149_);
lean_dec_ref(v___y_7148_);
return v_res_7153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(lean_object* v_entriesForConst_7155_, lean_object* v_droppedKeys_7156_, lean_object* v_droppedEntriesRef_7157_, lean_object* v_a_7158_, lean_object* v_a_7159_, lean_object* v_a_7160_, lean_object* v_a_7161_){
_start:
{
lean_object* v___f_7163_; lean_object* v___x_7164_; lean_object* v___x_7165_; lean_object* v___x_7166_; lean_object* v___x_7167_; 
v___f_7163_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_7163_, 0, v_entriesForConst_7155_);
lean_closure_set(v___f_7163_, 1, v_droppedEntriesRef_7157_);
lean_closure_set(v___f_7163_, 2, v_droppedKeys_7156_);
v___x_7164_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_7160_);
v___x_7165_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___closed__0));
v___x_7166_ = lean_box(0);
v___x_7167_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v___x_7165_, v___x_7164_, v___f_7163_, v___x_7166_, v_a_7158_, v_a_7159_, v_a_7160_, v_a_7161_);
lean_dec_ref(v___x_7164_);
return v___x_7167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___boxed(lean_object* v_entriesForConst_7168_, lean_object* v_droppedKeys_7169_, lean_object* v_droppedEntriesRef_7170_, lean_object* v_a_7171_, lean_object* v_a_7172_, lean_object* v_a_7173_, lean_object* v_a_7174_, lean_object* v_a_7175_){
_start:
{
lean_object* v_res_7176_; 
v_res_7176_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v_entriesForConst_7168_, v_droppedKeys_7169_, v_droppedEntriesRef_7170_, v_a_7171_, v_a_7172_, v_a_7173_, v_a_7174_);
lean_dec(v_a_7174_);
lean_dec_ref(v_a_7173_);
lean_dec(v_a_7172_);
lean_dec_ref(v_a_7171_);
return v_res_7176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef(lean_object* v_00_u03b1_7177_, lean_object* v_entriesForConst_7178_, lean_object* v_droppedKeys_7179_, lean_object* v_droppedEntriesRef_7180_, lean_object* v_a_7181_, lean_object* v_a_7182_, lean_object* v_a_7183_, lean_object* v_a_7184_){
_start:
{
lean_object* v___x_7186_; 
v___x_7186_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v_entriesForConst_7178_, v_droppedKeys_7179_, v_droppedEntriesRef_7180_, v_a_7181_, v_a_7182_, v_a_7183_, v_a_7184_);
return v___x_7186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___boxed(lean_object* v_00_u03b1_7187_, lean_object* v_entriesForConst_7188_, lean_object* v_droppedKeys_7189_, lean_object* v_droppedEntriesRef_7190_, lean_object* v_a_7191_, lean_object* v_a_7192_, lean_object* v_a_7193_, lean_object* v_a_7194_, lean_object* v_a_7195_){
_start:
{
lean_object* v_res_7196_; 
v_res_7196_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef(v_00_u03b1_7187_, v_entriesForConst_7188_, v_droppedKeys_7189_, v_droppedEntriesRef_7190_, v_a_7191_, v_a_7192_, v_a_7193_, v_a_7194_);
lean_dec(v_a_7194_);
lean_dec_ref(v_a_7193_);
lean_dec(v_a_7192_);
lean_dec_ref(v_a_7191_);
return v_res_7196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0(lean_object* v_moduleRef_7197_, lean_object* v_ty_7198_, lean_object* v___y_7199_, lean_object* v___y_7200_, lean_object* v___y_7201_, lean_object* v___y_7202_){
_start:
{
lean_object* v___x_7204_; lean_object* v___x_7205_; 
v___x_7204_ = lean_st_ref_get(v_moduleRef_7197_);
v___x_7205_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v___x_7204_, v_ty_7198_, v___y_7199_, v___y_7200_, v___y_7201_, v___y_7202_);
if (lean_obj_tag(v___x_7205_) == 0)
{
lean_object* v_a_7206_; lean_object* v___x_7208_; uint8_t v_isShared_7209_; uint8_t v_isSharedCheck_7216_; 
v_a_7206_ = lean_ctor_get(v___x_7205_, 0);
v_isSharedCheck_7216_ = !lean_is_exclusive(v___x_7205_);
if (v_isSharedCheck_7216_ == 0)
{
v___x_7208_ = v___x_7205_;
v_isShared_7209_ = v_isSharedCheck_7216_;
goto v_resetjp_7207_;
}
else
{
lean_inc(v_a_7206_);
lean_dec(v___x_7205_);
v___x_7208_ = lean_box(0);
v_isShared_7209_ = v_isSharedCheck_7216_;
goto v_resetjp_7207_;
}
v_resetjp_7207_:
{
lean_object* v_fst_7210_; lean_object* v_snd_7211_; lean_object* v___x_7212_; lean_object* v___x_7214_; 
v_fst_7210_ = lean_ctor_get(v_a_7206_, 0);
lean_inc(v_fst_7210_);
v_snd_7211_ = lean_ctor_get(v_a_7206_, 1);
lean_inc(v_snd_7211_);
lean_dec(v_a_7206_);
v___x_7212_ = lean_st_ref_swap(v_moduleRef_7197_, v_snd_7211_);
lean_dec(v___x_7212_);
if (v_isShared_7209_ == 0)
{
lean_ctor_set(v___x_7208_, 0, v_fst_7210_);
v___x_7214_ = v___x_7208_;
goto v_reusejp_7213_;
}
else
{
lean_object* v_reuseFailAlloc_7215_; 
v_reuseFailAlloc_7215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7215_, 0, v_fst_7210_);
v___x_7214_ = v_reuseFailAlloc_7215_;
goto v_reusejp_7213_;
}
v_reusejp_7213_:
{
return v___x_7214_;
}
}
}
else
{
lean_object* v_a_7217_; lean_object* v___x_7219_; uint8_t v_isShared_7220_; uint8_t v_isSharedCheck_7224_; 
v_a_7217_ = lean_ctor_get(v___x_7205_, 0);
v_isSharedCheck_7224_ = !lean_is_exclusive(v___x_7205_);
if (v_isSharedCheck_7224_ == 0)
{
v___x_7219_ = v___x_7205_;
v_isShared_7220_ = v_isSharedCheck_7224_;
goto v_resetjp_7218_;
}
else
{
lean_inc(v_a_7217_);
lean_dec(v___x_7205_);
v___x_7219_ = lean_box(0);
v_isShared_7220_ = v_isSharedCheck_7224_;
goto v_resetjp_7218_;
}
v_resetjp_7218_:
{
lean_object* v___x_7222_; 
if (v_isShared_7220_ == 0)
{
v___x_7222_ = v___x_7219_;
goto v_reusejp_7221_;
}
else
{
lean_object* v_reuseFailAlloc_7223_; 
v_reuseFailAlloc_7223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7223_, 0, v_a_7217_);
v___x_7222_ = v_reuseFailAlloc_7223_;
goto v_reusejp_7221_;
}
v_reusejp_7221_:
{
return v___x_7222_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0___boxed(lean_object* v_moduleRef_7225_, lean_object* v_ty_7226_, lean_object* v___y_7227_, lean_object* v___y_7228_, lean_object* v___y_7229_, lean_object* v___y_7230_, lean_object* v___y_7231_){
_start:
{
lean_object* v_res_7232_; 
v_res_7232_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0(v_moduleRef_7225_, v_ty_7226_, v___y_7227_, v___y_7228_, v___y_7229_, v___y_7230_);
lean_dec(v___y_7230_);
lean_dec_ref(v___y_7229_);
lean_dec(v___y_7228_);
lean_dec_ref(v___y_7227_);
lean_dec(v_moduleRef_7225_);
return v_res_7232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(lean_object* v_moduleRef_7234_, lean_object* v_ty_7235_, lean_object* v_a_7236_, lean_object* v_a_7237_, lean_object* v_a_7238_, lean_object* v_a_7239_){
_start:
{
lean_object* v___f_7241_; lean_object* v___x_7242_; lean_object* v___x_7243_; lean_object* v___x_7244_; lean_object* v___x_7245_; 
v___f_7241_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_7241_, 0, v_moduleRef_7234_);
lean_closure_set(v___f_7241_, 1, v_ty_7235_);
v___x_7242_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_7238_);
v___x_7243_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___closed__0));
v___x_7244_ = lean_box(0);
v___x_7245_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v___x_7243_, v___x_7242_, v___f_7241_, v___x_7244_, v_a_7236_, v_a_7237_, v_a_7238_, v_a_7239_);
lean_dec_ref(v___x_7242_);
return v___x_7245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___boxed(lean_object* v_moduleRef_7246_, lean_object* v_ty_7247_, lean_object* v_a_7248_, lean_object* v_a_7249_, lean_object* v_a_7250_, lean_object* v_a_7251_, lean_object* v_a_7252_){
_start:
{
lean_object* v_res_7253_; 
v_res_7253_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(v_moduleRef_7246_, v_ty_7247_, v_a_7248_, v_a_7249_, v_a_7250_, v_a_7251_);
lean_dec(v_a_7251_);
lean_dec_ref(v_a_7250_);
lean_dec(v_a_7249_);
lean_dec_ref(v_a_7248_);
return v_res_7253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches(lean_object* v_00_u03b1_7254_, lean_object* v_moduleRef_7255_, lean_object* v_ty_7256_, lean_object* v_a_7257_, lean_object* v_a_7258_, lean_object* v_a_7259_, lean_object* v_a_7260_){
_start:
{
lean_object* v___x_7262_; 
v___x_7262_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(v_moduleRef_7255_, v_ty_7256_, v_a_7257_, v_a_7258_, v_a_7259_, v_a_7260_);
return v___x_7262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___boxed(lean_object* v_00_u03b1_7263_, lean_object* v_moduleRef_7264_, lean_object* v_ty_7265_, lean_object* v_a_7266_, lean_object* v_a_7267_, lean_object* v_a_7268_, lean_object* v_a_7269_, lean_object* v_a_7270_){
_start:
{
lean_object* v_res_7271_; 
v_res_7271_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches(v_00_u03b1_7263_, v_moduleRef_7264_, v_ty_7265_, v_a_7266_, v_a_7267_, v_a_7268_, v_a_7269_);
lean_dec(v_a_7269_);
lean_dec_ref(v_a_7268_);
lean_dec(v_a_7267_);
lean_dec_ref(v_a_7266_);
return v_res_7271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(lean_object* v_adjustResult_7272_, lean_object* v_j_7273_, size_t v_sz_7274_, size_t v_i_7275_, lean_object* v_bs_7276_){
_start:
{
uint8_t v___x_7277_; 
v___x_7277_ = lean_usize_dec_lt(v_i_7275_, v_sz_7274_);
if (v___x_7277_ == 0)
{
lean_dec(v_j_7273_);
lean_dec(v_adjustResult_7272_);
return v_bs_7276_;
}
else
{
lean_object* v_v_7278_; lean_object* v___x_7279_; lean_object* v_bs_x27_7280_; lean_object* v___x_7281_; size_t v___x_7282_; size_t v___x_7283_; lean_object* v___x_7284_; 
v_v_7278_ = lean_array_uget(v_bs_7276_, v_i_7275_);
v___x_7279_ = lean_unsigned_to_nat(0u);
v_bs_x27_7280_ = lean_array_uset(v_bs_7276_, v_i_7275_, v___x_7279_);
lean_inc(v_adjustResult_7272_);
lean_inc(v_j_7273_);
v___x_7281_ = lean_apply_2(v_adjustResult_7272_, v_j_7273_, v_v_7278_);
v___x_7282_ = ((size_t)1ULL);
v___x_7283_ = lean_usize_add(v_i_7275_, v___x_7282_);
v___x_7284_ = lean_array_uset(v_bs_x27_7280_, v_i_7275_, v___x_7281_);
v_i_7275_ = v___x_7283_;
v_bs_7276_ = v___x_7284_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg___boxed(lean_object* v_adjustResult_7286_, lean_object* v_j_7287_, lean_object* v_sz_7288_, lean_object* v_i_7289_, lean_object* v_bs_7290_){
_start:
{
size_t v_sz_boxed_7291_; size_t v_i_boxed_7292_; lean_object* v_res_7293_; 
v_sz_boxed_7291_ = lean_unbox_usize(v_sz_7288_);
lean_dec(v_sz_7288_);
v_i_boxed_7292_ = lean_unbox_usize(v_i_7289_);
lean_dec(v_i_7289_);
v_res_7293_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(v_adjustResult_7286_, v_j_7287_, v_sz_boxed_7291_, v_i_boxed_7292_, v_bs_7290_);
return v_res_7293_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(lean_object* v_adjustResult_7294_, lean_object* v_j_7295_, lean_object* v_as_7296_, size_t v_i_7297_, size_t v_stop_7298_, lean_object* v_b_7299_){
_start:
{
uint8_t v___x_7300_; 
v___x_7300_ = lean_usize_dec_eq(v_i_7297_, v_stop_7298_);
if (v___x_7300_ == 0)
{
lean_object* v___x_7301_; size_t v_sz_7302_; size_t v___x_7303_; lean_object* v___x_7304_; lean_object* v___x_7305_; size_t v___x_7306_; size_t v___x_7307_; 
v___x_7301_ = lean_array_uget_borrowed(v_as_7296_, v_i_7297_);
v_sz_7302_ = lean_array_size(v___x_7301_);
v___x_7303_ = ((size_t)0ULL);
lean_inc(v___x_7301_);
lean_inc(v_j_7295_);
lean_inc(v_adjustResult_7294_);
v___x_7304_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(v_adjustResult_7294_, v_j_7295_, v_sz_7302_, v___x_7303_, v___x_7301_);
v___x_7305_ = l_Array_append___redArg(v_b_7299_, v___x_7304_);
lean_dec_ref(v___x_7304_);
v___x_7306_ = ((size_t)1ULL);
v___x_7307_ = lean_usize_add(v_i_7297_, v___x_7306_);
v_i_7297_ = v___x_7307_;
v_b_7299_ = v___x_7305_;
goto _start;
}
else
{
lean_dec(v_j_7295_);
lean_dec(v_adjustResult_7294_);
return v_b_7299_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg___boxed(lean_object* v_adjustResult_7309_, lean_object* v_j_7310_, lean_object* v_as_7311_, lean_object* v_i_7312_, lean_object* v_stop_7313_, lean_object* v_b_7314_){
_start:
{
size_t v_i_boxed_7315_; size_t v_stop_boxed_7316_; lean_object* v_res_7317_; 
v_i_boxed_7315_ = lean_unbox_usize(v_i_7312_);
lean_dec(v_i_7312_);
v_stop_boxed_7316_ = lean_unbox_usize(v_stop_7313_);
lean_dec(v_stop_7313_);
v_res_7317_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7309_, v_j_7310_, v_as_7311_, v_i_boxed_7315_, v_stop_boxed_7316_, v_b_7314_);
lean_dec_ref(v_as_7311_);
return v_res_7317_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(lean_object* v_n_7318_, lean_object* v_aa_7319_, lean_object* v_adjustResult_7320_, lean_object* v_n_7321_, lean_object* v_j_7322_, lean_object* v_a_7323_){
_start:
{
lean_object* v_zero_7324_; uint8_t v_isZero_7325_; 
v_zero_7324_ = lean_unsigned_to_nat(0u);
v_isZero_7325_ = lean_nat_dec_eq(v_j_7322_, v_zero_7324_);
if (v_isZero_7325_ == 1)
{
lean_dec(v_j_7322_);
lean_dec(v_adjustResult_7320_);
return v_a_7323_;
}
else
{
lean_object* v_one_7326_; lean_object* v_n_7327_; lean_object* v___x_7328_; lean_object* v___x_7329_; lean_object* v_j_7330_; lean_object* v_b_7331_; lean_object* v___x_7332_; uint8_t v___x_7333_; 
v_one_7326_ = lean_unsigned_to_nat(1u);
v_n_7327_ = lean_nat_sub(v_j_7322_, v_one_7326_);
v___x_7328_ = lean_nat_sub(v_n_7321_, v_j_7322_);
lean_dec(v_j_7322_);
v___x_7329_ = lean_nat_sub(v_n_7318_, v_one_7326_);
v_j_7330_ = lean_nat_sub(v___x_7329_, v___x_7328_);
lean_dec(v___x_7328_);
lean_dec(v___x_7329_);
v_b_7331_ = lean_array_fget_borrowed(v_aa_7319_, v_j_7330_);
v___x_7332_ = lean_array_get_size(v_b_7331_);
v___x_7333_ = lean_nat_dec_lt(v_zero_7324_, v___x_7332_);
if (v___x_7333_ == 0)
{
lean_dec(v_j_7330_);
v_j_7322_ = v_n_7327_;
goto _start;
}
else
{
size_t v___x_7335_; size_t v___x_7336_; lean_object* v___x_7337_; 
v___x_7335_ = ((size_t)0ULL);
v___x_7336_ = lean_usize_of_nat(v___x_7332_);
lean_inc(v_adjustResult_7320_);
v___x_7337_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7320_, v_j_7330_, v_b_7331_, v___x_7335_, v___x_7336_, v_a_7323_);
v_j_7322_ = v_n_7327_;
v_a_7323_ = v___x_7337_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_n_7339_, lean_object* v_aa_7340_, lean_object* v_adjustResult_7341_, lean_object* v_n_7342_, lean_object* v_j_7343_, lean_object* v_a_7344_){
_start:
{
lean_object* v_res_7345_; 
v_res_7345_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7339_, v_aa_7340_, v_adjustResult_7341_, v_n_7342_, v_j_7343_, v_a_7344_);
lean_dec(v_n_7342_);
lean_dec_ref(v_aa_7340_);
lean_dec(v_n_7339_);
return v_res_7345_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(lean_object* v_n_7346_, lean_object* v_adjustResult_7347_, lean_object* v_aa_7348_, lean_object* v_n_7349_, lean_object* v_j_7350_, lean_object* v_a_7351_){
_start:
{
lean_object* v_zero_7352_; uint8_t v_isZero_7353_; 
v_zero_7352_ = lean_unsigned_to_nat(0u);
v_isZero_7353_ = lean_nat_dec_eq(v_j_7350_, v_zero_7352_);
if (v_isZero_7353_ == 1)
{
lean_dec(v_adjustResult_7347_);
return v_a_7351_;
}
else
{
lean_object* v_one_7354_; lean_object* v_n_7355_; lean_object* v___x_7356_; lean_object* v___x_7357_; lean_object* v_j_7358_; lean_object* v_b_7359_; lean_object* v___x_7360_; uint8_t v___x_7361_; 
v_one_7354_ = lean_unsigned_to_nat(1u);
v_n_7355_ = lean_nat_sub(v_j_7350_, v_one_7354_);
v___x_7356_ = lean_nat_sub(v_n_7349_, v_j_7350_);
v___x_7357_ = lean_nat_sub(v_n_7346_, v_one_7354_);
v_j_7358_ = lean_nat_sub(v___x_7357_, v___x_7356_);
lean_dec(v___x_7356_);
lean_dec(v___x_7357_);
v_b_7359_ = lean_array_fget_borrowed(v_aa_7348_, v_j_7358_);
v___x_7360_ = lean_array_get_size(v_b_7359_);
v___x_7361_ = lean_nat_dec_lt(v_zero_7352_, v___x_7360_);
if (v___x_7361_ == 0)
{
lean_object* v___x_7362_; 
lean_dec(v_j_7358_);
v___x_7362_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7346_, v_aa_7348_, v_adjustResult_7347_, v_n_7349_, v_n_7355_, v_a_7351_);
return v___x_7362_;
}
else
{
size_t v___x_7363_; size_t v___x_7364_; lean_object* v___x_7365_; lean_object* v___x_7366_; 
v___x_7363_ = ((size_t)0ULL);
v___x_7364_ = lean_usize_of_nat(v___x_7360_);
lean_inc(v_adjustResult_7347_);
v___x_7365_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7347_, v_j_7358_, v_b_7359_, v___x_7363_, v___x_7364_, v_a_7351_);
v___x_7366_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7346_, v_aa_7348_, v_adjustResult_7347_, v_n_7349_, v_n_7355_, v___x_7365_);
return v___x_7366_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg___boxed(lean_object* v_n_7367_, lean_object* v_adjustResult_7368_, lean_object* v_aa_7369_, lean_object* v_n_7370_, lean_object* v_j_7371_, lean_object* v_a_7372_){
_start:
{
lean_object* v_res_7373_; 
v_res_7373_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(v_n_7367_, v_adjustResult_7368_, v_aa_7369_, v_n_7370_, v_j_7371_, v_a_7372_);
lean_dec(v_j_7371_);
lean_dec(v_n_7370_);
lean_dec_ref(v_aa_7369_);
lean_dec(v_n_7367_);
return v_res_7373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(lean_object* v_adjustResult_7374_, lean_object* v_mr_7375_, lean_object* v_a_7376_){
_start:
{
lean_object* v_n_7377_; lean_object* v___x_7378_; 
v_n_7377_ = lean_array_get_size(v_mr_7375_);
v___x_7378_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(v_n_7377_, v_adjustResult_7374_, v_mr_7375_, v_n_7377_, v_n_7377_, v_a_7376_);
return v___x_7378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg___boxed(lean_object* v_adjustResult_7379_, lean_object* v_mr_7380_, lean_object* v_a_7381_){
_start:
{
lean_object* v_res_7382_; 
v_res_7382_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7379_, v_mr_7380_, v_a_7381_);
lean_dec_ref(v_mr_7380_);
return v_res_7382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(lean_object* v_moduleTreeRef_7383_, lean_object* v_ref_7384_, lean_object* v_addEntry_7385_, lean_object* v_droppedKeys_7386_, lean_object* v_constantsPerTask_7387_, lean_object* v_droppedEntriesRef_7388_, lean_object* v_adjustResult_7389_, lean_object* v_ty_7390_, lean_object* v_a_7391_, lean_object* v_a_7392_, lean_object* v_a_7393_, lean_object* v_a_7394_){
_start:
{
lean_object* v___x_7396_; 
lean_inc_ref(v_ty_7390_);
v___x_7396_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(v_moduleTreeRef_7383_, v_ty_7390_, v_a_7391_, v_a_7392_, v_a_7393_, v_a_7394_);
if (lean_obj_tag(v___x_7396_) == 0)
{
lean_object* v_a_7397_; lean_object* v___x_7398_; 
v_a_7397_ = lean_ctor_get(v___x_7396_, 0);
lean_inc(v_a_7397_);
lean_dec_ref_known(v___x_7396_, 1);
v___x_7398_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(v_ref_7384_, v_addEntry_7385_, v_droppedKeys_7386_, v_constantsPerTask_7387_, v_droppedEntriesRef_7388_, v_ty_7390_, v_a_7391_, v_a_7392_, v_a_7393_, v_a_7394_);
if (lean_obj_tag(v___x_7398_) == 0)
{
lean_object* v_a_7399_; lean_object* v___x_7401_; uint8_t v_isShared_7402_; uint8_t v_isSharedCheck_7412_; 
v_a_7399_ = lean_ctor_get(v___x_7398_, 0);
v_isSharedCheck_7412_ = !lean_is_exclusive(v___x_7398_);
if (v_isSharedCheck_7412_ == 0)
{
v___x_7401_ = v___x_7398_;
v_isShared_7402_ = v_isSharedCheck_7412_;
goto v_resetjp_7400_;
}
else
{
lean_inc(v_a_7399_);
lean_dec(v___x_7398_);
v___x_7401_ = lean_box(0);
v_isShared_7402_ = v_isSharedCheck_7412_;
goto v_resetjp_7400_;
}
v_resetjp_7400_:
{
lean_object* v___x_7403_; lean_object* v___x_7404_; lean_object* v___x_7405_; lean_object* v___x_7406_; lean_object* v___x_7407_; lean_object* v___x_7408_; lean_object* v___x_7410_; 
v___x_7403_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_a_7397_);
v___x_7404_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_a_7399_);
v___x_7405_ = lean_nat_add(v___x_7403_, v___x_7404_);
lean_dec(v___x_7404_);
lean_dec(v___x_7403_);
v___x_7406_ = lean_mk_empty_array_with_capacity(v___x_7405_);
lean_dec(v___x_7405_);
lean_inc(v_adjustResult_7389_);
v___x_7407_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7389_, v_a_7397_, v___x_7406_);
lean_dec(v_a_7397_);
v___x_7408_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7389_, v_a_7399_, v___x_7407_);
lean_dec(v_a_7399_);
if (v_isShared_7402_ == 0)
{
lean_ctor_set(v___x_7401_, 0, v___x_7408_);
v___x_7410_ = v___x_7401_;
goto v_reusejp_7409_;
}
else
{
lean_object* v_reuseFailAlloc_7411_; 
v_reuseFailAlloc_7411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7411_, 0, v___x_7408_);
v___x_7410_ = v_reuseFailAlloc_7411_;
goto v_reusejp_7409_;
}
v_reusejp_7409_:
{
return v___x_7410_;
}
}
}
else
{
lean_object* v_a_7413_; lean_object* v___x_7415_; uint8_t v_isShared_7416_; uint8_t v_isSharedCheck_7420_; 
lean_dec(v_a_7397_);
lean_dec(v_adjustResult_7389_);
v_a_7413_ = lean_ctor_get(v___x_7398_, 0);
v_isSharedCheck_7420_ = !lean_is_exclusive(v___x_7398_);
if (v_isSharedCheck_7420_ == 0)
{
v___x_7415_ = v___x_7398_;
v_isShared_7416_ = v_isSharedCheck_7420_;
goto v_resetjp_7414_;
}
else
{
lean_inc(v_a_7413_);
lean_dec(v___x_7398_);
v___x_7415_ = lean_box(0);
v_isShared_7416_ = v_isSharedCheck_7420_;
goto v_resetjp_7414_;
}
v_resetjp_7414_:
{
lean_object* v___x_7418_; 
if (v_isShared_7416_ == 0)
{
v___x_7418_ = v___x_7415_;
goto v_reusejp_7417_;
}
else
{
lean_object* v_reuseFailAlloc_7419_; 
v_reuseFailAlloc_7419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7419_, 0, v_a_7413_);
v___x_7418_ = v_reuseFailAlloc_7419_;
goto v_reusejp_7417_;
}
v_reusejp_7417_:
{
return v___x_7418_;
}
}
}
}
else
{
lean_object* v_a_7421_; lean_object* v___x_7423_; uint8_t v_isShared_7424_; uint8_t v_isSharedCheck_7428_; 
lean_dec_ref(v_ty_7390_);
lean_dec(v_adjustResult_7389_);
lean_dec(v_droppedEntriesRef_7388_);
lean_dec(v_constantsPerTask_7387_);
lean_dec(v_droppedKeys_7386_);
lean_dec_ref(v_addEntry_7385_);
v_a_7421_ = lean_ctor_get(v___x_7396_, 0);
v_isSharedCheck_7428_ = !lean_is_exclusive(v___x_7396_);
if (v_isSharedCheck_7428_ == 0)
{
v___x_7423_ = v___x_7396_;
v_isShared_7424_ = v_isSharedCheck_7428_;
goto v_resetjp_7422_;
}
else
{
lean_inc(v_a_7421_);
lean_dec(v___x_7396_);
v___x_7423_ = lean_box(0);
v_isShared_7424_ = v_isSharedCheck_7428_;
goto v_resetjp_7422_;
}
v_resetjp_7422_:
{
lean_object* v___x_7426_; 
if (v_isShared_7424_ == 0)
{
v___x_7426_ = v___x_7423_;
goto v_reusejp_7425_;
}
else
{
lean_object* v_reuseFailAlloc_7427_; 
v_reuseFailAlloc_7427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7427_, 0, v_a_7421_);
v___x_7426_ = v_reuseFailAlloc_7427_;
goto v_reusejp_7425_;
}
v_reusejp_7425_:
{
return v___x_7426_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg___boxed(lean_object* v_moduleTreeRef_7429_, lean_object* v_ref_7430_, lean_object* v_addEntry_7431_, lean_object* v_droppedKeys_7432_, lean_object* v_constantsPerTask_7433_, lean_object* v_droppedEntriesRef_7434_, lean_object* v_adjustResult_7435_, lean_object* v_ty_7436_, lean_object* v_a_7437_, lean_object* v_a_7438_, lean_object* v_a_7439_, lean_object* v_a_7440_, lean_object* v_a_7441_){
_start:
{
lean_object* v_res_7442_; 
v_res_7442_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_moduleTreeRef_7429_, v_ref_7430_, v_addEntry_7431_, v_droppedKeys_7432_, v_constantsPerTask_7433_, v_droppedEntriesRef_7434_, v_adjustResult_7435_, v_ty_7436_, v_a_7437_, v_a_7438_, v_a_7439_, v_a_7440_);
lean_dec(v_a_7440_);
lean_dec_ref(v_a_7439_);
lean_dec(v_a_7438_);
lean_dec_ref(v_a_7437_);
lean_dec(v_ref_7430_);
return v_res_7442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt(lean_object* v_00_u03b1_7443_, lean_object* v_00_u03b2_7444_, lean_object* v_moduleTreeRef_7445_, lean_object* v_ref_7446_, lean_object* v_addEntry_7447_, lean_object* v_droppedKeys_7448_, lean_object* v_constantsPerTask_7449_, lean_object* v_droppedEntriesRef_7450_, lean_object* v_adjustResult_7451_, lean_object* v_ty_7452_, lean_object* v_a_7453_, lean_object* v_a_7454_, lean_object* v_a_7455_, lean_object* v_a_7456_){
_start:
{
lean_object* v___x_7458_; 
v___x_7458_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_moduleTreeRef_7445_, v_ref_7446_, v_addEntry_7447_, v_droppedKeys_7448_, v_constantsPerTask_7449_, v_droppedEntriesRef_7450_, v_adjustResult_7451_, v_ty_7452_, v_a_7453_, v_a_7454_, v_a_7455_, v_a_7456_);
return v___x_7458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___boxed(lean_object* v_00_u03b1_7459_, lean_object* v_00_u03b2_7460_, lean_object* v_moduleTreeRef_7461_, lean_object* v_ref_7462_, lean_object* v_addEntry_7463_, lean_object* v_droppedKeys_7464_, lean_object* v_constantsPerTask_7465_, lean_object* v_droppedEntriesRef_7466_, lean_object* v_adjustResult_7467_, lean_object* v_ty_7468_, lean_object* v_a_7469_, lean_object* v_a_7470_, lean_object* v_a_7471_, lean_object* v_a_7472_, lean_object* v_a_7473_){
_start:
{
lean_object* v_res_7474_; 
v_res_7474_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt(v_00_u03b1_7459_, v_00_u03b2_7460_, v_moduleTreeRef_7461_, v_ref_7462_, v_addEntry_7463_, v_droppedKeys_7464_, v_constantsPerTask_7465_, v_droppedEntriesRef_7466_, v_adjustResult_7467_, v_ty_7468_, v_a_7469_, v_a_7470_, v_a_7471_, v_a_7472_);
lean_dec(v_a_7472_);
lean_dec_ref(v_a_7471_);
lean_dec(v_a_7470_);
lean_dec_ref(v_a_7469_);
lean_dec(v_ref_7462_);
return v_res_7474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0(lean_object* v_00_u03b1_7475_, lean_object* v_00_u03b2_7476_, lean_object* v_adjustResult_7477_, lean_object* v_mr_7478_, lean_object* v_a_7479_){
_start:
{
lean_object* v___x_7480_; 
v___x_7480_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7477_, v_mr_7478_, v_a_7479_);
return v___x_7480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___boxed(lean_object* v_00_u03b1_7481_, lean_object* v_00_u03b2_7482_, lean_object* v_adjustResult_7483_, lean_object* v_mr_7484_, lean_object* v_a_7485_){
_start:
{
lean_object* v_res_7486_; 
v_res_7486_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0(v_00_u03b1_7481_, v_00_u03b2_7482_, v_adjustResult_7483_, v_mr_7484_, v_a_7485_);
lean_dec_ref(v_mr_7484_);
return v_res_7486_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0(lean_object* v_00_u03b1_7487_, lean_object* v_00_u03b2_7488_, lean_object* v_adjustResult_7489_, lean_object* v_j_7490_, size_t v_sz_7491_, size_t v_i_7492_, lean_object* v_bs_7493_){
_start:
{
lean_object* v___x_7494_; 
v___x_7494_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(v_adjustResult_7489_, v_j_7490_, v_sz_7491_, v_i_7492_, v_bs_7493_);
return v___x_7494_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___boxed(lean_object* v_00_u03b1_7495_, lean_object* v_00_u03b2_7496_, lean_object* v_adjustResult_7497_, lean_object* v_j_7498_, lean_object* v_sz_7499_, lean_object* v_i_7500_, lean_object* v_bs_7501_){
_start:
{
size_t v_sz_boxed_7502_; size_t v_i_boxed_7503_; lean_object* v_res_7504_; 
v_sz_boxed_7502_ = lean_unbox_usize(v_sz_7499_);
lean_dec(v_sz_7499_);
v_i_boxed_7503_ = lean_unbox_usize(v_i_7500_);
lean_dec(v_i_7500_);
v_res_7504_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0(v_00_u03b1_7495_, v_00_u03b2_7496_, v_adjustResult_7497_, v_j_7498_, v_sz_boxed_7502_, v_i_boxed_7503_, v_bs_7501_);
return v_res_7504_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1(lean_object* v_00_u03b1_7505_, lean_object* v_00_u03b2_7506_, lean_object* v_adjustResult_7507_, lean_object* v_j_7508_, lean_object* v_as_7509_, size_t v_i_7510_, size_t v_stop_7511_, lean_object* v_b_7512_){
_start:
{
lean_object* v___x_7513_; 
v___x_7513_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7507_, v_j_7508_, v_as_7509_, v_i_7510_, v_stop_7511_, v_b_7512_);
return v___x_7513_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___boxed(lean_object* v_00_u03b1_7514_, lean_object* v_00_u03b2_7515_, lean_object* v_adjustResult_7516_, lean_object* v_j_7517_, lean_object* v_as_7518_, lean_object* v_i_7519_, lean_object* v_stop_7520_, lean_object* v_b_7521_){
_start:
{
size_t v_i_boxed_7522_; size_t v_stop_boxed_7523_; lean_object* v_res_7524_; 
v_i_boxed_7522_ = lean_unbox_usize(v_i_7519_);
lean_dec(v_i_7519_);
v_stop_boxed_7523_ = lean_unbox_usize(v_stop_7520_);
lean_dec(v_stop_7520_);
v_res_7524_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1(v_00_u03b1_7514_, v_00_u03b2_7515_, v_adjustResult_7516_, v_j_7517_, v_as_7518_, v_i_boxed_7522_, v_stop_boxed_7523_, v_b_7521_);
lean_dec_ref(v_as_7518_);
return v_res_7524_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2(lean_object* v_00_u03b2_7525_, lean_object* v_n_7526_, lean_object* v_00_u03b1_7527_, lean_object* v_adjustResult_7528_, lean_object* v_aa_7529_, lean_object* v_n_7530_, lean_object* v_j_7531_, lean_object* v_a_7532_, lean_object* v_a_7533_){
_start:
{
lean_object* v___x_7534_; 
v___x_7534_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(v_n_7526_, v_adjustResult_7528_, v_aa_7529_, v_n_7530_, v_j_7531_, v_a_7533_);
return v___x_7534_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___boxed(lean_object* v_00_u03b2_7535_, lean_object* v_n_7536_, lean_object* v_00_u03b1_7537_, lean_object* v_adjustResult_7538_, lean_object* v_aa_7539_, lean_object* v_n_7540_, lean_object* v_j_7541_, lean_object* v_a_7542_, lean_object* v_a_7543_){
_start:
{
lean_object* v_res_7544_; 
v_res_7544_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2(v_00_u03b2_7535_, v_n_7536_, v_00_u03b1_7537_, v_adjustResult_7538_, v_aa_7539_, v_n_7540_, v_j_7541_, v_a_7542_, v_a_7543_);
lean_dec(v_j_7541_);
lean_dec(v_n_7540_);
lean_dec_ref(v_aa_7539_);
lean_dec(v_n_7536_);
return v_res_7544_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_7545_, lean_object* v_n_7546_, lean_object* v_00_u03b1_7547_, lean_object* v_aa_7548_, lean_object* v_adjustResult_7549_, lean_object* v_n_7550_, lean_object* v_j_7551_, lean_object* v_a_7552_, lean_object* v_a_7553_){
_start:
{
lean_object* v___x_7554_; 
v___x_7554_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7546_, v_aa_7548_, v_adjustResult_7549_, v_n_7550_, v_j_7551_, v_a_7553_);
return v___x_7554_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b2_7555_, lean_object* v_n_7556_, lean_object* v_00_u03b1_7557_, lean_object* v_aa_7558_, lean_object* v_adjustResult_7559_, lean_object* v_n_7560_, lean_object* v_j_7561_, lean_object* v_a_7562_, lean_object* v_a_7563_){
_start:
{
lean_object* v_res_7564_; 
v_res_7564_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3(v_00_u03b2_7555_, v_n_7556_, v_00_u03b1_7557_, v_aa_7558_, v_adjustResult_7559_, v_n_7560_, v_j_7561_, v_a_7562_, v_a_7563_);
lean_dec(v_n_7560_);
lean_dec_ref(v_aa_7558_);
lean_dec(v_n_7556_);
return v_res_7564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg___lam__0(lean_object* v_x_7565_, lean_object* v_v_7566_){
_start:
{
lean_inc(v_v_7566_);
return v_v_7566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg___lam__0___boxed(lean_object* v_x_7567_, lean_object* v_v_7568_){
_start:
{
lean_object* v_res_7569_; 
v_res_7569_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg___lam__0(v_x_7567_, v_v_7568_);
lean_dec(v_v_7568_);
lean_dec(v_x_7567_);
return v_res_7569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg(lean_object* v_ref_7571_, lean_object* v_addEntry_7572_, lean_object* v_droppedKeys_7573_, lean_object* v_constantsPerTask_7574_, lean_object* v_droppedEntriesRef_7575_, lean_object* v_ty_7576_, lean_object* v_a_7577_, lean_object* v_a_7578_, lean_object* v_a_7579_, lean_object* v_a_7580_){
_start:
{
lean_object* v___f_7582_; lean_object* v___x_7583_; 
v___f_7582_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_findMatches___redArg___closed__0));
lean_inc(v_droppedEntriesRef_7575_);
lean_inc(v_droppedKeys_7573_);
lean_inc_ref(v_addEntry_7572_);
v___x_7583_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v_addEntry_7572_, v_droppedKeys_7573_, v_droppedEntriesRef_7575_, v_a_7577_, v_a_7578_, v_a_7579_, v_a_7580_);
if (lean_obj_tag(v___x_7583_) == 0)
{
lean_object* v_a_7584_; lean_object* v___x_7585_; 
v_a_7584_ = lean_ctor_get(v___x_7583_, 0);
lean_inc(v_a_7584_);
lean_dec_ref_known(v___x_7583_, 1);
v___x_7585_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_a_7584_, v_ref_7571_, v_addEntry_7572_, v_droppedKeys_7573_, v_constantsPerTask_7574_, v_droppedEntriesRef_7575_, v___f_7582_, v_ty_7576_, v_a_7577_, v_a_7578_, v_a_7579_, v_a_7580_);
return v___x_7585_;
}
else
{
lean_object* v_a_7586_; lean_object* v___x_7588_; uint8_t v_isShared_7589_; uint8_t v_isSharedCheck_7593_; 
lean_dec_ref(v_ty_7576_);
lean_dec(v_droppedEntriesRef_7575_);
lean_dec(v_constantsPerTask_7574_);
lean_dec(v_droppedKeys_7573_);
lean_dec_ref(v_addEntry_7572_);
v_a_7586_ = lean_ctor_get(v___x_7583_, 0);
v_isSharedCheck_7593_ = !lean_is_exclusive(v___x_7583_);
if (v_isSharedCheck_7593_ == 0)
{
v___x_7588_ = v___x_7583_;
v_isShared_7589_ = v_isSharedCheck_7593_;
goto v_resetjp_7587_;
}
else
{
lean_inc(v_a_7586_);
lean_dec(v___x_7583_);
v___x_7588_ = lean_box(0);
v_isShared_7589_ = v_isSharedCheck_7593_;
goto v_resetjp_7587_;
}
v_resetjp_7587_:
{
lean_object* v___x_7591_; 
if (v_isShared_7589_ == 0)
{
v___x_7591_ = v___x_7588_;
goto v_reusejp_7590_;
}
else
{
lean_object* v_reuseFailAlloc_7592_; 
v_reuseFailAlloc_7592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7592_, 0, v_a_7586_);
v___x_7591_ = v_reuseFailAlloc_7592_;
goto v_reusejp_7590_;
}
v_reusejp_7590_:
{
return v___x_7591_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg___boxed(lean_object* v_ref_7594_, lean_object* v_addEntry_7595_, lean_object* v_droppedKeys_7596_, lean_object* v_constantsPerTask_7597_, lean_object* v_droppedEntriesRef_7598_, lean_object* v_ty_7599_, lean_object* v_a_7600_, lean_object* v_a_7601_, lean_object* v_a_7602_, lean_object* v_a_7603_, lean_object* v_a_7604_){
_start:
{
lean_object* v_res_7605_; 
v_res_7605_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg(v_ref_7594_, v_addEntry_7595_, v_droppedKeys_7596_, v_constantsPerTask_7597_, v_droppedEntriesRef_7598_, v_ty_7599_, v_a_7600_, v_a_7601_, v_a_7602_, v_a_7603_);
lean_dec(v_a_7603_);
lean_dec_ref(v_a_7602_);
lean_dec(v_a_7601_);
lean_dec_ref(v_a_7600_);
lean_dec(v_ref_7594_);
return v_res_7605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches(lean_object* v_00_u03b1_7606_, lean_object* v_ref_7607_, lean_object* v_addEntry_7608_, lean_object* v_droppedKeys_7609_, lean_object* v_constantsPerTask_7610_, lean_object* v_droppedEntriesRef_7611_, lean_object* v_ty_7612_, lean_object* v_a_7613_, lean_object* v_a_7614_, lean_object* v_a_7615_, lean_object* v_a_7616_){
_start:
{
lean_object* v___x_7618_; 
v___x_7618_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg(v_ref_7607_, v_addEntry_7608_, v_droppedKeys_7609_, v_constantsPerTask_7610_, v_droppedEntriesRef_7611_, v_ty_7612_, v_a_7613_, v_a_7614_, v_a_7615_, v_a_7616_);
return v___x_7618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___boxed(lean_object* v_00_u03b1_7619_, lean_object* v_ref_7620_, lean_object* v_addEntry_7621_, lean_object* v_droppedKeys_7622_, lean_object* v_constantsPerTask_7623_, lean_object* v_droppedEntriesRef_7624_, lean_object* v_ty_7625_, lean_object* v_a_7626_, lean_object* v_a_7627_, lean_object* v_a_7628_, lean_object* v_a_7629_, lean_object* v_a_7630_){
_start:
{
lean_object* v_res_7631_; 
v_res_7631_ = l_Lean_Meta_LazyDiscrTree_findMatches(v_00_u03b1_7619_, v_ref_7620_, v_addEntry_7621_, v_droppedKeys_7622_, v_constantsPerTask_7623_, v_droppedEntriesRef_7624_, v_ty_7625_, v_a_7626_, v_a_7627_, v_a_7628_, v_a_7629_);
lean_dec(v_a_7629_);
lean_dec_ref(v_a_7628_);
lean_dec(v_a_7627_);
lean_dec_ref(v_a_7626_);
lean_dec(v_ref_7620_);
return v_res_7631_;
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
