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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_Meta_Config_toConfigWithKey(lean_object*);
extern lean_object* l_Lean_Options_empty;
extern lean_object* l_Lean_NameSet_empty;
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint16_t lean_uint16_land(uint16_t, uint16_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
lean_object* l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(lean_object*);
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
lean_object* lean_obj_tag_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_ctorIdx___impl___boxed(lean_object*);
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
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13;
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
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_Meta_LazyDiscrTree_Key_ctorIdx___impl(v_x_3_);
lean_dec(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
switch(lean_obj_tag(v_t_5_))
{
case 0:
{
lean_object* v_a_7_; lean_object* v_a_8_; lean_object* v___x_9_; 
v_a_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_a_7_);
v_a_8_ = lean_ctor_get(v_t_5_, 1);
lean_inc(v_a_8_);
lean_dec_ref_known(v_t_5_, 2);
v___x_9_ = lean_apply_2(v_k_6_, v_a_7_, v_a_8_);
return v___x_9_;
}
case 1:
{
lean_object* v_a_10_; lean_object* v_a_11_; lean_object* v___x_12_; 
v_a_10_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_a_10_);
v_a_11_ = lean_ctor_get(v_t_5_, 1);
lean_inc(v_a_11_);
lean_dec_ref_known(v_t_5_, 2);
v___x_12_ = lean_apply_2(v_k_6_, v_a_10_, v_a_11_);
return v___x_12_;
}
case 2:
{
lean_object* v_a_13_; lean_object* v___x_14_; 
v_a_13_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_a_13_);
lean_dec_ref_known(v_t_5_, 1);
v___x_14_ = lean_apply_1(v_k_6_, v_a_13_);
return v___x_14_;
}
case 6:
{
lean_object* v_a_15_; lean_object* v_a_16_; lean_object* v_a_17_; lean_object* v___x_18_; 
v_a_15_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_a_15_);
v_a_16_ = lean_ctor_get(v_t_5_, 1);
lean_inc(v_a_16_);
v_a_17_ = lean_ctor_get(v_t_5_, 2);
lean_inc(v_a_17_);
lean_dec_ref_known(v_t_5_, 3);
v___x_18_ = lean_apply_3(v_k_6_, v_a_15_, v_a_16_, v_a_17_);
return v___x_18_;
}
default: 
{
lean_dec(v_t_5_);
return v_k_6_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_ctorElim(lean_object* v_motive_19_, lean_object* v_ctorIdx_20_, lean_object* v_t_21_, lean_object* v_h_22_, lean_object* v_k_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Lean_Meta_LazyDiscrTree_Key_ctorElim___redArg(v_t_21_, v_k_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_ctorElim___boxed(lean_object* v_motive_25_, lean_object* v_ctorIdx_26_, lean_object* v_t_27_, lean_object* v_h_28_, lean_object* v_k_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Meta_LazyDiscrTree_Key_ctorElim(v_motive_25_, v_ctorIdx_26_, v_t_27_, v_h_28_, v_k_29_);
lean_dec(v_ctorIdx_26_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_const_elim___redArg(lean_object* v_t_31_, lean_object* v_const_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lean_Meta_LazyDiscrTree_Key_ctorElim___redArg(v_t_31_, v_const_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_const_elim(lean_object* v_motive_34_, lean_object* v_t_35_, lean_object* v_h_36_, lean_object* v_const_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Lean_Meta_LazyDiscrTree_Key_ctorElim___redArg(v_t_35_, v_const_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_fvar_elim___redArg(lean_object* v_t_39_, lean_object* v_fvar_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_Meta_LazyDiscrTree_Key_ctorElim___redArg(v_t_39_, v_fvar_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_fvar_elim(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_fvar_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = l_Lean_Meta_LazyDiscrTree_Key_ctorElim___redArg(v_t_43_, v_fvar_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_lit_elim___redArg(lean_object* v_t_47_, lean_object* v_lit_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l_Lean_Meta_LazyDiscrTree_Key_ctorElim___redArg(v_t_47_, v_lit_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_lit_elim(lean_object* v_motive_50_, lean_object* v_t_51_, lean_object* v_h_52_, lean_object* v_lit_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = l_Lean_Meta_LazyDiscrTree_Key_ctorElim___redArg(v_t_51_, v_lit_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_star_elim___redArg(lean_object* v_t_55_, lean_object* v_star_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l_Lean_Meta_LazyDiscrTree_Key_ctorElim___redArg(v_t_55_, v_star_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_star_elim(lean_object* v_motive_58_, lean_object* v_t_59_, lean_object* v_h_60_, lean_object* v_star_61_){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = l_Lean_Meta_LazyDiscrTree_Key_ctorElim___redArg(v_t_59_, v_star_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_other_elim___redArg(lean_object* v_t_63_, lean_object* v_other_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l_Lean_Meta_LazyDiscrTree_Key_ctorElim___redArg(v_t_63_, v_other_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_other_elim(lean_object* v_motive_66_, lean_object* v_t_67_, lean_object* v_h_68_, lean_object* v_other_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l_Lean_Meta_LazyDiscrTree_Key_ctorElim___redArg(v_t_67_, v_other_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_arrow_elim___redArg(lean_object* v_t_71_, lean_object* v_arrow_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l_Lean_Meta_LazyDiscrTree_Key_ctorElim___redArg(v_t_71_, v_arrow_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_arrow_elim(lean_object* v_motive_74_, lean_object* v_t_75_, lean_object* v_h_76_, lean_object* v_arrow_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = l_Lean_Meta_LazyDiscrTree_Key_ctorElim___redArg(v_t_75_, v_arrow_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_proj_elim___redArg(lean_object* v_t_79_, lean_object* v_proj_80_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = l_Lean_Meta_LazyDiscrTree_Key_ctorElim___redArg(v_t_79_, v_proj_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_proj_elim(lean_object* v_motive_82_, lean_object* v_t_83_, lean_object* v_h_84_, lean_object* v_proj_85_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = l_Lean_Meta_LazyDiscrTree_Key_ctorElim___redArg(v_t_83_, v_proj_85_);
return v___x_86_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(lean_object* v_x_92_, lean_object* v_x_93_){
_start:
{
switch(lean_obj_tag(v_x_92_))
{
case 0:
{
if (lean_obj_tag(v_x_93_) == 0)
{
lean_object* v_a_94_; lean_object* v_a_95_; lean_object* v_a_96_; lean_object* v_a_97_; uint8_t v___x_98_; 
v_a_94_ = lean_ctor_get(v_x_92_, 0);
v_a_95_ = lean_ctor_get(v_x_92_, 1);
v_a_96_ = lean_ctor_get(v_x_93_, 0);
v_a_97_ = lean_ctor_get(v_x_93_, 1);
v___x_98_ = lean_name_eq(v_a_94_, v_a_96_);
if (v___x_98_ == 0)
{
return v___x_98_;
}
else
{
uint8_t v___x_99_; 
v___x_99_ = lean_nat_dec_eq(v_a_95_, v_a_97_);
return v___x_99_;
}
}
else
{
uint8_t v___x_100_; 
v___x_100_ = 0;
return v___x_100_;
}
}
case 1:
{
if (lean_obj_tag(v_x_93_) == 1)
{
lean_object* v_a_101_; lean_object* v_a_102_; lean_object* v_a_103_; lean_object* v_a_104_; uint8_t v___x_105_; 
v_a_101_ = lean_ctor_get(v_x_92_, 0);
v_a_102_ = lean_ctor_get(v_x_92_, 1);
v_a_103_ = lean_ctor_get(v_x_93_, 0);
v_a_104_ = lean_ctor_get(v_x_93_, 1);
v___x_105_ = l_Lean_instBEqFVarId_beq(v_a_101_, v_a_103_);
if (v___x_105_ == 0)
{
return v___x_105_;
}
else
{
uint8_t v___x_106_; 
v___x_106_ = lean_nat_dec_eq(v_a_102_, v_a_104_);
return v___x_106_;
}
}
else
{
uint8_t v___x_107_; 
v___x_107_ = 0;
return v___x_107_;
}
}
case 2:
{
if (lean_obj_tag(v_x_93_) == 2)
{
lean_object* v_a_108_; lean_object* v_a_109_; uint8_t v___x_110_; 
v_a_108_ = lean_ctor_get(v_x_92_, 0);
v_a_109_ = lean_ctor_get(v_x_93_, 0);
v___x_110_ = l_Lean_instBEqLiteral_beq(v_a_108_, v_a_109_);
return v___x_110_;
}
else
{
uint8_t v___x_111_; 
v___x_111_ = 0;
return v___x_111_;
}
}
case 3:
{
if (lean_obj_tag(v_x_93_) == 3)
{
uint8_t v___x_112_; 
v___x_112_ = 1;
return v___x_112_;
}
else
{
uint8_t v___x_113_; 
v___x_113_ = 0;
return v___x_113_;
}
}
case 4:
{
if (lean_obj_tag(v_x_93_) == 4)
{
uint8_t v___x_114_; 
v___x_114_ = 1;
return v___x_114_;
}
else
{
uint8_t v___x_115_; 
v___x_115_ = 0;
return v___x_115_;
}
}
case 5:
{
if (lean_obj_tag(v_x_93_) == 5)
{
uint8_t v___x_116_; 
v___x_116_ = 1;
return v___x_116_;
}
else
{
uint8_t v___x_117_; 
v___x_117_ = 0;
return v___x_117_;
}
}
default: 
{
if (lean_obj_tag(v_x_93_) == 6)
{
lean_object* v_a_118_; lean_object* v_a_119_; lean_object* v_a_120_; lean_object* v_a_121_; lean_object* v_a_122_; lean_object* v_a_123_; uint8_t v___x_124_; 
v_a_118_ = lean_ctor_get(v_x_92_, 0);
v_a_119_ = lean_ctor_get(v_x_92_, 1);
v_a_120_ = lean_ctor_get(v_x_92_, 2);
v_a_121_ = lean_ctor_get(v_x_93_, 0);
v_a_122_ = lean_ctor_get(v_x_93_, 1);
v_a_123_ = lean_ctor_get(v_x_93_, 2);
v___x_124_ = lean_name_eq(v_a_118_, v_a_121_);
if (v___x_124_ == 0)
{
return v___x_124_;
}
else
{
uint8_t v___x_125_; 
v___x_125_ = lean_nat_dec_eq(v_a_119_, v_a_122_);
if (v___x_125_ == 0)
{
return v___x_125_;
}
else
{
uint8_t v___x_126_; 
v___x_126_ = lean_nat_dec_eq(v_a_120_, v_a_123_);
return v___x_126_;
}
}
}
else
{
uint8_t v___x_127_; 
v___x_127_ = 0;
return v___x_127_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instBEqKey_beq___boxed(lean_object* v_x_128_, lean_object* v_x_129_){
_start:
{
uint8_t v_res_130_; lean_object* v_r_131_; 
v_res_130_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_x_128_, v_x_129_);
lean_dec(v_x_129_);
lean_dec(v_x_128_);
v_r_131_ = lean_box(v_res_130_);
return v_r_131_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__9(void){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_149_ = lean_unsigned_to_nat(2u);
v___x_150_ = lean_nat_to_int(v___x_149_);
return v___x_150_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__10(void){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_151_ = lean_unsigned_to_nat(1u);
v___x_152_ = lean_nat_to_int(v___x_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instReprKey_repr(lean_object* v_x_171_, lean_object* v_prec_172_){
_start:
{
lean_object* v___y_174_; lean_object* v___y_181_; lean_object* v___y_188_; 
switch(lean_obj_tag(v_x_171_))
{
case 0:
{
lean_object* v_a_194_; lean_object* v_a_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_220_; 
v_a_194_ = lean_ctor_get(v_x_171_, 0);
v_a_195_ = lean_ctor_get(v_x_171_, 1);
v_isSharedCheck_220_ = !lean_is_exclusive(v_x_171_);
if (v_isSharedCheck_220_ == 0)
{
v___x_197_ = v_x_171_;
v_isShared_198_ = v_isSharedCheck_220_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_a_195_);
lean_inc(v_a_194_);
lean_dec(v_x_171_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_220_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___y_200_; lean_object* v___x_216_; uint8_t v___x_217_; 
v___x_216_ = lean_unsigned_to_nat(1024u);
v___x_217_ = lean_nat_dec_le(v___x_216_, v_prec_172_);
if (v___x_217_ == 0)
{
lean_object* v___x_218_; 
v___x_218_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__9, &l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__9_once, _init_l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__9);
v___y_200_ = v___x_218_;
goto v___jp_199_;
}
else
{
lean_object* v___x_219_; 
v___x_219_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__10, &l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__10_once, _init_l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__10);
v___y_200_ = v___x_219_;
goto v___jp_199_;
}
v___jp_199_:
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_206_; 
v___x_201_ = lean_box(1);
v___x_202_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__8));
v___x_203_ = lean_unsigned_to_nat(1024u);
v___x_204_ = l_Lean_Name_reprPrec(v_a_194_, v___x_203_);
if (v_isShared_198_ == 0)
{
lean_ctor_set_tag(v___x_197_, 5);
lean_ctor_set(v___x_197_, 1, v___x_204_);
lean_ctor_set(v___x_197_, 0, v___x_202_);
v___x_206_ = v___x_197_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v___x_202_);
lean_ctor_set(v_reuseFailAlloc_215_, 1, v___x_204_);
v___x_206_ = v_reuseFailAlloc_215_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; uint8_t v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_207_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
lean_ctor_set(v___x_207_, 1, v___x_201_);
v___x_208_ = l_Nat_reprFast(v_a_195_);
v___x_209_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_209_, 0, v___x_208_);
v___x_210_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_210_, 0, v___x_207_);
lean_ctor_set(v___x_210_, 1, v___x_209_);
lean_inc(v___y_200_);
v___x_211_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_211_, 0, v___y_200_);
lean_ctor_set(v___x_211_, 1, v___x_210_);
v___x_212_ = 0;
v___x_213_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_213_, 0, v___x_211_);
lean_ctor_set_uint8(v___x_213_, sizeof(void*)*1, v___x_212_);
v___x_214_ = l_Repr_addAppParen(v___x_213_, v_prec_172_);
return v___x_214_;
}
}
}
}
case 1:
{
lean_object* v_a_221_; lean_object* v_a_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_247_; 
v_a_221_ = lean_ctor_get(v_x_171_, 0);
v_a_222_ = lean_ctor_get(v_x_171_, 1);
v_isSharedCheck_247_ = !lean_is_exclusive(v_x_171_);
if (v_isSharedCheck_247_ == 0)
{
v___x_224_ = v_x_171_;
v_isShared_225_ = v_isSharedCheck_247_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_a_222_);
lean_inc(v_a_221_);
lean_dec(v_x_171_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_247_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___y_227_; lean_object* v___x_243_; uint8_t v___x_244_; 
v___x_243_ = lean_unsigned_to_nat(1024u);
v___x_244_ = lean_nat_dec_le(v___x_243_, v_prec_172_);
if (v___x_244_ == 0)
{
lean_object* v___x_245_; 
v___x_245_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__9, &l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__9_once, _init_l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__9);
v___y_227_ = v___x_245_;
goto v___jp_226_;
}
else
{
lean_object* v___x_246_; 
v___x_246_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__10, &l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__10_once, _init_l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__10);
v___y_227_ = v___x_246_;
goto v___jp_226_;
}
v___jp_226_:
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_233_; 
v___x_228_ = lean_box(1);
v___x_229_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__13));
v___x_230_ = lean_unsigned_to_nat(1024u);
v___x_231_ = l_Lean_Name_reprPrec(v_a_221_, v___x_230_);
if (v_isShared_225_ == 0)
{
lean_ctor_set_tag(v___x_224_, 5);
lean_ctor_set(v___x_224_, 1, v___x_231_);
lean_ctor_set(v___x_224_, 0, v___x_229_);
v___x_233_ = v___x_224_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_229_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v___x_231_);
v___x_233_ = v_reuseFailAlloc_242_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; uint8_t v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_234_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
lean_ctor_set(v___x_234_, 1, v___x_228_);
v___x_235_ = l_Nat_reprFast(v_a_222_);
v___x_236_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
v___x_237_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_234_);
lean_ctor_set(v___x_237_, 1, v___x_236_);
lean_inc(v___y_227_);
v___x_238_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_238_, 0, v___y_227_);
lean_ctor_set(v___x_238_, 1, v___x_237_);
v___x_239_ = 0;
v___x_240_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_240_, 0, v___x_238_);
lean_ctor_set_uint8(v___x_240_, sizeof(void*)*1, v___x_239_);
v___x_241_ = l_Repr_addAppParen(v___x_240_, v_prec_172_);
return v___x_241_;
}
}
}
}
case 2:
{
lean_object* v_a_248_; lean_object* v___y_250_; lean_object* v___x_259_; uint8_t v___x_260_; 
v_a_248_ = lean_ctor_get(v_x_171_, 0);
lean_inc_ref(v_a_248_);
lean_dec_ref_known(v_x_171_, 1);
v___x_259_ = lean_unsigned_to_nat(1024u);
v___x_260_ = lean_nat_dec_le(v___x_259_, v_prec_172_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; 
v___x_261_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__9, &l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__9_once, _init_l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__9);
v___y_250_ = v___x_261_;
goto v___jp_249_;
}
else
{
lean_object* v___x_262_; 
v___x_262_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__10, &l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__10_once, _init_l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__10);
v___y_250_ = v___x_262_;
goto v___jp_249_;
}
v___jp_249_:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; uint8_t v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_251_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__16));
v___x_252_ = lean_unsigned_to_nat(1024u);
v___x_253_ = l_Lean_instReprLiteral_repr(v_a_248_, v___x_252_);
v___x_254_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_251_);
lean_ctor_set(v___x_254_, 1, v___x_253_);
lean_inc(v___y_250_);
v___x_255_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_255_, 0, v___y_250_);
lean_ctor_set(v___x_255_, 1, v___x_254_);
v___x_256_ = 0;
v___x_257_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_257_, 0, v___x_255_);
lean_ctor_set_uint8(v___x_257_, sizeof(void*)*1, v___x_256_);
v___x_258_ = l_Repr_addAppParen(v___x_257_, v_prec_172_);
return v___x_258_;
}
}
case 3:
{
lean_object* v___x_263_; uint8_t v___x_264_; 
v___x_263_ = lean_unsigned_to_nat(1024u);
v___x_264_ = lean_nat_dec_le(v___x_263_, v_prec_172_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; 
v___x_265_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__9, &l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__9_once, _init_l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__9);
v___y_188_ = v___x_265_;
goto v___jp_187_;
}
else
{
lean_object* v___x_266_; 
v___x_266_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__10, &l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__10_once, _init_l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__10);
v___y_188_ = v___x_266_;
goto v___jp_187_;
}
}
case 4:
{
lean_object* v___x_267_; uint8_t v___x_268_; 
v___x_267_ = lean_unsigned_to_nat(1024u);
v___x_268_ = lean_nat_dec_le(v___x_267_, v_prec_172_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; 
v___x_269_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__9, &l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__9_once, _init_l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__9);
v___y_181_ = v___x_269_;
goto v___jp_180_;
}
else
{
lean_object* v___x_270_; 
v___x_270_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__10, &l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__10_once, _init_l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__10);
v___y_181_ = v___x_270_;
goto v___jp_180_;
}
}
case 5:
{
lean_object* v___x_271_; uint8_t v___x_272_; 
v___x_271_ = lean_unsigned_to_nat(1024u);
v___x_272_ = lean_nat_dec_le(v___x_271_, v_prec_172_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; 
v___x_273_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__9, &l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__9_once, _init_l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__9);
v___y_174_ = v___x_273_;
goto v___jp_173_;
}
else
{
lean_object* v___x_274_; 
v___x_274_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__10, &l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__10_once, _init_l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__10);
v___y_174_ = v___x_274_;
goto v___jp_173_;
}
}
default: 
{
lean_object* v_a_275_; lean_object* v_a_276_; lean_object* v_a_277_; lean_object* v___y_279_; lean_object* v___x_297_; uint8_t v___x_298_; 
v_a_275_ = lean_ctor_get(v_x_171_, 0);
lean_inc(v_a_275_);
v_a_276_ = lean_ctor_get(v_x_171_, 1);
lean_inc(v_a_276_);
v_a_277_ = lean_ctor_get(v_x_171_, 2);
lean_inc(v_a_277_);
lean_dec_ref_known(v_x_171_, 3);
v___x_297_ = lean_unsigned_to_nat(1024u);
v___x_298_ = lean_nat_dec_le(v___x_297_, v_prec_172_);
if (v___x_298_ == 0)
{
lean_object* v___x_299_; 
v___x_299_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__9, &l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__9_once, _init_l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__9);
v___y_279_ = v___x_299_;
goto v___jp_278_;
}
else
{
lean_object* v___x_300_; 
v___x_300_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__10, &l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__10_once, _init_l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__10);
v___y_279_ = v___x_300_;
goto v___jp_278_;
}
v___jp_278_:
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; uint8_t v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_280_ = lean_box(1);
v___x_281_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__19));
v___x_282_ = lean_unsigned_to_nat(1024u);
v___x_283_ = l_Lean_Name_reprPrec(v_a_275_, v___x_282_);
v___x_284_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_281_);
lean_ctor_set(v___x_284_, 1, v___x_283_);
v___x_285_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
lean_ctor_set(v___x_285_, 1, v___x_280_);
v___x_286_ = l_Nat_reprFast(v_a_276_);
v___x_287_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
v___x_288_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_285_);
lean_ctor_set(v___x_288_, 1, v___x_287_);
v___x_289_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
lean_ctor_set(v___x_289_, 1, v___x_280_);
v___x_290_ = l_Nat_reprFast(v_a_277_);
v___x_291_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
v___x_292_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_289_);
lean_ctor_set(v___x_292_, 1, v___x_291_);
lean_inc(v___y_279_);
v___x_293_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_293_, 0, v___y_279_);
lean_ctor_set(v___x_293_, 1, v___x_292_);
v___x_294_ = 0;
v___x_295_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_295_, 0, v___x_293_);
lean_ctor_set_uint8(v___x_295_, sizeof(void*)*1, v___x_294_);
v___x_296_ = l_Repr_addAppParen(v___x_295_, v_prec_172_);
return v___x_296_;
}
}
}
v___jp_173_:
{
lean_object* v___x_175_; lean_object* v___x_176_; uint8_t v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_175_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__1));
lean_inc(v___y_174_);
v___x_176_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_176_, 0, v___y_174_);
lean_ctor_set(v___x_176_, 1, v___x_175_);
v___x_177_ = 0;
v___x_178_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_178_, 0, v___x_176_);
lean_ctor_set_uint8(v___x_178_, sizeof(void*)*1, v___x_177_);
v___x_179_ = l_Repr_addAppParen(v___x_178_, v_prec_172_);
return v___x_179_;
}
v___jp_180_:
{
lean_object* v___x_182_; lean_object* v___x_183_; uint8_t v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_182_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__3));
lean_inc(v___y_181_);
v___x_183_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_183_, 0, v___y_181_);
lean_ctor_set(v___x_183_, 1, v___x_182_);
v___x_184_ = 0;
v___x_185_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_185_, 0, v___x_183_);
lean_ctor_set_uint8(v___x_185_, sizeof(void*)*1, v___x_184_);
v___x_186_ = l_Repr_addAppParen(v___x_185_, v_prec_172_);
return v___x_186_;
}
v___jp_187_:
{
lean_object* v___x_189_; lean_object* v___x_190_; uint8_t v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_189_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__5));
lean_inc(v___y_188_);
v___x_190_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_190_, 0, v___y_188_);
lean_ctor_set(v___x_190_, 1, v___x_189_);
v___x_191_ = 0;
v___x_192_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_192_, 0, v___x_190_);
lean_ctor_set_uint8(v___x_192_, sizeof(void*)*1, v___x_191_);
v___x_193_ = l_Repr_addAppParen(v___x_192_, v_prec_172_);
return v___x_193_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instReprKey_repr___boxed(lean_object* v_x_301_, lean_object* v_prec_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Lean_Meta_LazyDiscrTree_instReprKey_repr(v_x_301_, v_prec_302_);
lean_dec(v_prec_302_);
return v_res_303_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_LazyDiscrTree_Key_hash(lean_object* v_x_306_){
_start:
{
switch(lean_obj_tag(v_x_306_))
{
case 0:
{
lean_object* v_a_307_; lean_object* v_a_308_; uint64_t v___x_309_; uint64_t v___y_311_; 
v_a_307_ = lean_ctor_get(v_x_306_, 0);
v_a_308_ = lean_ctor_get(v_x_306_, 1);
v___x_309_ = 5237ULL;
if (lean_obj_tag(v_a_307_) == 0)
{
uint64_t v___x_315_; 
v___x_315_ = 1723ULL;
v___y_311_ = v___x_315_;
goto v___jp_310_;
}
else
{
uint64_t v_hash_316_; 
v_hash_316_ = lean_ctor_get_uint64(v_a_307_, sizeof(void*)*2);
v___y_311_ = v_hash_316_;
goto v___jp_310_;
}
v___jp_310_:
{
uint64_t v___x_312_; uint64_t v___x_313_; uint64_t v___x_314_; 
v___x_312_ = lean_uint64_of_nat(v_a_308_);
v___x_313_ = lean_uint64_mix_hash(v___y_311_, v___x_312_);
v___x_314_ = lean_uint64_mix_hash(v___x_309_, v___x_313_);
return v___x_314_;
}
}
case 1:
{
lean_object* v_a_317_; lean_object* v_a_318_; uint64_t v___x_319_; uint64_t v___x_320_; uint64_t v___x_321_; uint64_t v___x_322_; uint64_t v___x_323_; 
v_a_317_ = lean_ctor_get(v_x_306_, 0);
v_a_318_ = lean_ctor_get(v_x_306_, 1);
v___x_319_ = 3541ULL;
v___x_320_ = l_Lean_instHashableFVarId_hash(v_a_317_);
v___x_321_ = lean_uint64_of_nat(v_a_318_);
v___x_322_ = lean_uint64_mix_hash(v___x_320_, v___x_321_);
v___x_323_ = lean_uint64_mix_hash(v___x_319_, v___x_322_);
return v___x_323_;
}
case 2:
{
lean_object* v_a_324_; uint64_t v___x_325_; uint64_t v___x_326_; uint64_t v___x_327_; 
v_a_324_ = lean_ctor_get(v_x_306_, 0);
v___x_325_ = 1879ULL;
v___x_326_ = l_Lean_Literal_hash(v_a_324_);
v___x_327_ = lean_uint64_mix_hash(v___x_325_, v___x_326_);
return v___x_327_;
}
case 3:
{
uint64_t v___x_328_; 
v___x_328_ = 7883ULL;
return v___x_328_;
}
case 4:
{
uint64_t v___x_329_; 
v___x_329_ = 2411ULL;
return v___x_329_;
}
case 5:
{
uint64_t v___x_330_; 
v___x_330_ = 17ULL;
return v___x_330_;
}
default: 
{
lean_object* v_a_331_; lean_object* v_a_332_; lean_object* v_a_333_; uint64_t v___x_334_; uint64_t v___y_336_; 
v_a_331_ = lean_ctor_get(v_x_306_, 0);
v_a_332_ = lean_ctor_get(v_x_306_, 1);
v_a_333_ = lean_ctor_get(v_x_306_, 2);
v___x_334_ = lean_uint64_of_nat(v_a_333_);
if (lean_obj_tag(v_a_331_) == 0)
{
uint64_t v___x_340_; 
v___x_340_ = 1723ULL;
v___y_336_ = v___x_340_;
goto v___jp_335_;
}
else
{
uint64_t v_hash_341_; 
v_hash_341_ = lean_ctor_get_uint64(v_a_331_, sizeof(void*)*2);
v___y_336_ = v_hash_341_;
goto v___jp_335_;
}
v___jp_335_:
{
uint64_t v___x_337_; uint64_t v___x_338_; uint64_t v___x_339_; 
v___x_337_ = lean_uint64_of_nat(v_a_332_);
v___x_338_ = lean_uint64_mix_hash(v___y_336_, v___x_337_);
v___x_339_ = lean_uint64_mix_hash(v___x_334_, v___x_338_);
return v___x_339_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_hash___boxed(lean_object* v_x_342_){
_start:
{
uint64_t v_res_343_; lean_object* v_r_344_; 
v_res_343_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_x_342_);
lean_dec(v_x_342_);
v_r_344_ = lean_box_uint64(v_res_343_);
return v_r_344_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_MatchClone_tmpStar___closed__0(void){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_351_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_tmpMVarId));
v___x_352_ = l_Lean_mkMVar(v___x_351_);
return v___x_352_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_MatchClone_tmpStar(void){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_MatchClone_tmpStar___closed__0, &l_Lean_Meta_LazyDiscrTree_MatchClone_tmpStar___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_MatchClone_tmpStar___closed__0);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_ignoreArg(lean_object* v_a_354_, lean_object* v_i_355_, lean_object* v_infos_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_){
_start:
{
lean_object* v___x_362_; uint8_t v___x_363_; 
v___x_362_ = lean_array_get_size(v_infos_356_);
v___x_363_ = lean_nat_dec_lt(v_i_355_, v___x_362_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; 
v___x_364_ = l_Lean_Meta_isProof(v_a_354_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
return v___x_364_;
}
else
{
lean_object* v_info_365_; uint8_t v_isInstance_366_; uint8_t v___y_368_; 
v_info_365_ = lean_array_fget_borrowed(v_infos_356_, v_i_355_);
v_isInstance_366_ = lean_ctor_get_uint8(v_info_365_, sizeof(void*)*1 + 4);
if (v_isInstance_366_ == 0)
{
uint8_t v___x_384_; 
v___x_384_ = l_Lean_Meta_ParamInfo_isImplicit(v_info_365_);
if (v___x_384_ == 0)
{
uint8_t v___x_385_; 
v___x_385_ = l_Lean_Meta_ParamInfo_isStrictImplicit(v_info_365_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; 
v___x_386_ = l_Lean_Meta_isProof(v_a_354_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
return v___x_386_;
}
else
{
v___y_368_ = v___x_385_;
goto v___jp_367_;
}
}
else
{
v___y_368_ = v___x_363_;
goto v___jp_367_;
}
}
else
{
lean_object* v___x_387_; lean_object* v___x_388_; 
lean_dec_ref(v_a_354_);
v___x_387_ = lean_box(v___x_363_);
v___x_388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
return v___x_388_;
}
v___jp_367_:
{
lean_object* v___x_369_; 
v___x_369_ = l_Lean_Meta_isType(v_a_354_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
if (lean_obj_tag(v___x_369_) == 0)
{
lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_383_; 
v_a_370_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_383_ == 0)
{
v___x_372_ = v___x_369_;
v_isShared_373_ = v_isSharedCheck_383_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_dec(v___x_369_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_383_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
uint8_t v___x_374_; 
v___x_374_ = lean_unbox(v_a_370_);
lean_dec(v_a_370_);
if (v___x_374_ == 0)
{
lean_object* v___x_375_; lean_object* v___x_377_; 
v___x_375_ = lean_box(v___y_368_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v___x_375_);
v___x_377_ = v___x_372_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v___x_375_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
else
{
lean_object* v___x_379_; lean_object* v___x_381_; 
v___x_379_ = lean_box(v_isInstance_366_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v___x_379_);
v___x_381_ = v___x_372_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v___x_379_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
}
else
{
return v___x_369_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_ignoreArg___boxed(lean_object* v_a_389_, lean_object* v_i_390_, lean_object* v_infos_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_Meta_LazyDiscrTree_MatchClone_ignoreArg(v_a_389_, v_i_390_, v_infos_391_, v_a_392_, v_a_393_, v_a_394_, v_a_395_);
lean_dec(v_a_395_);
lean_dec_ref(v_a_394_);
lean_dec(v_a_393_);
lean_dec_ref(v_a_392_);
lean_dec_ref(v_infos_391_);
lean_dec(v_i_390_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_pushArgsAux(lean_object* v_infos_398_, lean_object* v_x_399_, lean_object* v_x_400_, lean_object* v_x_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_){
_start:
{
if (lean_obj_tag(v_x_400_) == 5)
{
lean_object* v_fn_407_; lean_object* v_arg_408_; lean_object* v___x_409_; 
v_fn_407_ = lean_ctor_get(v_x_400_, 0);
lean_inc_ref(v_fn_407_);
v_arg_408_ = lean_ctor_get(v_x_400_, 1);
lean_inc_ref_n(v_arg_408_, 2);
lean_dec_ref_known(v_x_400_, 2);
v___x_409_ = l_Lean_Meta_LazyDiscrTree_MatchClone_ignoreArg(v_arg_408_, v_x_399_, v_infos_398_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v_a_410_; uint8_t v___x_411_; 
v_a_410_ = lean_ctor_get(v___x_409_, 0);
lean_inc(v_a_410_);
lean_dec_ref_known(v___x_409_, 1);
v___x_411_ = lean_unbox(v_a_410_);
lean_dec(v_a_410_);
if (v___x_411_ == 0)
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_412_ = lean_unsigned_to_nat(1u);
v___x_413_ = lean_nat_sub(v_x_399_, v___x_412_);
lean_dec(v_x_399_);
v___x_414_ = lean_array_push(v_x_401_, v_arg_408_);
v_x_399_ = v___x_413_;
v_x_400_ = v_fn_407_;
v_x_401_ = v___x_414_;
goto _start;
}
else
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
lean_dec_ref(v_arg_408_);
v___x_416_ = lean_unsigned_to_nat(1u);
v___x_417_ = lean_nat_sub(v_x_399_, v___x_416_);
lean_dec(v_x_399_);
v___x_418_ = l_Lean_Meta_LazyDiscrTree_MatchClone_tmpStar;
v___x_419_ = lean_array_push(v_x_401_, v___x_418_);
v_x_399_ = v___x_417_;
v_x_400_ = v_fn_407_;
v_x_401_ = v___x_419_;
goto _start;
}
}
else
{
lean_object* v_a_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_428_; 
lean_dec_ref(v_arg_408_);
lean_dec_ref(v_fn_407_);
lean_dec_ref(v_x_401_);
lean_dec(v_x_399_);
v_a_421_ = lean_ctor_get(v___x_409_, 0);
v_isSharedCheck_428_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_428_ == 0)
{
v___x_423_ = v___x_409_;
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_a_421_);
lean_dec(v___x_409_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_426_; 
if (v_isShared_424_ == 0)
{
v___x_426_ = v___x_423_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_a_421_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
}
else
{
lean_object* v___x_429_; 
lean_dec_ref(v_x_400_);
lean_dec(v_x_399_);
v___x_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_429_, 0, v_x_401_);
return v___x_429_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_pushArgsAux___boxed(lean_object* v_infos_430_, lean_object* v_x_431_, lean_object* v_x_432_, lean_object* v_x_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Lean_Meta_LazyDiscrTree_MatchClone_pushArgsAux(v_infos_430_, v_x_431_, v_x_432_, v_x_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_);
lean_dec(v_a_437_);
lean_dec_ref(v_a_436_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
lean_dec_ref(v_infos_430_);
return v_res_439_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral(lean_object* v_e_454_){
_start:
{
uint8_t v___x_455_; uint8_t v___x_456_; 
v___x_455_ = l_Lean_Expr_isRawNatLit(v_e_454_);
v___x_456_ = 1;
if (v___x_455_ == 0)
{
lean_object* v_f_457_; uint8_t v___x_458_; 
v_f_457_ = l_Lean_Expr_getAppFn(v_e_454_);
v___x_458_ = l_Lean_Expr_isConst(v_f_457_);
if (v___x_458_ == 0)
{
lean_dec_ref(v_f_457_);
lean_dec_ref(v_e_454_);
return v___x_455_;
}
else
{
if (v___x_455_ == 0)
{
lean_object* v_fName_459_; lean_object* v___x_477_; uint8_t v___x_478_; 
v_fName_459_ = l_Lean_Expr_constName_x21(v_f_457_);
lean_dec_ref(v_f_457_);
v___x_477_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__7));
v___x_478_ = lean_name_eq(v_fName_459_, v___x_477_);
if (v___x_478_ == 0)
{
goto v___jp_466_;
}
else
{
lean_object* v___x_479_; lean_object* v___x_480_; uint8_t v___x_481_; 
v___x_479_ = l_Lean_Expr_getAppNumArgs(v_e_454_);
v___x_480_ = lean_unsigned_to_nat(1u);
v___x_481_ = lean_nat_dec_eq(v___x_479_, v___x_480_);
lean_dec(v___x_479_);
if (v___x_481_ == 0)
{
goto v___jp_466_;
}
else
{
lean_object* v___x_482_; 
lean_dec(v_fName_459_);
v___x_482_ = l_Lean_Expr_appArg_x21(v_e_454_);
lean_dec_ref(v_e_454_);
v_e_454_ = v___x_482_;
goto _start;
}
}
v___jp_460_:
{
lean_object* v___x_461_; uint8_t v___x_462_; 
v___x_461_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__2));
v___x_462_ = lean_name_eq(v_fName_459_, v___x_461_);
lean_dec(v_fName_459_);
if (v___x_462_ == 0)
{
lean_dec_ref(v_e_454_);
return v___x_455_;
}
else
{
lean_object* v___x_463_; lean_object* v___x_464_; uint8_t v___x_465_; 
v___x_463_ = l_Lean_Expr_getAppNumArgs(v_e_454_);
lean_dec_ref(v_e_454_);
v___x_464_ = lean_unsigned_to_nat(0u);
v___x_465_ = lean_nat_dec_eq(v___x_463_, v___x_464_);
lean_dec(v___x_463_);
if (v___x_465_ == 0)
{
return v___x_465_;
}
else
{
return v___x_456_;
}
}
}
v___jp_466_:
{
lean_object* v___x_467_; uint8_t v___x_468_; 
v___x_467_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__5));
v___x_468_ = lean_name_eq(v_fName_459_, v___x_467_);
if (v___x_468_ == 0)
{
goto v___jp_460_;
}
else
{
lean_object* v___x_469_; lean_object* v___x_470_; uint8_t v___x_471_; 
v___x_469_ = l_Lean_Expr_getAppNumArgs(v_e_454_);
v___x_470_ = lean_unsigned_to_nat(3u);
v___x_471_ = lean_nat_dec_eq(v___x_469_, v___x_470_);
if (v___x_471_ == 0)
{
lean_dec(v___x_469_);
goto v___jp_460_;
}
else
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
lean_dec(v_fName_459_);
v___x_472_ = lean_unsigned_to_nat(1u);
v___x_473_ = lean_nat_sub(v___x_469_, v___x_472_);
lean_dec(v___x_469_);
v___x_474_ = lean_nat_sub(v___x_473_, v___x_472_);
lean_dec(v___x_473_);
v___x_475_ = l_Lean_Expr_getRevArg_x21(v_e_454_, v___x_474_);
lean_dec_ref(v_e_454_);
v_e_454_ = v___x_475_;
goto _start;
}
}
}
}
else
{
lean_dec_ref(v_f_457_);
lean_dec_ref(v_e_454_);
return v___x_455_;
}
}
}
else
{
lean_dec_ref(v_e_454_);
return v___x_456_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___boxed(lean_object* v_e_484_){
_start:
{
uint8_t v_res_485_; lean_object* v_r_486_; 
v_res_485_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral(v_e_484_);
v_r_486_ = lean_box(v_res_485_);
return v_r_486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f_loop(lean_object* v_e_489_){
_start:
{
uint8_t v___y_491_; lean_object* v_f_494_; 
v_f_494_ = l_Lean_Expr_getAppFn(v_e_489_);
switch(lean_obj_tag(v_f_494_))
{
case 9:
{
lean_object* v_a_495_; 
lean_dec_ref(v_e_489_);
v_a_495_ = lean_ctor_get(v_f_494_, 0);
lean_inc_ref(v_a_495_);
lean_dec_ref_known(v_f_494_, 1);
if (lean_obj_tag(v_a_495_) == 0)
{
lean_object* v_val_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_503_; 
v_val_496_ = lean_ctor_get(v_a_495_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v_a_495_);
if (v_isSharedCheck_503_ == 0)
{
v___x_498_ = v_a_495_;
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_val_496_);
lean_dec(v_a_495_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_501_; 
if (v_isShared_499_ == 0)
{
lean_ctor_set_tag(v___x_498_, 1);
v___x_501_ = v___x_498_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_val_496_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
else
{
lean_object* v___x_504_; 
lean_dec_ref(v_a_495_);
v___x_504_ = lean_box(0);
return v___x_504_;
}
}
case 4:
{
lean_object* v_declName_505_; uint8_t v___y_507_; uint8_t v___y_520_; lean_object* v___x_538_; uint8_t v___x_539_; 
v_declName_505_ = lean_ctor_get(v_f_494_, 0);
lean_inc(v_declName_505_);
lean_dec_ref_known(v_f_494_, 2);
v___x_538_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__7));
v___x_539_ = lean_name_eq(v_declName_505_, v___x_538_);
if (v___x_539_ == 0)
{
v___y_520_ = v___x_539_;
goto v___jp_519_;
}
else
{
lean_object* v___x_540_; lean_object* v___x_541_; uint8_t v___x_542_; 
v___x_540_ = l_Lean_Expr_getAppNumArgs(v_e_489_);
v___x_541_ = lean_unsigned_to_nat(1u);
v___x_542_ = lean_nat_dec_eq(v___x_540_, v___x_541_);
lean_dec(v___x_540_);
v___y_520_ = v___x_542_;
goto v___jp_519_;
}
v___jp_506_:
{
if (v___y_507_ == 0)
{
lean_object* v___x_508_; uint8_t v___x_509_; 
v___x_508_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__2));
v___x_509_ = lean_name_eq(v_declName_505_, v___x_508_);
lean_dec(v_declName_505_);
if (v___x_509_ == 0)
{
lean_dec_ref(v_e_489_);
v___y_491_ = v___x_509_;
goto v___jp_490_;
}
else
{
lean_object* v___x_510_; lean_object* v___x_511_; uint8_t v___x_512_; 
v___x_510_ = l_Lean_Expr_getAppNumArgs(v_e_489_);
lean_dec_ref(v_e_489_);
v___x_511_ = lean_unsigned_to_nat(0u);
v___x_512_ = lean_nat_dec_eq(v___x_510_, v___x_511_);
lean_dec(v___x_510_);
v___y_491_ = v___x_512_;
goto v___jp_490_;
}
}
else
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
lean_dec(v_declName_505_);
v___x_513_ = lean_unsigned_to_nat(1u);
v___x_514_ = l_Lean_Expr_getAppNumArgs(v_e_489_);
v___x_515_ = lean_nat_sub(v___x_514_, v___x_513_);
lean_dec(v___x_514_);
v___x_516_ = lean_nat_sub(v___x_515_, v___x_513_);
lean_dec(v___x_515_);
v___x_517_ = l_Lean_Expr_getRevArg_x21(v_e_489_, v___x_516_);
lean_dec_ref(v_e_489_);
v_e_489_ = v___x_517_;
goto _start;
}
}
v___jp_519_:
{
if (v___y_520_ == 0)
{
lean_object* v___x_521_; uint8_t v___x_522_; 
v___x_521_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__5));
v___x_522_ = lean_name_eq(v_declName_505_, v___x_521_);
if (v___x_522_ == 0)
{
v___y_507_ = v___x_522_;
goto v___jp_506_;
}
else
{
lean_object* v___x_523_; lean_object* v___x_524_; uint8_t v___x_525_; 
v___x_523_ = l_Lean_Expr_getAppNumArgs(v_e_489_);
v___x_524_ = lean_unsigned_to_nat(3u);
v___x_525_ = lean_nat_dec_eq(v___x_523_, v___x_524_);
lean_dec(v___x_523_);
v___y_507_ = v___x_525_;
goto v___jp_506_;
}
}
else
{
lean_object* v___x_526_; lean_object* v___x_527_; 
lean_dec(v_declName_505_);
v___x_526_ = l_Lean_Expr_appArg_x21(v_e_489_);
lean_dec_ref(v_e_489_);
v___x_527_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f_loop(v___x_526_);
if (lean_obj_tag(v___x_527_) == 0)
{
return v___x_527_;
}
else
{
lean_object* v_val_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_537_; 
v_val_528_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_537_ == 0)
{
v___x_530_ = v___x_527_;
v_isShared_531_ = v_isSharedCheck_537_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_val_528_);
lean_dec(v___x_527_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_537_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_535_; 
v___x_532_ = lean_unsigned_to_nat(1u);
v___x_533_ = lean_nat_add(v_val_528_, v___x_532_);
lean_dec(v_val_528_);
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 0, v___x_533_);
v___x_535_ = v___x_530_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v___x_533_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_543_; 
lean_dec_ref(v_f_494_);
lean_dec_ref(v_e_489_);
v___x_543_ = lean_box(0);
return v___x_543_;
}
}
v___jp_490_:
{
if (v___y_491_ == 0)
{
lean_object* v___x_492_; 
v___x_492_ = lean_box(0);
return v___x_492_;
}
else
{
lean_object* v___x_493_; 
v___x_493_ = ((lean_object*)(l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f_loop___closed__0));
return v___x_493_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f(lean_object* v_e_544_){
_start:
{
uint8_t v___x_545_; 
lean_inc_ref(v_e_544_);
v___x_545_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral(v_e_544_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; 
lean_dec_ref(v_e_544_);
v___x_546_ = lean_box(0);
return v___x_546_;
}
else
{
lean_object* v___x_547_; 
v___x_547_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f_loop(v_e_544_);
if (lean_obj_tag(v___x_547_) == 1)
{
lean_object* v_val_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_556_; 
v_val_548_ = lean_ctor_get(v___x_547_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_547_);
if (v_isSharedCheck_556_ == 0)
{
v___x_550_ = v___x_547_;
v_isShared_551_ = v_isSharedCheck_556_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_val_548_);
lean_dec(v___x_547_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_556_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_552_; lean_object* v___x_554_; 
v___x_552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_552_, 0, v_val_548_);
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 0, v___x_552_);
v___x_554_ = v___x_550_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v___x_552_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
else
{
lean_object* v___x_557_; 
lean_dec(v___x_547_);
v___x_557_ = lean_box(0);
return v___x_557_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNatType(lean_object* v_e_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_){
_start:
{
lean_object* v___x_566_; 
lean_inc(v_a_564_);
lean_inc_ref(v_a_563_);
lean_inc(v_a_562_);
lean_inc_ref(v_a_561_);
v___x_566_ = lean_whnf(v_e_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_);
if (lean_obj_tag(v___x_566_) == 0)
{
lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_577_; 
v_a_567_ = lean_ctor_get(v___x_566_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_566_);
if (v_isSharedCheck_577_ == 0)
{
v___x_569_ = v___x_566_;
v_isShared_570_ = v_isSharedCheck_577_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_dec(v___x_566_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_577_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_571_; uint8_t v___x_572_; lean_object* v___x_573_; lean_object* v___x_575_; 
v___x_571_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNatType___closed__0));
v___x_572_ = l_Lean_Expr_isConstOf(v_a_567_, v___x_571_);
lean_dec(v_a_567_);
v___x_573_ = lean_box(v___x_572_);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 0, v___x_573_);
v___x_575_ = v___x_569_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v___x_573_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
else
{
lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_585_; 
v_a_578_ = lean_ctor_get(v___x_566_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_566_);
if (v_isSharedCheck_585_ == 0)
{
v___x_580_ = v___x_566_;
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v___x_566_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_583_; 
if (v_isShared_581_ == 0)
{
v___x_583_ = v___x_580_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_a_578_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNatType___boxed(lean_object* v_e_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNatType(v_e_586_, v_a_587_, v_a_588_, v_a_589_, v_a_590_);
lean_dec(v_a_590_);
lean_dec_ref(v_a_589_);
lean_dec(v_a_588_);
lean_dec_ref(v_a_587_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset(lean_object* v_fName_606_, lean_object* v_e_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_){
_start:
{
uint8_t v___y_614_; uint8_t v___y_644_; uint8_t v___y_669_; lean_object* v___x_679_; uint8_t v___x_680_; 
v___x_679_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___closed__6));
v___x_680_ = lean_name_eq(v_fName_606_, v___x_679_);
if (v___x_680_ == 0)
{
v___y_669_ = v___x_680_;
goto v___jp_668_;
}
else
{
lean_object* v___x_681_; lean_object* v___x_682_; uint8_t v___x_683_; 
v___x_681_ = l_Lean_Expr_getAppNumArgs(v_e_607_);
v___x_682_ = lean_unsigned_to_nat(2u);
v___x_683_ = lean_nat_dec_eq(v___x_681_, v___x_682_);
lean_dec(v___x_681_);
v___y_669_ = v___x_683_;
goto v___jp_668_;
}
v___jp_613_:
{
if (v___y_614_ == 0)
{
lean_object* v___x_615_; uint8_t v___x_616_; 
v___x_615_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__7));
v___x_616_ = lean_name_eq(v_fName_606_, v___x_615_);
if (v___x_616_ == 0)
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = lean_box(v___x_616_);
v___x_618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_618_, 0, v___x_617_);
return v___x_618_;
}
else
{
lean_object* v___x_619_; lean_object* v___x_620_; uint8_t v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_619_ = l_Lean_Expr_getAppNumArgs(v_e_607_);
v___x_620_ = lean_unsigned_to_nat(1u);
v___x_621_ = lean_nat_dec_eq(v___x_619_, v___x_620_);
lean_dec(v___x_619_);
v___x_622_ = lean_box(v___x_621_);
v___x_623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_623_, 0, v___x_622_);
return v___x_623_;
}
}
else
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_624_ = lean_unsigned_to_nat(1u);
v___x_625_ = l_Lean_Expr_getAppNumArgs(v_e_607_);
v___x_626_ = lean_nat_sub(v___x_625_, v___x_624_);
lean_dec(v___x_625_);
v___x_627_ = lean_nat_sub(v___x_626_, v___x_624_);
lean_dec(v___x_626_);
v___x_628_ = l_Lean_Expr_getRevArg_x21(v_e_607_, v___x_627_);
v___x_629_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNatType(v___x_628_, v_a_608_, v_a_609_, v_a_610_, v_a_611_);
if (lean_obj_tag(v___x_629_) == 0)
{
lean_object* v_a_630_; uint8_t v___x_631_; 
v_a_630_ = lean_ctor_get(v___x_629_, 0);
v___x_631_ = lean_unbox(v_a_630_);
if (v___x_631_ == 0)
{
return v___x_629_;
}
else
{
lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_641_; 
v_isSharedCheck_641_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_641_ == 0)
{
lean_object* v_unused_642_; 
v_unused_642_ = lean_ctor_get(v___x_629_, 0);
lean_dec(v_unused_642_);
v___x_633_ = v___x_629_;
v_isShared_634_ = v_isSharedCheck_641_;
goto v_resetjp_632_;
}
else
{
lean_dec(v___x_629_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_641_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_635_; uint8_t v___x_636_; lean_object* v___x_637_; lean_object* v___x_639_; 
v___x_635_ = l_Lean_Expr_appArg_x21(v_e_607_);
v___x_636_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral(v___x_635_);
v___x_637_ = lean_box(v___x_636_);
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 0, v___x_637_);
v___x_639_ = v___x_633_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v___x_637_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
}
else
{
return v___x_629_;
}
}
}
v___jp_643_:
{
if (v___y_644_ == 0)
{
lean_object* v___x_645_; uint8_t v___x_646_; 
v___x_645_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___closed__2));
v___x_646_ = lean_name_eq(v_fName_606_, v___x_645_);
if (v___x_646_ == 0)
{
v___y_614_ = v___x_646_;
goto v___jp_613_;
}
else
{
lean_object* v___x_647_; lean_object* v___x_648_; uint8_t v___x_649_; 
v___x_647_ = l_Lean_Expr_getAppNumArgs(v_e_607_);
v___x_648_ = lean_unsigned_to_nat(6u);
v___x_649_ = lean_nat_dec_eq(v___x_647_, v___x_648_);
lean_dec(v___x_647_);
v___y_614_ = v___x_649_;
goto v___jp_613_;
}
}
else
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_650_ = l_Lean_Expr_getAppNumArgs(v_e_607_);
v___x_651_ = lean_unsigned_to_nat(1u);
v___x_652_ = lean_nat_sub(v___x_650_, v___x_651_);
lean_dec(v___x_650_);
v___x_653_ = l_Lean_Expr_getRevArg_x21(v_e_607_, v___x_652_);
v___x_654_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNatType(v___x_653_, v_a_608_, v_a_609_, v_a_610_, v_a_611_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v_a_655_; uint8_t v___x_656_; 
v_a_655_ = lean_ctor_get(v___x_654_, 0);
v___x_656_ = lean_unbox(v_a_655_);
if (v___x_656_ == 0)
{
return v___x_654_;
}
else
{
lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_666_; 
v_isSharedCheck_666_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_666_ == 0)
{
lean_object* v_unused_667_; 
v_unused_667_ = lean_ctor_get(v___x_654_, 0);
lean_dec(v_unused_667_);
v___x_658_ = v___x_654_;
v_isShared_659_ = v_isSharedCheck_666_;
goto v_resetjp_657_;
}
else
{
lean_dec(v___x_654_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_666_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_660_; uint8_t v___x_661_; lean_object* v___x_662_; lean_object* v___x_664_; 
v___x_660_ = l_Lean_Expr_appArg_x21(v_e_607_);
v___x_661_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral(v___x_660_);
v___x_662_ = lean_box(v___x_661_);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 0, v___x_662_);
v___x_664_ = v___x_658_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v___x_662_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
}
}
else
{
return v___x_654_;
}
}
}
v___jp_668_:
{
if (v___y_669_ == 0)
{
lean_object* v___x_670_; uint8_t v___x_671_; 
v___x_670_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___closed__5));
v___x_671_ = lean_name_eq(v_fName_606_, v___x_670_);
if (v___x_671_ == 0)
{
v___y_644_ = v___x_671_;
goto v___jp_643_;
}
else
{
lean_object* v___x_672_; lean_object* v___x_673_; uint8_t v___x_674_; 
v___x_672_ = l_Lean_Expr_getAppNumArgs(v_e_607_);
v___x_673_ = lean_unsigned_to_nat(4u);
v___x_674_ = lean_nat_dec_eq(v___x_672_, v___x_673_);
lean_dec(v___x_672_);
v___y_644_ = v___x_674_;
goto v___jp_643_;
}
}
else
{
lean_object* v___x_675_; uint8_t v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_675_ = l_Lean_Expr_appArg_x21(v_e_607_);
v___x_676_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral(v___x_675_);
v___x_677_ = lean_box(v___x_676_);
v___x_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_678_, 0, v___x_677_);
return v___x_678_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___boxed(lean_object* v_fName_684_, lean_object* v_e_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset(v_fName_684_, v_e_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_);
lean_dec(v_a_689_);
lean_dec_ref(v_a_688_);
lean_dec(v_a_687_);
lean_dec_ref(v_a_686_);
lean_dec_ref(v_e_685_);
lean_dec(v_fName_684_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_shouldAddAsStar(lean_object* v_fName_692_, lean_object* v_e_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_){
_start:
{
lean_object* v___x_699_; 
v___x_699_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset(v_fName_692_, v_e_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_shouldAddAsStar___boxed(lean_object* v_fName_700_, lean_object* v_e_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_Lean_Meta_LazyDiscrTree_MatchClone_shouldAddAsStar(v_fName_700_, v_e_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_);
lean_dec(v_a_705_);
lean_dec_ref(v_a_704_);
lean_dec(v_a_703_);
lean_dec_ref(v_a_702_);
lean_dec_ref(v_e_701_);
lean_dec(v_fName_700_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__0(lean_object* v_e_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
uint8_t v___x_714_; 
v___x_714_ = l_Lean_Expr_hasLooseBVars(v_e_710_);
if (v___x_714_ == 0)
{
lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_715_, 0, v_e_710_);
v___x_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_716_, 0, v___x_715_);
return v___x_716_;
}
else
{
uint8_t v___x_717_; uint8_t v___x_718_; 
v___x_717_ = 0;
v___x_718_ = l_Lean_Expr_isHeadBetaTarget(v_e_710_, v___x_717_);
if (v___x_718_ == 0)
{
lean_object* v___x_719_; lean_object* v___x_720_; 
lean_dec_ref(v_e_710_);
v___x_719_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__0___closed__0));
v___x_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_720_, 0, v___x_719_);
return v___x_720_;
}
else
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_721_ = l_Lean_Expr_headBeta(v_e_710_);
v___x_722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_722_, 0, v___x_721_);
v___x_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_723_, 0, v___x_722_);
return v___x_723_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__0___boxed(lean_object* v_e_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__0(v_e_724_, v___y_725_, v___y_726_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__1(lean_object* v_e_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_733_, 0, v_e_729_);
v___x_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_734_, 0, v___x_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__1___boxed(lean_object* v_e_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__1(v_e_735_, v___y_736_, v___y_737_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
return v_res_739_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_740_ = lean_box(0);
v___x_741_ = l_Lean_interruptExceptionId;
v___x_742_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_741_);
lean_ctor_set(v___x_742_, 1, v___x_740_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg(){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_744_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg___closed__0);
v___x_745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_745_, 0, v___x_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg___boxed(lean_object* v___y_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg();
return v_res_747_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_753_ = l_Lean_maxRecDepthErrorMessage;
v___x_754_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
return v___x_754_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_755_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__3);
v___x_756_ = l_Lean_MessageData_ofFormat(v___x_755_);
return v___x_756_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_757_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__4);
v___x_758_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__2));
v___x_759_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_759_, 0, v___x_758_);
lean_ctor_set(v___x_759_, 1, v___x_757_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_ref_760_){
_start:
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_762_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_763_, 0, v_ref_760_);
lean_ctor_set(v___x_763_, 1, v___x_762_);
v___x_764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_764_, 0, v___x_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_ref_765_, lean_object* v___y_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_765_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg(lean_object* v_x_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_){
_start:
{
lean_object* v___y_774_; uint16_t v___y_784_; uint8_t v___y_785_; lean_object* v___y_786_; lean_object* v___y_787_; uint8_t v___y_788_; lean_object* v___y_789_; lean_object* v_toCold_794_; lean_object* v_currRecDepth_795_; lean_object* v_ref_796_; uint16_t v_optionFlags_797_; uint8_t v_suppressElabErrors_798_; uint8_t v_isRecordingDeps_799_; lean_object* v_maxRecDepth_800_; lean_object* v_cancelTk_x3f_801_; 
v_toCold_794_ = lean_ctor_get(v___y_770_, 0);
v_currRecDepth_795_ = lean_ctor_get(v___y_770_, 1);
v_ref_796_ = lean_ctor_get(v___y_770_, 2);
v_optionFlags_797_ = lean_ctor_get_uint16(v___y_770_, sizeof(void*)*3);
v_suppressElabErrors_798_ = lean_ctor_get_uint8(v___y_770_, sizeof(void*)*3 + 2);
v_isRecordingDeps_799_ = lean_ctor_get_uint8(v___y_770_, sizeof(void*)*3 + 3);
v_maxRecDepth_800_ = lean_ctor_get(v_toCold_794_, 3);
v_cancelTk_x3f_801_ = lean_ctor_get(v_toCold_794_, 10);
if (lean_obj_tag(v_cancelTk_x3f_801_) == 1)
{
lean_object* v_val_807_; uint8_t v___x_808_; 
v_val_807_ = lean_ctor_get(v_cancelTk_x3f_801_, 0);
v___x_808_ = l_IO_CancelToken_isSet(v_val_807_);
if (v___x_808_ == 0)
{
goto v___jp_802_;
}
else
{
lean_object* v___x_809_; lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_817_; 
lean_dec_ref(v_x_768_);
v___x_809_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg();
v_a_810_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_817_ == 0)
{
v___x_812_ = v___x_809_;
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_809_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
if (v_isShared_813_ == 0)
{
v___x_815_ = v___x_812_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_a_810_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
else
{
goto v___jp_802_;
}
v___jp_773_:
{
if (lean_obj_tag(v___y_774_) == 0)
{
return v___y_774_;
}
else
{
lean_object* v_a_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_782_; 
v_a_775_ = lean_ctor_get(v___y_774_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___y_774_);
if (v_isSharedCheck_782_ == 0)
{
v___x_777_ = v___y_774_;
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_a_775_);
lean_dec(v___y_774_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_780_; 
if (v_isShared_778_ == 0)
{
v___x_780_ = v___x_777_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_a_775_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
}
v___jp_783_:
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_790_ = lean_unsigned_to_nat(1u);
v___x_791_ = lean_nat_add(v___y_786_, v___x_790_);
lean_inc_ref(v___y_787_);
v___x_792_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_792_, 0, v___y_787_);
lean_ctor_set(v___x_792_, 1, v___x_791_);
lean_ctor_set(v___x_792_, 2, v___y_789_);
lean_ctor_set_uint16(v___x_792_, sizeof(void*)*3, v___y_784_);
lean_ctor_set_uint8(v___x_792_, sizeof(void*)*3 + 2, v___y_785_);
lean_ctor_set_uint8(v___x_792_, sizeof(void*)*3 + 3, v___y_788_);
lean_inc(v___y_771_);
lean_inc(v___y_769_);
v___x_793_ = lean_apply_4(v_x_768_, v___y_769_, v___x_792_, v___y_771_, lean_box(0));
v___y_774_ = v___x_793_;
goto v___jp_773_;
}
v___jp_802_:
{
lean_object* v___x_803_; uint8_t v___x_804_; 
v___x_803_ = lean_unsigned_to_nat(0u);
v___x_804_ = lean_nat_dec_eq(v_maxRecDepth_800_, v___x_803_);
if (v___x_804_ == 0)
{
uint8_t v___x_805_; 
v___x_805_ = lean_nat_dec_eq(v_currRecDepth_795_, v_maxRecDepth_800_);
if (v___x_805_ == 0)
{
lean_inc(v_ref_796_);
v___y_784_ = v_optionFlags_797_;
v___y_785_ = v_suppressElabErrors_798_;
v___y_786_ = v_currRecDepth_795_;
v___y_787_ = v_toCold_794_;
v___y_788_ = v_isRecordingDeps_799_;
v___y_789_ = v_ref_796_;
goto v___jp_783_;
}
else
{
lean_object* v___x_806_; 
lean_dec_ref(v_x_768_);
lean_inc(v_ref_796_);
v___x_806_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_796_);
v___y_774_ = v___x_806_;
goto v___jp_773_;
}
}
else
{
lean_inc(v_ref_796_);
v___y_784_ = v_optionFlags_797_;
v___y_785_ = v_suppressElabErrors_798_;
v___y_786_ = v_currRecDepth_795_;
v___y_787_ = v_toCold_794_;
v___y_788_ = v_isRecordingDeps_799_;
v___y_789_ = v_ref_796_;
goto v___jp_783_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg(v_x_818_, v___y_819_, v___y_820_, v___y_821_);
lean_dec(v___y_821_);
lean_dec_ref(v___y_820_);
lean_dec(v___y_819_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_a_824_, lean_object* v_x_825_){
_start:
{
if (lean_obj_tag(v_x_825_) == 0)
{
lean_object* v___x_826_; 
v___x_826_ = lean_box(0);
return v___x_826_;
}
else
{
lean_object* v_key_827_; lean_object* v_value_828_; lean_object* v_tail_829_; uint8_t v___x_830_; 
v_key_827_ = lean_ctor_get(v_x_825_, 0);
v_value_828_ = lean_ctor_get(v_x_825_, 1);
v_tail_829_ = lean_ctor_get(v_x_825_, 2);
v___x_830_ = l_Lean_ExprStructEq_beq(v_key_827_, v_a_824_);
if (v___x_830_ == 0)
{
v_x_825_ = v_tail_829_;
goto _start;
}
else
{
lean_object* v___x_832_; 
lean_inc(v_value_828_);
v___x_832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_832_, 0, v_value_828_);
return v___x_832_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_a_833_, lean_object* v_x_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg(v_a_833_, v_x_834_);
lean_dec(v_x_834_);
lean_dec_ref(v_a_833_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg(lean_object* v_m_836_, lean_object* v_a_837_){
_start:
{
lean_object* v_buckets_838_; lean_object* v___x_839_; uint64_t v___x_840_; uint64_t v___x_841_; uint64_t v___x_842_; uint64_t v_fold_843_; uint64_t v___x_844_; uint64_t v___x_845_; uint64_t v___x_846_; size_t v___x_847_; size_t v___x_848_; size_t v___x_849_; size_t v___x_850_; size_t v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v_buckets_838_ = lean_ctor_get(v_m_836_, 1);
v___x_839_ = lean_array_get_size(v_buckets_838_);
v___x_840_ = l_Lean_ExprStructEq_hash(v_a_837_);
v___x_841_ = 32ULL;
v___x_842_ = lean_uint64_shift_right(v___x_840_, v___x_841_);
v_fold_843_ = lean_uint64_xor(v___x_840_, v___x_842_);
v___x_844_ = 16ULL;
v___x_845_ = lean_uint64_shift_right(v_fold_843_, v___x_844_);
v___x_846_ = lean_uint64_xor(v_fold_843_, v___x_845_);
v___x_847_ = lean_uint64_to_usize(v___x_846_);
v___x_848_ = lean_usize_of_nat(v___x_839_);
v___x_849_ = ((size_t)1ULL);
v___x_850_ = lean_usize_sub(v___x_848_, v___x_849_);
v___x_851_ = lean_usize_land(v___x_847_, v___x_850_);
v___x_852_ = lean_array_uget_borrowed(v_buckets_838_, v___x_851_);
v___x_853_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg(v_a_837_, v___x_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_m_854_, lean_object* v_a_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg(v_m_854_, v_a_855_);
lean_dec_ref(v_a_855_);
lean_dec_ref(v_m_854_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12___redArg(lean_object* v_a_857_, lean_object* v_b_858_, lean_object* v_x_859_){
_start:
{
if (lean_obj_tag(v_x_859_) == 0)
{
lean_dec(v_b_858_);
lean_dec_ref(v_a_857_);
return v_x_859_;
}
else
{
lean_object* v_key_860_; lean_object* v_value_861_; lean_object* v_tail_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_874_; 
v_key_860_ = lean_ctor_get(v_x_859_, 0);
v_value_861_ = lean_ctor_get(v_x_859_, 1);
v_tail_862_ = lean_ctor_get(v_x_859_, 2);
v_isSharedCheck_874_ = !lean_is_exclusive(v_x_859_);
if (v_isSharedCheck_874_ == 0)
{
v___x_864_ = v_x_859_;
v_isShared_865_ = v_isSharedCheck_874_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_tail_862_);
lean_inc(v_value_861_);
lean_inc(v_key_860_);
lean_dec(v_x_859_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_874_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
uint8_t v___x_866_; 
v___x_866_ = l_Lean_ExprStructEq_beq(v_key_860_, v_a_857_);
if (v___x_866_ == 0)
{
lean_object* v___x_867_; lean_object* v___x_869_; 
v___x_867_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12___redArg(v_a_857_, v_b_858_, v_tail_862_);
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 2, v___x_867_);
v___x_869_ = v___x_864_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_key_860_);
lean_ctor_set(v_reuseFailAlloc_870_, 1, v_value_861_);
lean_ctor_set(v_reuseFailAlloc_870_, 2, v___x_867_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
else
{
lean_object* v___x_872_; 
lean_dec(v_value_861_);
lean_dec(v_key_860_);
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 1, v_b_858_);
lean_ctor_set(v___x_864_, 0, v_a_857_);
v___x_872_ = v___x_864_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_a_857_);
lean_ctor_set(v_reuseFailAlloc_873_, 1, v_b_858_);
lean_ctor_set(v_reuseFailAlloc_873_, 2, v_tail_862_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(lean_object* v_x_875_, lean_object* v_x_876_){
_start:
{
if (lean_obj_tag(v_x_876_) == 0)
{
return v_x_875_;
}
else
{
lean_object* v_key_877_; lean_object* v_value_878_; lean_object* v_tail_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_902_; 
v_key_877_ = lean_ctor_get(v_x_876_, 0);
v_value_878_ = lean_ctor_get(v_x_876_, 1);
v_tail_879_ = lean_ctor_get(v_x_876_, 2);
v_isSharedCheck_902_ = !lean_is_exclusive(v_x_876_);
if (v_isSharedCheck_902_ == 0)
{
v___x_881_ = v_x_876_;
v_isShared_882_ = v_isSharedCheck_902_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_tail_879_);
lean_inc(v_value_878_);
lean_inc(v_key_877_);
lean_dec(v_x_876_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_902_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_883_; uint64_t v___x_884_; uint64_t v___x_885_; uint64_t v___x_886_; uint64_t v_fold_887_; uint64_t v___x_888_; uint64_t v___x_889_; uint64_t v___x_890_; size_t v___x_891_; size_t v___x_892_; size_t v___x_893_; size_t v___x_894_; size_t v___x_895_; lean_object* v___x_896_; lean_object* v___x_898_; 
v___x_883_ = lean_array_get_size(v_x_875_);
v___x_884_ = l_Lean_ExprStructEq_hash(v_key_877_);
v___x_885_ = 32ULL;
v___x_886_ = lean_uint64_shift_right(v___x_884_, v___x_885_);
v_fold_887_ = lean_uint64_xor(v___x_884_, v___x_886_);
v___x_888_ = 16ULL;
v___x_889_ = lean_uint64_shift_right(v_fold_887_, v___x_888_);
v___x_890_ = lean_uint64_xor(v_fold_887_, v___x_889_);
v___x_891_ = lean_uint64_to_usize(v___x_890_);
v___x_892_ = lean_usize_of_nat(v___x_883_);
v___x_893_ = ((size_t)1ULL);
v___x_894_ = lean_usize_sub(v___x_892_, v___x_893_);
v___x_895_ = lean_usize_land(v___x_891_, v___x_894_);
v___x_896_ = lean_array_uget_borrowed(v_x_875_, v___x_895_);
lean_inc(v___x_896_);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 2, v___x_896_);
v___x_898_ = v___x_881_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_key_877_);
lean_ctor_set(v_reuseFailAlloc_901_, 1, v_value_878_);
lean_ctor_set(v_reuseFailAlloc_901_, 2, v___x_896_);
v___x_898_ = v_reuseFailAlloc_901_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
lean_object* v___x_899_; 
v___x_899_ = lean_array_uset(v_x_875_, v___x_895_, v___x_898_);
v_x_875_ = v___x_899_;
v_x_876_ = v_tail_879_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(lean_object* v_i_903_, lean_object* v_source_904_, lean_object* v_target_905_){
_start:
{
lean_object* v___x_906_; uint8_t v___x_907_; 
v___x_906_ = lean_array_get_size(v_source_904_);
v___x_907_ = lean_nat_dec_lt(v_i_903_, v___x_906_);
if (v___x_907_ == 0)
{
lean_dec_ref(v_source_904_);
lean_dec(v_i_903_);
return v_target_905_;
}
else
{
lean_object* v_es_908_; lean_object* v___x_909_; lean_object* v_source_910_; lean_object* v_target_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v_es_908_ = lean_array_fget(v_source_904_, v_i_903_);
v___x_909_ = lean_box(0);
v_source_910_ = lean_array_fset(v_source_904_, v_i_903_, v___x_909_);
v_target_911_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_target_905_, v_es_908_);
v___x_912_ = lean_unsigned_to_nat(1u);
v___x_913_ = lean_nat_add(v_i_903_, v___x_912_);
lean_dec(v_i_903_);
v_i_903_ = v___x_913_;
v_source_904_ = v_source_910_;
v_target_905_ = v_target_911_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11___redArg(lean_object* v_data_915_){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v_nbuckets_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_916_ = lean_array_get_size(v_data_915_);
v___x_917_ = lean_unsigned_to_nat(2u);
v_nbuckets_918_ = lean_nat_mul(v___x_916_, v___x_917_);
v___x_919_ = lean_unsigned_to_nat(0u);
v___x_920_ = lean_box(0);
v___x_921_ = lean_mk_array(v_nbuckets_918_, v___x_920_);
v___x_922_ = lean_array_propagate_mark(v_data_915_, v___x_921_);
v___x_923_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v___x_919_, v_data_915_, v___x_922_);
return v___x_923_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(lean_object* v_a_924_, lean_object* v_x_925_){
_start:
{
if (lean_obj_tag(v_x_925_) == 0)
{
uint8_t v___x_926_; 
v___x_926_ = 0;
return v___x_926_;
}
else
{
lean_object* v_key_927_; lean_object* v_tail_928_; uint8_t v___x_929_; 
v_key_927_ = lean_ctor_get(v_x_925_, 0);
v_tail_928_ = lean_ctor_get(v_x_925_, 2);
v___x_929_ = l_Lean_ExprStructEq_beq(v_key_927_, v_a_924_);
if (v___x_929_ == 0)
{
v_x_925_ = v_tail_928_;
goto _start;
}
else
{
return v___x_929_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg___boxed(lean_object* v_a_931_, lean_object* v_x_932_){
_start:
{
uint8_t v_res_933_; lean_object* v_r_934_; 
v_res_933_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(v_a_931_, v_x_932_);
lean_dec(v_x_932_);
lean_dec_ref(v_a_931_);
v_r_934_ = lean_box(v_res_933_);
return v_r_934_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6___redArg(lean_object* v_m_935_, lean_object* v_a_936_, lean_object* v_b_937_){
_start:
{
lean_object* v_size_938_; lean_object* v_buckets_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_982_; 
v_size_938_ = lean_ctor_get(v_m_935_, 0);
v_buckets_939_ = lean_ctor_get(v_m_935_, 1);
v_isSharedCheck_982_ = !lean_is_exclusive(v_m_935_);
if (v_isSharedCheck_982_ == 0)
{
v___x_941_ = v_m_935_;
v_isShared_942_ = v_isSharedCheck_982_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_buckets_939_);
lean_inc(v_size_938_);
lean_dec(v_m_935_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_982_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_943_; uint64_t v___x_944_; uint64_t v___x_945_; uint64_t v___x_946_; uint64_t v_fold_947_; uint64_t v___x_948_; uint64_t v___x_949_; uint64_t v___x_950_; size_t v___x_951_; size_t v___x_952_; size_t v___x_953_; size_t v___x_954_; size_t v___x_955_; lean_object* v_bkt_956_; uint8_t v___x_957_; 
v___x_943_ = lean_array_get_size(v_buckets_939_);
v___x_944_ = l_Lean_ExprStructEq_hash(v_a_936_);
v___x_945_ = 32ULL;
v___x_946_ = lean_uint64_shift_right(v___x_944_, v___x_945_);
v_fold_947_ = lean_uint64_xor(v___x_944_, v___x_946_);
v___x_948_ = 16ULL;
v___x_949_ = lean_uint64_shift_right(v_fold_947_, v___x_948_);
v___x_950_ = lean_uint64_xor(v_fold_947_, v___x_949_);
v___x_951_ = lean_uint64_to_usize(v___x_950_);
v___x_952_ = lean_usize_of_nat(v___x_943_);
v___x_953_ = ((size_t)1ULL);
v___x_954_ = lean_usize_sub(v___x_952_, v___x_953_);
v___x_955_ = lean_usize_land(v___x_951_, v___x_954_);
v_bkt_956_ = lean_array_uget_borrowed(v_buckets_939_, v___x_955_);
v___x_957_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(v_a_936_, v_bkt_956_);
if (v___x_957_ == 0)
{
lean_object* v___x_958_; lean_object* v_size_x27_959_; lean_object* v___x_960_; lean_object* v_buckets_x27_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; uint8_t v___x_967_; 
v___x_958_ = lean_unsigned_to_nat(1u);
v_size_x27_959_ = lean_nat_add(v_size_938_, v___x_958_);
lean_dec(v_size_938_);
lean_inc(v_bkt_956_);
v___x_960_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_960_, 0, v_a_936_);
lean_ctor_set(v___x_960_, 1, v_b_937_);
lean_ctor_set(v___x_960_, 2, v_bkt_956_);
v_buckets_x27_961_ = lean_array_uset(v_buckets_939_, v___x_955_, v___x_960_);
v___x_962_ = lean_unsigned_to_nat(4u);
v___x_963_ = lean_nat_mul(v_size_x27_959_, v___x_962_);
v___x_964_ = lean_unsigned_to_nat(3u);
v___x_965_ = lean_nat_div(v___x_963_, v___x_964_);
lean_dec(v___x_963_);
v___x_966_ = lean_array_get_size(v_buckets_x27_961_);
v___x_967_ = lean_nat_dec_le(v___x_965_, v___x_966_);
lean_dec(v___x_965_);
if (v___x_967_ == 0)
{
lean_object* v_val_968_; lean_object* v___x_970_; 
v_val_968_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11___redArg(v_buckets_x27_961_);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 1, v_val_968_);
lean_ctor_set(v___x_941_, 0, v_size_x27_959_);
v___x_970_ = v___x_941_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_size_x27_959_);
lean_ctor_set(v_reuseFailAlloc_971_, 1, v_val_968_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
else
{
lean_object* v___x_973_; 
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 1, v_buckets_x27_961_);
lean_ctor_set(v___x_941_, 0, v_size_x27_959_);
v___x_973_ = v___x_941_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_size_x27_959_);
lean_ctor_set(v_reuseFailAlloc_974_, 1, v_buckets_x27_961_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
else
{
lean_object* v___x_975_; lean_object* v_buckets_x27_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_980_; 
lean_inc(v_bkt_956_);
v___x_975_ = lean_box(0);
v_buckets_x27_976_ = lean_array_uset(v_buckets_939_, v___x_955_, v___x_975_);
v___x_977_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12___redArg(v_a_936_, v_b_937_, v_bkt_956_);
v___x_978_ = lean_array_uset(v_buckets_x27_976_, v___x_955_, v___x_977_);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 1, v___x_978_);
v___x_980_ = v___x_941_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_size_938_);
lean_ctor_set(v_reuseFailAlloc_981_, 1, v___x_978_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2(lean_object* v_a_983_, lean_object* v_e_984_, lean_object* v_a_985_){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_987_ = lean_st_ref_take(v_a_983_);
v___x_988_ = lean_box(0);
v___x_989_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6___redArg(v___x_987_, v_e_984_, v_a_985_);
v___x_990_ = lean_st_ref_put(v_a_983_, v___x_989_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2___boxed(lean_object* v_a_991_, lean_object* v_e_992_, lean_object* v_a_993_, lean_object* v___y_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2(v_a_991_, v_e_992_, v_a_993_);
lean_dec(v_a_991_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_996_, lean_object* v_x_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1001_ = lean_apply_1(v_x_997_, lean_box(0));
v___x_1002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1001_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1003_, lean_object* v_x_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_){
_start:
{
lean_object* v_res_1008_; 
v_res_1008_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(v_00_u03b1_1003_, v_x_1004_, v___y_1005_, v___y_1006_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
return v_res_1008_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0(void){
_start:
{
lean_object* v___x_1010_; lean_object* v_dummy_1011_; 
v___x_1010_ = lean_box(0);
v_dummy_1011_ = l_Lean_Expr_sort___override(v___x_1010_);
return v_dummy_1011_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1(lean_object* v_pre_1012_, lean_object* v_post_1013_, size_t v_sz_1014_, size_t v_i_1015_, lean_object* v_bs_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
uint8_t v___x_1021_; 
v___x_1021_ = lean_usize_dec_lt(v_i_1015_, v_sz_1014_);
if (v___x_1021_ == 0)
{
lean_object* v___x_1022_; 
lean_dec_ref(v_post_1013_);
lean_dec_ref(v_pre_1012_);
v___x_1022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1022_, 0, v_bs_1016_);
return v___x_1022_;
}
else
{
lean_object* v_v_1023_; lean_object* v___x_1024_; lean_object* v_bs_x27_1025_; lean_object* v___x_1026_; 
v_v_1023_ = lean_array_uget(v_bs_1016_, v_i_1015_);
v___x_1024_ = lean_unsigned_to_nat(0u);
v_bs_x27_1025_ = lean_array_uset(v_bs_1016_, v_i_1015_, v___x_1024_);
lean_inc_ref(v_post_1013_);
lean_inc_ref(v_pre_1012_);
v___x_1026_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1012_, v_post_1013_, v_v_1023_, v___y_1017_, v___y_1018_, v___y_1019_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v_a_1027_; size_t v___x_1028_; size_t v___x_1029_; lean_object* v___x_1030_; 
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
lean_inc(v_a_1027_);
lean_dec_ref_known(v___x_1026_, 1);
v___x_1028_ = ((size_t)1ULL);
v___x_1029_ = lean_usize_add(v_i_1015_, v___x_1028_);
v___x_1030_ = lean_array_uset(v_bs_x27_1025_, v_i_1015_, v_a_1027_);
v_i_1015_ = v___x_1029_;
v_bs_1016_ = v___x_1030_;
goto _start;
}
else
{
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1039_; 
lean_dec_ref(v_bs_x27_1025_);
lean_dec_ref(v_post_1013_);
lean_dec_ref(v_pre_1012_);
v_a_1032_ = lean_ctor_get(v___x_1026_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1034_ = v___x_1026_;
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_1026_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1037_; 
if (v_isShared_1035_ == 0)
{
v___x_1037_ = v___x_1034_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_a_1032_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4(lean_object* v_pre_1040_, lean_object* v_post_1041_, lean_object* v_x_1042_, lean_object* v_x_1043_, lean_object* v_x_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_){
_start:
{
if (lean_obj_tag(v_x_1042_) == 5)
{
lean_object* v_fn_1049_; lean_object* v_arg_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
v_fn_1049_ = lean_ctor_get(v_x_1042_, 0);
lean_inc_ref(v_fn_1049_);
v_arg_1050_ = lean_ctor_get(v_x_1042_, 1);
lean_inc_ref(v_arg_1050_);
lean_dec_ref_known(v_x_1042_, 2);
v___x_1051_ = lean_array_set(v_x_1043_, v_x_1044_, v_arg_1050_);
v___x_1052_ = lean_unsigned_to_nat(1u);
v___x_1053_ = lean_nat_sub(v_x_1044_, v___x_1052_);
lean_dec(v_x_1044_);
v_x_1042_ = v_fn_1049_;
v_x_1043_ = v___x_1051_;
v_x_1044_ = v___x_1053_;
goto _start;
}
else
{
lean_object* v___x_1055_; 
lean_dec(v_x_1044_);
lean_inc_ref(v_post_1041_);
lean_inc_ref(v_pre_1040_);
v___x_1055_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1040_, v_post_1041_, v_x_1042_, v___y_1045_, v___y_1046_, v___y_1047_);
if (lean_obj_tag(v___x_1055_) == 0)
{
lean_object* v_a_1056_; size_t v_sz_1057_; size_t v___x_1058_; lean_object* v___x_1059_; 
v_a_1056_ = lean_ctor_get(v___x_1055_, 0);
lean_inc(v_a_1056_);
lean_dec_ref_known(v___x_1055_, 1);
v_sz_1057_ = lean_array_size(v_x_1043_);
v___x_1058_ = ((size_t)0ULL);
lean_inc_ref(v_post_1041_);
lean_inc_ref(v_pre_1040_);
v___x_1059_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1(v_pre_1040_, v_post_1041_, v_sz_1057_, v___x_1058_, v_x_1043_, v___y_1045_, v___y_1046_, v___y_1047_);
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_object* v_a_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; 
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
lean_inc(v_a_1060_);
lean_dec_ref_known(v___x_1059_, 1);
v___x_1061_ = l_Lean_mkAppN(v_a_1056_, v_a_1060_);
lean_dec(v_a_1060_);
v___x_1062_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1040_, v_post_1041_, v___x_1061_, v___y_1045_, v___y_1046_, v___y_1047_);
return v___x_1062_;
}
else
{
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1070_; 
lean_dec(v_a_1056_);
lean_dec_ref(v_post_1041_);
lean_dec_ref(v_pre_1040_);
v_a_1063_ = lean_ctor_get(v___x_1059_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1065_ = v___x_1059_;
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_1059_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1068_; 
if (v_isShared_1066_ == 0)
{
v___x_1068_ = v___x_1065_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_a_1063_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
}
else
{
lean_dec_ref(v_x_1043_);
lean_dec_ref(v_post_1041_);
lean_dec_ref(v_pre_1040_);
return v___x_1055_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1(lean_object* v___x_1071_, lean_object* v_pre_1072_, lean_object* v_e_1073_, lean_object* v_post_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_){
_start:
{
lean_object* v___x_1079_; 
v___x_1079_ = l_Lean_Core_checkSystem(v___x_1071_, v___y_1076_, v___y_1077_);
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v___x_1080_; 
lean_dec_ref_known(v___x_1079_, 1);
lean_inc_ref(v_pre_1072_);
lean_inc(v___y_1077_);
lean_inc_ref(v___y_1076_);
lean_inc_ref(v_e_1073_);
v___x_1080_ = lean_apply_4(v_pre_1072_, v_e_1073_, v___y_1076_, v___y_1077_, lean_box(0));
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v_a_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1196_; 
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1083_ = v___x_1080_;
v_isShared_1084_ = v_isSharedCheck_1196_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_a_1081_);
lean_dec(v___x_1080_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1196_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___y_1086_; 
switch(lean_obj_tag(v_a_1081_))
{
case 0:
{
lean_object* v_e_1186_; lean_object* v___x_1188_; 
lean_dec_ref(v_post_1074_);
lean_dec_ref(v_e_1073_);
lean_dec_ref(v_pre_1072_);
v_e_1186_ = lean_ctor_get(v_a_1081_, 0);
lean_inc_ref(v_e_1186_);
lean_dec_ref_known(v_a_1081_, 1);
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 0, v_e_1186_);
v___x_1188_ = v___x_1083_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_e_1186_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
case 1:
{
lean_object* v_e_1190_; lean_object* v___x_1191_; 
lean_del_object(v___x_1083_);
lean_dec_ref(v_e_1073_);
v_e_1190_ = lean_ctor_get(v_a_1081_, 0);
lean_inc_ref(v_e_1190_);
lean_dec_ref_known(v_a_1081_, 1);
lean_inc_ref(v_post_1074_);
lean_inc_ref(v_pre_1072_);
v___x_1191_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1072_, v_post_1074_, v_e_1190_, v___y_1075_, v___y_1076_, v___y_1077_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v_a_1192_; lean_object* v___x_1193_; 
v_a_1192_ = lean_ctor_get(v___x_1191_, 0);
lean_inc(v_a_1192_);
lean_dec_ref_known(v___x_1191_, 1);
v___x_1193_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1072_, v_post_1074_, v_a_1192_, v___y_1075_, v___y_1076_, v___y_1077_);
return v___x_1193_;
}
else
{
lean_dec_ref(v_post_1074_);
lean_dec_ref(v_pre_1072_);
return v___x_1191_;
}
}
default: 
{
lean_object* v_e_x3f_1194_; 
lean_del_object(v___x_1083_);
v_e_x3f_1194_ = lean_ctor_get(v_a_1081_, 0);
lean_inc(v_e_x3f_1194_);
lean_dec_ref_known(v_a_1081_, 1);
if (lean_obj_tag(v_e_x3f_1194_) == 0)
{
v___y_1086_ = v_e_1073_;
goto v___jp_1085_;
}
else
{
lean_object* v_val_1195_; 
lean_dec_ref(v_e_1073_);
v_val_1195_ = lean_ctor_get(v_e_x3f_1194_, 0);
lean_inc(v_val_1195_);
lean_dec_ref_known(v_e_x3f_1194_, 1);
v___y_1086_ = v_val_1195_;
goto v___jp_1085_;
}
}
}
v___jp_1085_:
{
switch(lean_obj_tag(v___y_1086_))
{
case 7:
{
lean_object* v_binderName_1087_; lean_object* v_binderType_1088_; lean_object* v_body_1089_; uint8_t v_binderInfo_1090_; lean_object* v___x_1091_; 
v_binderName_1087_ = lean_ctor_get(v___y_1086_, 0);
v_binderType_1088_ = lean_ctor_get(v___y_1086_, 1);
v_body_1089_ = lean_ctor_get(v___y_1086_, 2);
v_binderInfo_1090_ = lean_ctor_get_uint8(v___y_1086_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1088_);
lean_inc_ref(v_post_1074_);
lean_inc_ref(v_pre_1072_);
v___x_1091_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1072_, v_post_1074_, v_binderType_1088_, v___y_1075_, v___y_1076_, v___y_1077_);
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_object* v_a_1092_; lean_object* v___x_1093_; 
v_a_1092_ = lean_ctor_get(v___x_1091_, 0);
lean_inc(v_a_1092_);
lean_dec_ref_known(v___x_1091_, 1);
lean_inc_ref(v_body_1089_);
lean_inc_ref(v_post_1074_);
lean_inc_ref(v_pre_1072_);
v___x_1093_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1072_, v_post_1074_, v_body_1089_, v___y_1075_, v___y_1076_, v___y_1077_);
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_object* v_a_1094_; size_t v___x_1095_; size_t v___x_1096_; uint8_t v___x_1097_; 
v_a_1094_ = lean_ctor_get(v___x_1093_, 0);
lean_inc(v_a_1094_);
lean_dec_ref_known(v___x_1093_, 1);
v___x_1095_ = lean_ptr_addr(v_binderType_1088_);
v___x_1096_ = lean_ptr_addr(v_a_1092_);
v___x_1097_ = lean_usize_dec_eq(v___x_1095_, v___x_1096_);
if (v___x_1097_ == 0)
{
lean_object* v___x_1098_; lean_object* v___x_1099_; 
lean_inc(v_binderName_1087_);
lean_dec_ref_known(v___y_1086_, 3);
v___x_1098_ = l_Lean_Expr_forallE___override(v_binderName_1087_, v_a_1092_, v_a_1094_, v_binderInfo_1090_);
v___x_1099_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1072_, v_post_1074_, v___x_1098_, v___y_1075_, v___y_1076_, v___y_1077_);
return v___x_1099_;
}
else
{
size_t v___x_1100_; size_t v___x_1101_; uint8_t v___x_1102_; 
v___x_1100_ = lean_ptr_addr(v_body_1089_);
v___x_1101_ = lean_ptr_addr(v_a_1094_);
v___x_1102_ = lean_usize_dec_eq(v___x_1100_, v___x_1101_);
if (v___x_1102_ == 0)
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
lean_inc(v_binderName_1087_);
lean_dec_ref_known(v___y_1086_, 3);
v___x_1103_ = l_Lean_Expr_forallE___override(v_binderName_1087_, v_a_1092_, v_a_1094_, v_binderInfo_1090_);
v___x_1104_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1072_, v_post_1074_, v___x_1103_, v___y_1075_, v___y_1076_, v___y_1077_);
return v___x_1104_;
}
else
{
uint8_t v___x_1105_; 
v___x_1105_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1090_, v_binderInfo_1090_);
if (v___x_1105_ == 0)
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
lean_inc(v_binderName_1087_);
lean_dec_ref_known(v___y_1086_, 3);
v___x_1106_ = l_Lean_Expr_forallE___override(v_binderName_1087_, v_a_1092_, v_a_1094_, v_binderInfo_1090_);
v___x_1107_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1072_, v_post_1074_, v___x_1106_, v___y_1075_, v___y_1076_, v___y_1077_);
return v___x_1107_;
}
else
{
lean_object* v___x_1108_; 
lean_dec(v_a_1094_);
lean_dec(v_a_1092_);
v___x_1108_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1072_, v_post_1074_, v___y_1086_, v___y_1075_, v___y_1076_, v___y_1077_);
return v___x_1108_;
}
}
}
}
else
{
lean_dec(v_a_1092_);
lean_dec_ref_known(v___y_1086_, 3);
lean_dec_ref(v_post_1074_);
lean_dec_ref(v_pre_1072_);
return v___x_1093_;
}
}
else
{
lean_dec_ref_known(v___y_1086_, 3);
lean_dec_ref(v_post_1074_);
lean_dec_ref(v_pre_1072_);
return v___x_1091_;
}
}
case 6:
{
lean_object* v_binderName_1109_; lean_object* v_binderType_1110_; lean_object* v_body_1111_; uint8_t v_binderInfo_1112_; lean_object* v___x_1113_; 
v_binderName_1109_ = lean_ctor_get(v___y_1086_, 0);
v_binderType_1110_ = lean_ctor_get(v___y_1086_, 1);
v_body_1111_ = lean_ctor_get(v___y_1086_, 2);
v_binderInfo_1112_ = lean_ctor_get_uint8(v___y_1086_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1110_);
lean_inc_ref(v_post_1074_);
lean_inc_ref(v_pre_1072_);
v___x_1113_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1072_, v_post_1074_, v_binderType_1110_, v___y_1075_, v___y_1076_, v___y_1077_);
if (lean_obj_tag(v___x_1113_) == 0)
{
lean_object* v_a_1114_; lean_object* v___x_1115_; 
v_a_1114_ = lean_ctor_get(v___x_1113_, 0);
lean_inc(v_a_1114_);
lean_dec_ref_known(v___x_1113_, 1);
lean_inc_ref(v_body_1111_);
lean_inc_ref(v_post_1074_);
lean_inc_ref(v_pre_1072_);
v___x_1115_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1072_, v_post_1074_, v_body_1111_, v___y_1075_, v___y_1076_, v___y_1077_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v_a_1116_; size_t v___x_1117_; size_t v___x_1118_; uint8_t v___x_1119_; 
v_a_1116_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_a_1116_);
lean_dec_ref_known(v___x_1115_, 1);
v___x_1117_ = lean_ptr_addr(v_binderType_1110_);
v___x_1118_ = lean_ptr_addr(v_a_1114_);
v___x_1119_ = lean_usize_dec_eq(v___x_1117_, v___x_1118_);
if (v___x_1119_ == 0)
{
lean_object* v___x_1120_; lean_object* v___x_1121_; 
lean_inc(v_binderName_1109_);
lean_dec_ref_known(v___y_1086_, 3);
v___x_1120_ = l_Lean_Expr_lam___override(v_binderName_1109_, v_a_1114_, v_a_1116_, v_binderInfo_1112_);
v___x_1121_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1072_, v_post_1074_, v___x_1120_, v___y_1075_, v___y_1076_, v___y_1077_);
return v___x_1121_;
}
else
{
size_t v___x_1122_; size_t v___x_1123_; uint8_t v___x_1124_; 
v___x_1122_ = lean_ptr_addr(v_body_1111_);
v___x_1123_ = lean_ptr_addr(v_a_1116_);
v___x_1124_ = lean_usize_dec_eq(v___x_1122_, v___x_1123_);
if (v___x_1124_ == 0)
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
lean_inc(v_binderName_1109_);
lean_dec_ref_known(v___y_1086_, 3);
v___x_1125_ = l_Lean_Expr_lam___override(v_binderName_1109_, v_a_1114_, v_a_1116_, v_binderInfo_1112_);
v___x_1126_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1072_, v_post_1074_, v___x_1125_, v___y_1075_, v___y_1076_, v___y_1077_);
return v___x_1126_;
}
else
{
uint8_t v___x_1127_; 
v___x_1127_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1112_, v_binderInfo_1112_);
if (v___x_1127_ == 0)
{
lean_object* v___x_1128_; lean_object* v___x_1129_; 
lean_inc(v_binderName_1109_);
lean_dec_ref_known(v___y_1086_, 3);
v___x_1128_ = l_Lean_Expr_lam___override(v_binderName_1109_, v_a_1114_, v_a_1116_, v_binderInfo_1112_);
v___x_1129_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1072_, v_post_1074_, v___x_1128_, v___y_1075_, v___y_1076_, v___y_1077_);
return v___x_1129_;
}
else
{
lean_object* v___x_1130_; 
lean_dec(v_a_1116_);
lean_dec(v_a_1114_);
v___x_1130_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1072_, v_post_1074_, v___y_1086_, v___y_1075_, v___y_1076_, v___y_1077_);
return v___x_1130_;
}
}
}
}
else
{
lean_dec(v_a_1114_);
lean_dec_ref_known(v___y_1086_, 3);
lean_dec_ref(v_post_1074_);
lean_dec_ref(v_pre_1072_);
return v___x_1115_;
}
}
else
{
lean_dec_ref_known(v___y_1086_, 3);
lean_dec_ref(v_post_1074_);
lean_dec_ref(v_pre_1072_);
return v___x_1113_;
}
}
case 8:
{
lean_object* v_declName_1131_; lean_object* v_type_1132_; lean_object* v_value_1133_; lean_object* v_body_1134_; uint8_t v_nondep_1135_; lean_object* v___x_1136_; 
v_declName_1131_ = lean_ctor_get(v___y_1086_, 0);
v_type_1132_ = lean_ctor_get(v___y_1086_, 1);
v_value_1133_ = lean_ctor_get(v___y_1086_, 2);
v_body_1134_ = lean_ctor_get(v___y_1086_, 3);
v_nondep_1135_ = lean_ctor_get_uint8(v___y_1086_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_1132_);
lean_inc_ref(v_post_1074_);
lean_inc_ref(v_pre_1072_);
v___x_1136_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1072_, v_post_1074_, v_type_1132_, v___y_1075_, v___y_1076_, v___y_1077_);
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_object* v_a_1137_; lean_object* v___x_1138_; 
v_a_1137_ = lean_ctor_get(v___x_1136_, 0);
lean_inc(v_a_1137_);
lean_dec_ref_known(v___x_1136_, 1);
lean_inc_ref(v_value_1133_);
lean_inc_ref(v_post_1074_);
lean_inc_ref(v_pre_1072_);
v___x_1138_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1072_, v_post_1074_, v_value_1133_, v___y_1075_, v___y_1076_, v___y_1077_);
if (lean_obj_tag(v___x_1138_) == 0)
{
lean_object* v_a_1139_; lean_object* v___x_1140_; 
v_a_1139_ = lean_ctor_get(v___x_1138_, 0);
lean_inc(v_a_1139_);
lean_dec_ref_known(v___x_1138_, 1);
lean_inc_ref(v_body_1134_);
lean_inc_ref(v_post_1074_);
lean_inc_ref(v_pre_1072_);
v___x_1140_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1072_, v_post_1074_, v_body_1134_, v___y_1075_, v___y_1076_, v___y_1077_);
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_object* v_a_1141_; size_t v___x_1142_; size_t v___x_1143_; uint8_t v___x_1144_; 
v_a_1141_ = lean_ctor_get(v___x_1140_, 0);
lean_inc(v_a_1141_);
lean_dec_ref_known(v___x_1140_, 1);
v___x_1142_ = lean_ptr_addr(v_type_1132_);
v___x_1143_ = lean_ptr_addr(v_a_1137_);
v___x_1144_ = lean_usize_dec_eq(v___x_1142_, v___x_1143_);
if (v___x_1144_ == 0)
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
lean_inc(v_declName_1131_);
lean_dec_ref_known(v___y_1086_, 4);
v___x_1145_ = l_Lean_Expr_letE___override(v_declName_1131_, v_a_1137_, v_a_1139_, v_a_1141_, v_nondep_1135_);
v___x_1146_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1072_, v_post_1074_, v___x_1145_, v___y_1075_, v___y_1076_, v___y_1077_);
return v___x_1146_;
}
else
{
size_t v___x_1147_; size_t v___x_1148_; uint8_t v___x_1149_; 
v___x_1147_ = lean_ptr_addr(v_value_1133_);
v___x_1148_ = lean_ptr_addr(v_a_1139_);
v___x_1149_ = lean_usize_dec_eq(v___x_1147_, v___x_1148_);
if (v___x_1149_ == 0)
{
lean_object* v___x_1150_; lean_object* v___x_1151_; 
lean_inc(v_declName_1131_);
lean_dec_ref_known(v___y_1086_, 4);
v___x_1150_ = l_Lean_Expr_letE___override(v_declName_1131_, v_a_1137_, v_a_1139_, v_a_1141_, v_nondep_1135_);
v___x_1151_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1072_, v_post_1074_, v___x_1150_, v___y_1075_, v___y_1076_, v___y_1077_);
return v___x_1151_;
}
else
{
size_t v___x_1152_; size_t v___x_1153_; uint8_t v___x_1154_; 
v___x_1152_ = lean_ptr_addr(v_body_1134_);
v___x_1153_ = lean_ptr_addr(v_a_1141_);
v___x_1154_ = lean_usize_dec_eq(v___x_1152_, v___x_1153_);
if (v___x_1154_ == 0)
{
lean_object* v___x_1155_; lean_object* v___x_1156_; 
lean_inc(v_declName_1131_);
lean_dec_ref_known(v___y_1086_, 4);
v___x_1155_ = l_Lean_Expr_letE___override(v_declName_1131_, v_a_1137_, v_a_1139_, v_a_1141_, v_nondep_1135_);
v___x_1156_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1072_, v_post_1074_, v___x_1155_, v___y_1075_, v___y_1076_, v___y_1077_);
return v___x_1156_;
}
else
{
lean_object* v___x_1157_; 
lean_dec(v_a_1141_);
lean_dec(v_a_1139_);
lean_dec(v_a_1137_);
v___x_1157_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1072_, v_post_1074_, v___y_1086_, v___y_1075_, v___y_1076_, v___y_1077_);
return v___x_1157_;
}
}
}
}
else
{
lean_dec(v_a_1139_);
lean_dec(v_a_1137_);
lean_dec_ref_known(v___y_1086_, 4);
lean_dec_ref(v_post_1074_);
lean_dec_ref(v_pre_1072_);
return v___x_1140_;
}
}
else
{
lean_dec(v_a_1137_);
lean_dec_ref_known(v___y_1086_, 4);
lean_dec_ref(v_post_1074_);
lean_dec_ref(v_pre_1072_);
return v___x_1138_;
}
}
else
{
lean_dec_ref_known(v___y_1086_, 4);
lean_dec_ref(v_post_1074_);
lean_dec_ref(v_pre_1072_);
return v___x_1136_;
}
}
case 5:
{
lean_object* v_dummy_1158_; lean_object* v_nargs_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
v_dummy_1158_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0);
v_nargs_1159_ = l_Lean_Expr_getAppNumArgs(v___y_1086_);
lean_inc(v_nargs_1159_);
v___x_1160_ = lean_mk_array(v_nargs_1159_, v_dummy_1158_);
v___x_1161_ = lean_unsigned_to_nat(1u);
v___x_1162_ = lean_nat_sub(v_nargs_1159_, v___x_1161_);
lean_dec(v_nargs_1159_);
v___x_1163_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4(v_pre_1072_, v_post_1074_, v___y_1086_, v___x_1160_, v___x_1162_, v___y_1075_, v___y_1076_, v___y_1077_);
return v___x_1163_;
}
case 10:
{
lean_object* v_data_1164_; lean_object* v_expr_1165_; lean_object* v___x_1166_; 
v_data_1164_ = lean_ctor_get(v___y_1086_, 0);
v_expr_1165_ = lean_ctor_get(v___y_1086_, 1);
lean_inc_ref(v_expr_1165_);
lean_inc_ref(v_post_1074_);
lean_inc_ref(v_pre_1072_);
v___x_1166_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1072_, v_post_1074_, v_expr_1165_, v___y_1075_, v___y_1076_, v___y_1077_);
if (lean_obj_tag(v___x_1166_) == 0)
{
lean_object* v_a_1167_; size_t v___x_1168_; size_t v___x_1169_; uint8_t v___x_1170_; 
v_a_1167_ = lean_ctor_get(v___x_1166_, 0);
lean_inc(v_a_1167_);
lean_dec_ref_known(v___x_1166_, 1);
v___x_1168_ = lean_ptr_addr(v_expr_1165_);
v___x_1169_ = lean_ptr_addr(v_a_1167_);
v___x_1170_ = lean_usize_dec_eq(v___x_1168_, v___x_1169_);
if (v___x_1170_ == 0)
{
lean_object* v___x_1171_; lean_object* v___x_1172_; 
lean_inc(v_data_1164_);
lean_dec_ref_known(v___y_1086_, 2);
v___x_1171_ = l_Lean_Expr_mdata___override(v_data_1164_, v_a_1167_);
v___x_1172_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1072_, v_post_1074_, v___x_1171_, v___y_1075_, v___y_1076_, v___y_1077_);
return v___x_1172_;
}
else
{
lean_object* v___x_1173_; 
lean_dec(v_a_1167_);
v___x_1173_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1072_, v_post_1074_, v___y_1086_, v___y_1075_, v___y_1076_, v___y_1077_);
return v___x_1173_;
}
}
else
{
lean_dec_ref_known(v___y_1086_, 2);
lean_dec_ref(v_post_1074_);
lean_dec_ref(v_pre_1072_);
return v___x_1166_;
}
}
case 11:
{
lean_object* v_typeName_1174_; lean_object* v_idx_1175_; lean_object* v_struct_1176_; lean_object* v___x_1177_; 
v_typeName_1174_ = lean_ctor_get(v___y_1086_, 0);
v_idx_1175_ = lean_ctor_get(v___y_1086_, 1);
v_struct_1176_ = lean_ctor_get(v___y_1086_, 2);
lean_inc_ref(v_struct_1176_);
lean_inc_ref(v_post_1074_);
lean_inc_ref(v_pre_1072_);
v___x_1177_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1072_, v_post_1074_, v_struct_1176_, v___y_1075_, v___y_1076_, v___y_1077_);
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v_a_1178_; size_t v___x_1179_; size_t v___x_1180_; uint8_t v___x_1181_; 
v_a_1178_ = lean_ctor_get(v___x_1177_, 0);
lean_inc(v_a_1178_);
lean_dec_ref_known(v___x_1177_, 1);
v___x_1179_ = lean_ptr_addr(v_struct_1176_);
v___x_1180_ = lean_ptr_addr(v_a_1178_);
v___x_1181_ = lean_usize_dec_eq(v___x_1179_, v___x_1180_);
if (v___x_1181_ == 0)
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
lean_inc(v_idx_1175_);
lean_inc(v_typeName_1174_);
lean_dec_ref_known(v___y_1086_, 3);
v___x_1182_ = l_Lean_Expr_proj___override(v_typeName_1174_, v_idx_1175_, v_a_1178_);
v___x_1183_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1072_, v_post_1074_, v___x_1182_, v___y_1075_, v___y_1076_, v___y_1077_);
return v___x_1183_;
}
else
{
lean_object* v___x_1184_; 
lean_dec(v_a_1178_);
v___x_1184_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1072_, v_post_1074_, v___y_1086_, v___y_1075_, v___y_1076_, v___y_1077_);
return v___x_1184_;
}
}
else
{
lean_dec_ref_known(v___y_1086_, 3);
lean_dec_ref(v_post_1074_);
lean_dec_ref(v_pre_1072_);
return v___x_1177_;
}
}
default: 
{
lean_object* v___x_1185_; 
v___x_1185_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1072_, v_post_1074_, v___y_1086_, v___y_1075_, v___y_1076_, v___y_1077_);
return v___x_1185_;
}
}
}
}
}
else
{
lean_object* v_a_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1204_; 
lean_dec_ref(v_post_1074_);
lean_dec_ref(v_e_1073_);
lean_dec_ref(v_pre_1072_);
v_a_1197_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1199_ = v___x_1080_;
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_a_1197_);
lean_dec(v___x_1080_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1202_; 
if (v_isShared_1200_ == 0)
{
v___x_1202_ = v___x_1199_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_a_1197_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
else
{
lean_object* v_a_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1212_; 
lean_dec_ref(v_post_1074_);
lean_dec_ref(v_e_1073_);
lean_dec_ref(v_pre_1072_);
v_a_1205_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1207_ = v___x_1079_;
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_a_1205_);
lean_dec(v___x_1079_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1210_; 
if (v_isShared_1208_ == 0)
{
v___x_1210_ = v___x_1207_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_a_1205_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___boxed(lean_object* v___x_1213_, lean_object* v_pre_1214_, lean_object* v_e_1215_, lean_object* v_post_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_){
_start:
{
lean_object* v_res_1221_; 
v_res_1221_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1(v___x_1213_, v_pre_1214_, v_e_1215_, v_post_1216_, v___y_1217_, v___y_1218_, v___y_1219_);
lean_dec(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec(v___y_1217_);
return v_res_1221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(lean_object* v_pre_1222_, lean_object* v_post_1223_, lean_object* v_e_1224_, lean_object* v_a_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; 
lean_inc(v_a_1225_);
v___x_1229_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1229_, 0, lean_box(0));
lean_closure_set(v___x_1229_, 1, lean_box(0));
lean_closure_set(v___x_1229_, 2, v_a_1225_);
v___x_1230_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(lean_box(0), v___x_1229_, v___y_1226_, v___y_1227_);
if (lean_obj_tag(v___x_1230_) == 0)
{
lean_object* v_a_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1262_; 
v_a_1231_ = lean_ctor_get(v___x_1230_, 0);
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1233_ = v___x_1230_;
v_isShared_1234_ = v_isSharedCheck_1262_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_a_1231_);
lean_dec(v___x_1230_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1262_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1235_; 
v___x_1235_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg(v_a_1231_, v_e_1224_);
lean_dec(v_a_1231_);
if (lean_obj_tag(v___x_1235_) == 0)
{
lean_object* v___x_1236_; lean_object* v___f_1237_; lean_object* v___x_1238_; 
lean_del_object(v___x_1233_);
v___x_1236_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___closed__0));
lean_inc_ref(v_e_1224_);
v___f_1237_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___boxed), 8, 4);
lean_closure_set(v___f_1237_, 0, v___x_1236_);
lean_closure_set(v___f_1237_, 1, v_pre_1222_);
lean_closure_set(v___f_1237_, 2, v_e_1224_);
lean_closure_set(v___f_1237_, 3, v_post_1223_);
v___x_1238_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg(v___f_1237_, v_a_1225_, v___y_1226_, v___y_1227_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v_a_1239_; lean_object* v___f_1240_; lean_object* v___x_1241_; 
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
lean_inc_n(v_a_1239_, 2);
lean_dec_ref_known(v___x_1238_, 1);
lean_inc(v_a_1225_);
v___f_1240_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1240_, 0, v_a_1225_);
lean_closure_set(v___f_1240_, 1, v_e_1224_);
lean_closure_set(v___f_1240_, 2, v_a_1239_);
v___x_1241_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(lean_box(0), v___f_1240_, v___y_1226_, v___y_1227_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1248_; 
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1248_ == 0)
{
lean_object* v_unused_1249_; 
v_unused_1249_ = lean_ctor_get(v___x_1241_, 0);
lean_dec(v_unused_1249_);
v___x_1243_ = v___x_1241_;
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
else
{
lean_dec(v___x_1241_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1246_; 
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 0, v_a_1239_);
v___x_1246_ = v___x_1243_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_a_1239_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
else
{
lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1257_; 
lean_dec(v_a_1239_);
v_a_1250_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1252_ = v___x_1241_;
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_1241_);
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
}
else
{
lean_dec_ref(v_e_1224_);
return v___x_1238_;
}
}
else
{
lean_object* v_val_1258_; lean_object* v___x_1260_; 
lean_dec_ref(v_e_1224_);
lean_dec_ref(v_post_1223_);
lean_dec_ref(v_pre_1222_);
v_val_1258_ = lean_ctor_get(v___x_1235_, 0);
lean_inc(v_val_1258_);
lean_dec_ref_known(v___x_1235_, 1);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 0, v_val_1258_);
v___x_1260_ = v___x_1233_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v_val_1258_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
}
else
{
lean_object* v_a_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1270_; 
lean_dec_ref(v_e_1224_);
lean_dec_ref(v_post_1223_);
lean_dec_ref(v_pre_1222_);
v_a_1263_ = lean_ctor_get(v___x_1230_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1265_ = v___x_1230_;
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_a_1263_);
lean_dec(v___x_1230_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1268_; 
if (v_isShared_1266_ == 0)
{
v___x_1268_ = v___x_1265_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_a_1263_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(lean_object* v_pre_1271_, lean_object* v_post_1272_, lean_object* v_e_1273_, lean_object* v_a_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_){
_start:
{
lean_object* v___x_1278_; 
lean_inc_ref(v_post_1272_);
lean_inc(v___y_1276_);
lean_inc_ref(v___y_1275_);
lean_inc_ref(v_e_1273_);
v___x_1278_ = lean_apply_4(v_post_1272_, v_e_1273_, v___y_1275_, v___y_1276_, lean_box(0));
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v_a_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1297_; 
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1281_ = v___x_1278_;
v_isShared_1282_ = v_isSharedCheck_1297_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_a_1279_);
lean_dec(v___x_1278_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1297_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
switch(lean_obj_tag(v_a_1279_))
{
case 0:
{
lean_object* v_e_1283_; lean_object* v___x_1285_; 
lean_dec_ref(v_e_1273_);
lean_dec_ref(v_post_1272_);
lean_dec_ref(v_pre_1271_);
v_e_1283_ = lean_ctor_get(v_a_1279_, 0);
lean_inc_ref(v_e_1283_);
lean_dec_ref_known(v_a_1279_, 1);
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 0, v_e_1283_);
v___x_1285_ = v___x_1281_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_e_1283_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
case 1:
{
lean_object* v_e_1287_; lean_object* v___x_1288_; 
lean_del_object(v___x_1281_);
lean_dec_ref(v_e_1273_);
v_e_1287_ = lean_ctor_get(v_a_1279_, 0);
lean_inc_ref(v_e_1287_);
lean_dec_ref_known(v_a_1279_, 1);
v___x_1288_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1271_, v_post_1272_, v_e_1287_, v_a_1274_, v___y_1275_, v___y_1276_);
return v___x_1288_;
}
default: 
{
lean_object* v_e_x3f_1289_; 
lean_dec_ref(v_post_1272_);
lean_dec_ref(v_pre_1271_);
v_e_x3f_1289_ = lean_ctor_get(v_a_1279_, 0);
lean_inc(v_e_x3f_1289_);
lean_dec_ref_known(v_a_1279_, 1);
if (lean_obj_tag(v_e_x3f_1289_) == 0)
{
lean_object* v___x_1291_; 
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 0, v_e_1273_);
v___x_1291_ = v___x_1281_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_e_1273_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
else
{
lean_object* v_val_1293_; lean_object* v___x_1295_; 
lean_dec_ref(v_e_1273_);
v_val_1293_ = lean_ctor_get(v_e_x3f_1289_, 0);
lean_inc(v_val_1293_);
lean_dec_ref_known(v_e_x3f_1289_, 1);
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 0, v_val_1293_);
v___x_1295_ = v___x_1281_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_val_1293_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
}
}
}
else
{
lean_object* v_a_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1305_; 
lean_dec_ref(v_e_1273_);
lean_dec_ref(v_post_1272_);
lean_dec_ref(v_pre_1271_);
v_a_1298_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1300_ = v___x_1278_;
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_a_1298_);
lean_dec(v___x_1278_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1303_; 
if (v_isShared_1301_ == 0)
{
v___x_1303_ = v___x_1300_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_a_1298_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_1306_, lean_object* v_post_1307_, lean_object* v_e_1308_, lean_object* v_a_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1306_, v_post_1307_, v_e_1308_, v_a_1309_, v___y_1310_, v___y_1311_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec(v_a_1309_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_1314_, lean_object* v_post_1315_, lean_object* v_sz_1316_, lean_object* v_i_1317_, lean_object* v_bs_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
size_t v_sz_boxed_1323_; size_t v_i_boxed_1324_; lean_object* v_res_1325_; 
v_sz_boxed_1323_ = lean_unbox_usize(v_sz_1316_);
lean_dec(v_sz_1316_);
v_i_boxed_1324_ = lean_unbox_usize(v_i_1317_);
lean_dec(v_i_1317_);
v_res_1325_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1(v_pre_1314_, v_post_1315_, v_sz_boxed_1323_, v_i_boxed_1324_, v_bs_1318_, v___y_1319_, v___y_1320_, v___y_1321_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec(v___y_1319_);
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_1326_, lean_object* v_post_1327_, lean_object* v_x_1328_, lean_object* v_x_1329_, lean_object* v_x_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4(v_pre_1326_, v_post_1327_, v_x_1328_, v_x_1329_, v_x_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v___y_1331_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___boxed(lean_object* v_pre_1336_, lean_object* v_post_1337_, lean_object* v_e_1338_, lean_object* v_a_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1336_, v_post_1337_, v_e_1338_, v_a_1339_, v___y_1340_, v___y_1341_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v_a_1339_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(lean_object* v_00_u03b1_1344_, lean_object* v_x_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_){
_start:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___x_1349_ = lean_apply_1(v_x_1345_, lean_box(0));
v___x_1350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1349_);
return v___x_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1351_, lean_object* v_x_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
lean_object* v_res_1356_; 
v_res_1356_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(v_00_u03b1_1351_, v_x_1352_, v___y_1353_, v___y_1354_);
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
return v_res_1356_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1357_ = lean_box(0);
v___x_1358_ = lean_unsigned_to_nat(16u);
v___x_1359_ = lean_mk_array(v___x_1358_, v___x_1357_);
return v___x_1359_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1360_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0, &l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0);
v___x_1361_ = lean_unsigned_to_nat(0u);
v___x_1362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1361_);
lean_ctor_set(v___x_1362_, 1, v___x_1360_);
return v___x_1362_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1363_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1, &l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1_once, _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1);
v___x_1364_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1364_, 0, lean_box(0));
lean_closure_set(v___x_1364_, 1, lean_box(0));
lean_closure_set(v___x_1364_, 2, v___x_1363_);
return v___x_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0(lean_object* v_input_1365_, lean_object* v_pre_1366_, lean_object* v_post_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_){
_start:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v_a_1373_; lean_object* v___x_1374_; 
v___x_1371_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2);
v___x_1372_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(lean_box(0), v___x_1371_, v___y_1368_, v___y_1369_);
v_a_1373_ = lean_ctor_get(v___x_1372_, 0);
lean_inc(v_a_1373_);
lean_dec_ref(v___x_1372_);
v___x_1374_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1366_, v_post_1367_, v_input_1365_, v_a_1373_, v___y_1368_, v___y_1369_);
if (lean_obj_tag(v___x_1374_) == 0)
{
lean_object* v_a_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1384_; 
v_a_1375_ = lean_ctor_get(v___x_1374_, 0);
lean_inc(v_a_1375_);
lean_dec_ref_known(v___x_1374_, 1);
v___x_1376_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1376_, 0, lean_box(0));
lean_closure_set(v___x_1376_, 1, lean_box(0));
lean_closure_set(v___x_1376_, 2, v_a_1373_);
v___x_1377_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(lean_box(0), v___x_1376_, v___y_1368_, v___y_1369_);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1384_ == 0)
{
lean_object* v_unused_1385_; 
v_unused_1385_ = lean_ctor_get(v___x_1377_, 0);
lean_dec(v_unused_1385_);
v___x_1379_ = v___x_1377_;
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
else
{
lean_dec(v___x_1377_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1382_; 
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 0, v_a_1375_);
v___x_1382_ = v___x_1379_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_a_1375_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
else
{
lean_dec(v_a_1373_);
return v___x_1374_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___boxed(lean_object* v_input_1386_, lean_object* v_pre_1387_, lean_object* v_post_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0(v_input_1386_, v_pre_1387_, v_post_1388_, v___y_1389_, v___y_1390_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(lean_object* v_e_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_){
_start:
{
lean_object* v___f_1399_; lean_object* v___f_1400_; lean_object* v___x_1401_; 
v___f_1399_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___closed__0));
v___f_1400_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___closed__1));
v___x_1401_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0(v_e_1395_, v___f_1399_, v___f_1400_, v_a_1396_, v_a_1397_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___boxed(lean_object* v_e_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(v_e_1402_, v_a_1403_, v_a_1404_);
lean_dec(v_a_1404_);
lean_dec_ref(v_a_1403_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1407_, lean_object* v_m_1408_, lean_object* v_a_1409_){
_start:
{
lean_object* v___x_1410_; 
v___x_1410_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg(v_m_1408_, v_a_1409_);
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1411_, lean_object* v_m_1412_, lean_object* v_a_1413_){
_start:
{
lean_object* v_res_1414_; 
v_res_1414_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3(v_00_u03b2_1411_, v_m_1412_, v_a_1413_);
lean_dec_ref(v_a_1413_);
lean_dec_ref(v_m_1412_);
return v_res_1414_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_1415_, lean_object* v_ref_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
lean_object* v___x_1420_; 
v___x_1420_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1416_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1421_, lean_object* v_ref_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_1421_, v_ref_1422_, v___y_1423_, v___y_1424_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8(lean_object* v_00_u03b1_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
lean_object* v___x_1431_; 
v___x_1431_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg();
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
lean_object* v_res_1436_; 
v_res_1436_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8(v_00_u03b1_1432_, v___y_1433_, v___y_1434_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
return v_res_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_1437_, lean_object* v_x_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
lean_object* v___x_1443_; 
v___x_1443_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg(v_x_1438_, v___y_1439_, v___y_1440_, v___y_1441_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_1444_, lean_object* v_x_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5(v_00_u03b1_1444_, v_x_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
lean_dec(v___y_1446_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_1451_, lean_object* v_m_1452_, lean_object* v_a_1453_, lean_object* v_b_1454_){
_start:
{
lean_object* v___x_1455_; 
v___x_1455_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6___redArg(v_m_1452_, v_a_1453_, v_b_1454_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_1456_, lean_object* v_a_1457_, lean_object* v_x_1458_){
_start:
{
lean_object* v___x_1459_; 
v___x_1459_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1457_, v_x_1458_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1460_, lean_object* v_a_1461_, lean_object* v_x_1462_){
_start:
{
lean_object* v_res_1463_; 
v_res_1463_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_1460_, v_a_1461_, v_x_1462_);
lean_dec(v_x_1462_);
lean_dec_ref(v_a_1461_);
return v_res_1463_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_1464_, lean_object* v_a_1465_, lean_object* v_x_1466_){
_start:
{
uint8_t v___x_1467_; 
v___x_1467_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1465_, v_x_1466_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___boxed(lean_object* v_00_u03b2_1468_, lean_object* v_a_1469_, lean_object* v_x_1470_){
_start:
{
uint8_t v_res_1471_; lean_object* v_r_1472_; 
v_res_1471_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10(v_00_u03b2_1468_, v_a_1469_, v_x_1470_);
lean_dec(v_x_1470_);
lean_dec_ref(v_a_1469_);
v_r_1472_ = lean_box(v_res_1471_);
return v_r_1472_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_1473_, lean_object* v_data_1474_){
_start:
{
lean_object* v___x_1475_; 
v___x_1475_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11___redArg(v_data_1474_);
return v___x_1475_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12(lean_object* v_00_u03b2_1476_, lean_object* v_a_1477_, lean_object* v_b_1478_, lean_object* v_x_1479_){
_start:
{
lean_object* v___x_1480_; 
v___x_1480_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1477_, v_b_1478_, v_x_1479_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12(lean_object* v_00_u03b2_1481_, lean_object* v_i_1482_, lean_object* v_source_1483_, lean_object* v_target_1484_){
_start:
{
lean_object* v___x_1485_; 
v___x_1485_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v_i_1482_, v_source_1483_, v_target_1484_);
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_1486_, lean_object* v_x_1487_, lean_object* v_x_1488_){
_start:
{
lean_object* v___x_1489_; 
v___x_1489_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_x_1487_, v_x_1488_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(lean_object* v_declName_1490_, lean_object* v___y_1491_){
_start:
{
lean_object* v___x_1493_; lean_object* v_env_1494_; uint8_t v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1493_ = lean_st_ref_get(v___y_1491_);
v_env_1494_ = lean_ctor_get(v___x_1493_, 0);
lean_inc_ref(v_env_1494_);
lean_dec(v___x_1493_);
v___x_1495_ = l_Lean_isRecCore(v_env_1494_, v_declName_1490_);
v___x_1496_ = lean_box(v___x_1495_);
v___x_1497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1497_, 0, v___x_1496_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg___boxed(lean_object* v_declName_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(v_declName_1498_, v___y_1499_);
lean_dec(v___y_1499_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2(lean_object* v_declName_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_){
_start:
{
lean_object* v___x_1508_; 
v___x_1508_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(v_declName_1502_, v___y_1506_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___boxed(lean_object* v_declName_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2(v_declName_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_);
lean_dec(v___y_1513_);
lean_dec_ref(v___y_1512_);
lean_dec(v___y_1511_);
lean_dec_ref(v___y_1510_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(lean_object* v_declName_1516_, lean_object* v___y_1517_){
_start:
{
lean_object* v___x_1519_; lean_object* v_env_1520_; uint8_t v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1519_ = lean_st_ref_get(v___y_1517_);
v_env_1520_ = lean_ctor_get(v___x_1519_, 0);
lean_inc_ref(v_env_1520_);
lean_dec(v___x_1519_);
v___x_1521_ = l_Lean_getReducibilityStatusCore(v_env_1520_, v_declName_1516_);
v___x_1522_ = lean_box(v___x_1521_);
v___x_1523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1523_, 0, v___x_1522_);
return v___x_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg___boxed(lean_object* v_declName_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
lean_object* v_res_1527_; 
v_res_1527_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(v_declName_1524_, v___y_1525_);
lean_dec(v___y_1525_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0(lean_object* v_declName_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_){
_start:
{
lean_object* v___x_1534_; lean_object* v_a_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1550_; 
v___x_1534_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(v_declName_1528_, v___y_1532_);
v_a_1535_ = lean_ctor_get(v___x_1534_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1534_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1537_ = v___x_1534_;
v_isShared_1538_ = v_isSharedCheck_1550_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_a_1535_);
lean_dec(v___x_1534_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1550_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
uint8_t v___x_1539_; 
v___x_1539_ = lean_unbox(v_a_1535_);
lean_dec(v_a_1535_);
if (v___x_1539_ == 0)
{
uint8_t v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1543_; 
v___x_1540_ = 1;
v___x_1541_ = lean_box(v___x_1540_);
if (v_isShared_1538_ == 0)
{
lean_ctor_set(v___x_1537_, 0, v___x_1541_);
v___x_1543_ = v___x_1537_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1541_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
else
{
uint8_t v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1548_; 
v___x_1545_ = 0;
v___x_1546_ = lean_box(v___x_1545_);
if (v_isShared_1538_ == 0)
{
lean_ctor_set(v___x_1537_, 0, v___x_1546_);
v___x_1548_ = v___x_1537_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v___x_1546_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0___boxed(lean_object* v_declName_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_){
_start:
{
lean_object* v_res_1557_; 
v_res_1557_ = l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0(v_declName_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_);
lean_dec(v___y_1555_);
lean_dec_ref(v___y_1554_);
lean_dec(v___y_1553_);
lean_dec_ref(v___y_1552_);
return v_res_1557_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(lean_object* v_a_1558_, lean_object* v_b_1559_){
_start:
{
lean_object* v_array_1561_; lean_object* v_start_1562_; lean_object* v_stop_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1580_; 
v_array_1561_ = lean_ctor_get(v_a_1558_, 0);
v_start_1562_ = lean_ctor_get(v_a_1558_, 1);
v_stop_1563_ = lean_ctor_get(v_a_1558_, 2);
v_isSharedCheck_1580_ = !lean_is_exclusive(v_a_1558_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1565_ = v_a_1558_;
v_isShared_1566_ = v_isSharedCheck_1580_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_stop_1563_);
lean_inc(v_start_1562_);
lean_inc(v_array_1561_);
lean_dec(v_a_1558_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1580_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
uint8_t v___x_1567_; 
v___x_1567_ = lean_nat_dec_lt(v_start_1562_, v_stop_1563_);
if (v___x_1567_ == 0)
{
lean_object* v___x_1568_; 
lean_del_object(v___x_1565_);
lean_dec(v_stop_1563_);
lean_dec(v_start_1562_);
lean_dec_ref(v_array_1561_);
v___x_1568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1568_, 0, v_b_1559_);
return v___x_1568_;
}
else
{
lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1573_; 
v___x_1569_ = lean_box(0);
v___x_1570_ = lean_unsigned_to_nat(1u);
v___x_1571_ = lean_nat_add(v_start_1562_, v___x_1570_);
lean_inc_ref(v_array_1561_);
if (v_isShared_1566_ == 0)
{
lean_ctor_set(v___x_1565_, 1, v___x_1571_);
v___x_1573_ = v___x_1565_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_array_1561_);
lean_ctor_set(v_reuseFailAlloc_1579_, 1, v___x_1571_);
lean_ctor_set(v_reuseFailAlloc_1579_, 2, v_stop_1563_);
v___x_1573_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
lean_object* v___x_1574_; uint8_t v___x_1575_; 
v___x_1574_ = lean_array_fget(v_array_1561_, v_start_1562_);
lean_dec(v_start_1562_);
lean_dec_ref(v_array_1561_);
v___x_1575_ = l_Lean_Expr_hasExprMVar(v___x_1574_);
lean_dec(v___x_1574_);
if (v___x_1575_ == 0)
{
v_a_1558_ = v___x_1573_;
v_b_1559_ = v___x_1569_;
goto _start;
}
else
{
lean_object* v___x_1577_; 
v___x_1577_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_dec_ref_known(v___x_1577_, 1);
v_a_1558_ = v___x_1573_;
v_b_1559_ = v___x_1569_;
goto _start;
}
else
{
lean_dec_ref(v___x_1573_);
return v___x_1577_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg___boxed(lean_object* v_a_1581_, lean_object* v_b_1582_, lean_object* v___y_1583_){
_start:
{
lean_object* v_res_1584_; 
v_res_1584_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(v_a_1581_, v_b_1582_);
return v_res_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(lean_object* v_e_1593_, uint8_t v_isMatch_1594_, uint8_t v_root_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_){
_start:
{
lean_object* v___y_1602_; lean_object* v_b_1603_; lean_object* v___x_1614_; 
v___x_1614_ = l_Lean_Meta_DiscrTree_reduceDT(v_e_1593_, v_root_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1777_; 
v_a_1615_ = lean_ctor_get(v___x_1614_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1617_ = v___x_1614_;
v_isShared_1618_ = v_isSharedCheck_1777_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_a_1615_);
lean_dec(v___x_1614_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1777_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___y_1620_; lean_object* v___y_1630_; lean_object* v___y_1631_; lean_object* v___y_1632_; lean_object* v___y_1633_; 
if (v_root_1595_ == 0)
{
lean_object* v___x_1765_; 
lean_inc(v_a_1615_);
v___x_1765_ = l_Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f(v_a_1615_);
if (lean_obj_tag(v___x_1765_) == 1)
{
lean_object* v_val_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1776_; 
lean_del_object(v___x_1617_);
lean_dec(v_a_1615_);
v_val_1766_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1768_ = v___x_1765_;
v_isShared_1769_ = v_isSharedCheck_1776_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_val_1766_);
lean_dec(v___x_1765_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1776_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v___x_1771_; 
if (v_isShared_1769_ == 0)
{
lean_ctor_set_tag(v___x_1768_, 2);
v___x_1771_ = v___x_1768_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_val_1766_);
v___x_1771_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___x_1772_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
v___x_1773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1773_, 0, v___x_1771_);
lean_ctor_set(v___x_1773_, 1, v___x_1772_);
v___x_1774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1773_);
return v___x_1774_;
}
}
}
else
{
lean_dec(v___x_1765_);
v___y_1630_ = v_a_1596_;
v___y_1631_ = v_a_1597_;
v___y_1632_ = v_a_1598_;
v___y_1633_ = v_a_1599_;
goto v___jp_1629_;
}
}
else
{
v___y_1630_ = v_a_1596_;
v___y_1631_ = v_a_1597_;
v___y_1632_ = v_a_1598_;
v___y_1633_ = v_a_1599_;
goto v___jp_1629_;
}
v___jp_1619_:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1627_; 
v___x_1621_ = l_Lean_Expr_getAppNumArgs(v_a_1615_);
lean_inc(v___x_1621_);
v___x_1622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1622_, 0, v___y_1620_);
lean_ctor_set(v___x_1622_, 1, v___x_1621_);
v___x_1623_ = lean_mk_empty_array_with_capacity(v___x_1621_);
lean_dec(v___x_1621_);
v___x_1624_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1615_, v___x_1623_);
v___x_1625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1622_);
lean_ctor_set(v___x_1625_, 1, v___x_1624_);
if (v_isShared_1618_ == 0)
{
lean_ctor_set(v___x_1617_, 0, v___x_1625_);
v___x_1627_ = v___x_1617_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v___x_1625_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
v___jp_1629_:
{
lean_object* v___x_1634_; 
v___x_1634_ = l_Lean_Expr_getAppFn(v_a_1615_);
switch(lean_obj_tag(v___x_1634_))
{
case 1:
{
lean_object* v_fvarId_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
lean_del_object(v___x_1617_);
v_fvarId_1635_ = lean_ctor_get(v___x_1634_, 0);
lean_inc(v_fvarId_1635_);
lean_dec_ref_known(v___x_1634_, 1);
v___x_1636_ = l_Lean_Expr_getAppNumArgs(v_a_1615_);
lean_inc(v___x_1636_);
v___x_1637_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1637_, 0, v_fvarId_1635_);
lean_ctor_set(v___x_1637_, 1, v___x_1636_);
v___x_1638_ = lean_mk_empty_array_with_capacity(v___x_1636_);
lean_dec(v___x_1636_);
v___x_1639_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1615_, v___x_1638_);
v___x_1640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1637_);
lean_ctor_set(v___x_1640_, 1, v___x_1639_);
v___x_1641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1640_);
return v___x_1641_;
}
case 2:
{
lean_del_object(v___x_1617_);
lean_dec(v_a_1615_);
if (v_isMatch_1594_ == 0)
{
lean_object* v_mvarId_1642_; lean_object* v___x_1643_; uint8_t v_isDefEqStuckEx_1644_; 
v_mvarId_1642_ = lean_ctor_get(v___x_1634_, 0);
lean_inc(v_mvarId_1642_);
lean_dec_ref_known(v___x_1634_, 1);
v___x_1643_ = l_Lean_Meta_Context_config(v___y_1630_);
v_isDefEqStuckEx_1644_ = lean_ctor_get_uint8(v___x_1643_, 4);
lean_dec_ref(v___x_1643_);
if (v_isDefEqStuckEx_1644_ == 0)
{
lean_object* v___x_1645_; 
v___x_1645_ = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(v_mvarId_1642_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
if (lean_obj_tag(v___x_1645_) == 0)
{
lean_object* v_a_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1659_; 
v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1645_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1648_ = v___x_1645_;
v_isShared_1649_ = v_isSharedCheck_1659_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_a_1646_);
lean_dec(v___x_1645_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1659_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
uint8_t v___x_1650_; 
v___x_1650_ = lean_unbox(v_a_1646_);
lean_dec(v_a_1646_);
if (v___x_1650_ == 0)
{
lean_object* v___x_1651_; lean_object* v___x_1653_; 
v___x_1651_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__2));
if (v_isShared_1649_ == 0)
{
lean_ctor_set(v___x_1648_, 0, v___x_1651_);
v___x_1653_ = v___x_1648_;
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
else
{
lean_object* v___x_1655_; lean_object* v___x_1657_; 
v___x_1655_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
if (v_isShared_1649_ == 0)
{
lean_ctor_set(v___x_1648_, 0, v___x_1655_);
v___x_1657_ = v___x_1648_;
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
}
}
else
{
lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1667_; 
v_a_1660_ = lean_ctor_get(v___x_1645_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1645_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1662_ = v___x_1645_;
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v___x_1645_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1665_; 
if (v_isShared_1663_ == 0)
{
v___x_1665_ = v___x_1662_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_a_1660_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
}
else
{
lean_object* v___x_1668_; lean_object* v___x_1669_; 
lean_dec(v_mvarId_1642_);
v___x_1668_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__2));
v___x_1669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1668_);
return v___x_1669_;
}
}
else
{
lean_object* v___x_1670_; lean_object* v___x_1671_; 
lean_dec_ref_known(v___x_1634_, 1);
v___x_1670_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
v___x_1671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1670_);
return v___x_1671_;
}
}
case 4:
{
lean_object* v_declName_1672_; lean_object* v___x_1673_; uint8_t v_isDefEqStuckEx_1674_; 
v_declName_1672_ = lean_ctor_get(v___x_1634_, 0);
lean_inc(v_declName_1672_);
lean_dec_ref_known(v___x_1634_, 2);
v___x_1673_ = l_Lean_Meta_Context_config(v___y_1630_);
v_isDefEqStuckEx_1674_ = lean_ctor_get_uint8(v___x_1673_, 4);
lean_dec_ref(v___x_1673_);
if (v_isDefEqStuckEx_1674_ == 0)
{
v___y_1620_ = v_declName_1672_;
goto v___jp_1619_;
}
else
{
uint8_t v___x_1675_; 
v___x_1675_ = l_Lean_Expr_hasExprMVar(v_a_1615_);
if (v___x_1675_ == 0)
{
v___y_1620_ = v_declName_1672_;
goto v___jp_1619_;
}
else
{
lean_object* v___x_1676_; 
lean_inc(v_declName_1672_);
v___x_1676_ = l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0(v_declName_1672_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
if (lean_obj_tag(v___x_1676_) == 0)
{
lean_object* v_a_1677_; uint8_t v___x_1678_; 
v_a_1677_ = lean_ctor_get(v___x_1676_, 0);
lean_inc(v_a_1677_);
lean_dec_ref_known(v___x_1676_, 1);
v___x_1678_ = lean_unbox(v_a_1677_);
lean_dec(v_a_1677_);
if (v___x_1678_ == 0)
{
lean_object* v___x_1679_; lean_object* v_env_1680_; lean_object* v___x_1681_; 
v___x_1679_ = lean_st_ref_get(v___y_1633_);
v_env_1680_ = lean_ctor_get(v___x_1679_, 0);
lean_inc_ref(v_env_1680_);
lean_dec(v___x_1679_);
v___x_1681_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_1680_, v_a_1615_);
if (lean_obj_tag(v___x_1681_) == 1)
{
lean_object* v_val_1682_; lean_object* v_numDiscrs_1683_; lean_object* v_nargs_1684_; lean_object* v_dummy_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; 
v_val_1682_ = lean_ctor_get(v___x_1681_, 0);
lean_inc(v_val_1682_);
lean_dec_ref_known(v___x_1681_, 1);
v_numDiscrs_1683_ = lean_ctor_get(v_val_1682_, 1);
lean_inc(v_numDiscrs_1683_);
v_nargs_1684_ = l_Lean_Expr_getAppNumArgs(v_a_1615_);
v_dummy_1685_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0);
lean_inc(v_nargs_1684_);
v___x_1686_ = lean_mk_array(v_nargs_1684_, v_dummy_1685_);
v___x_1687_ = lean_unsigned_to_nat(1u);
v___x_1688_ = lean_nat_sub(v_nargs_1684_, v___x_1687_);
lean_dec(v_nargs_1684_);
lean_inc(v_a_1615_);
v___x_1689_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1615_, v___x_1686_, v___x_1688_);
v___x_1690_ = l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(v_val_1682_);
lean_dec(v_val_1682_);
v___x_1691_ = lean_nat_add(v___x_1690_, v_numDiscrs_1683_);
lean_dec(v_numDiscrs_1683_);
v___x_1692_ = l_Array_toSubarray___redArg(v___x_1689_, v___x_1690_, v___x_1691_);
v___x_1693_ = lean_box(0);
v___x_1694_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(v___x_1692_, v___x_1693_);
if (lean_obj_tag(v___x_1694_) == 0)
{
lean_dec_ref_known(v___x_1694_, 1);
v___y_1620_ = v_declName_1672_;
goto v___jp_1619_;
}
else
{
lean_object* v_a_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1702_; 
lean_dec(v_declName_1672_);
lean_del_object(v___x_1617_);
lean_dec(v_a_1615_);
v_a_1695_ = lean_ctor_get(v___x_1694_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1694_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1697_ = v___x_1694_;
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_a_1695_);
lean_dec(v___x_1694_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1700_; 
if (v_isShared_1698_ == 0)
{
v___x_1700_ = v___x_1697_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_a_1695_);
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
lean_object* v___x_1703_; lean_object* v_a_1704_; uint8_t v___x_1705_; 
lean_dec(v___x_1681_);
lean_inc(v_declName_1672_);
v___x_1703_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(v_declName_1672_, v___y_1633_);
v_a_1704_ = lean_ctor_get(v___x_1703_, 0);
lean_inc(v_a_1704_);
lean_dec_ref(v___x_1703_);
v___x_1705_ = lean_unbox(v_a_1704_);
lean_dec(v_a_1704_);
if (v___x_1705_ == 0)
{
v___y_1620_ = v_declName_1672_;
goto v___jp_1619_;
}
else
{
lean_object* v___x_1706_; 
v___x_1706_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1706_) == 0)
{
lean_dec_ref_known(v___x_1706_, 1);
v___y_1620_ = v_declName_1672_;
goto v___jp_1619_;
}
else
{
lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1714_; 
lean_dec(v_declName_1672_);
lean_del_object(v___x_1617_);
lean_dec(v_a_1615_);
v_a_1707_ = lean_ctor_get(v___x_1706_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1706_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1709_ = v___x_1706_;
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_dec(v___x_1706_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1712_; 
if (v_isShared_1710_ == 0)
{
v___x_1712_ = v___x_1709_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_a_1707_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
}
}
}
}
else
{
lean_object* v___x_1715_; 
v___x_1715_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1715_) == 0)
{
lean_dec_ref_known(v___x_1715_, 1);
v___y_1620_ = v_declName_1672_;
goto v___jp_1619_;
}
else
{
lean_object* v_a_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1723_; 
lean_dec(v_declName_1672_);
lean_del_object(v___x_1617_);
lean_dec(v_a_1615_);
v_a_1716_ = lean_ctor_get(v___x_1715_, 0);
v_isSharedCheck_1723_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1723_ == 0)
{
v___x_1718_ = v___x_1715_;
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_a_1716_);
lean_dec(v___x_1715_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v___x_1721_; 
if (v_isShared_1719_ == 0)
{
v___x_1721_ = v___x_1718_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_a_1716_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
return v___x_1721_;
}
}
}
}
}
else
{
lean_object* v_a_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1731_; 
lean_dec(v_declName_1672_);
lean_del_object(v___x_1617_);
lean_dec(v_a_1615_);
v_a_1724_ = lean_ctor_get(v___x_1676_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1676_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1726_ = v___x_1676_;
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_a_1724_);
lean_dec(v___x_1676_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1729_; 
if (v_isShared_1727_ == 0)
{
v___x_1729_ = v___x_1726_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_a_1724_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
}
}
}
}
case 7:
{
lean_object* v_binderType_1732_; lean_object* v_body_1733_; uint8_t v___x_1734_; 
lean_del_object(v___x_1617_);
lean_dec(v_a_1615_);
v_binderType_1732_ = lean_ctor_get(v___x_1634_, 1);
lean_inc_ref(v_binderType_1732_);
v_body_1733_ = lean_ctor_get(v___x_1634_, 2);
lean_inc_ref(v_body_1733_);
lean_dec_ref_known(v___x_1634_, 3);
v___x_1734_ = l_Lean_Expr_hasLooseBVars(v_body_1733_);
if (v___x_1734_ == 0)
{
v___y_1602_ = v_binderType_1732_;
v_b_1603_ = v_body_1733_;
goto v___jp_1601_;
}
else
{
lean_object* v___x_1735_; 
v___x_1735_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(v_body_1733_, v___y_1632_, v___y_1633_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_object* v_a_1736_; 
v_a_1736_ = lean_ctor_get(v___x_1735_, 0);
lean_inc(v_a_1736_);
lean_dec_ref_known(v___x_1735_, 1);
v___y_1602_ = v_binderType_1732_;
v_b_1603_ = v_a_1736_;
goto v___jp_1601_;
}
else
{
lean_object* v_a_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1744_; 
lean_dec_ref(v_binderType_1732_);
v_a_1737_ = lean_ctor_get(v___x_1735_, 0);
v_isSharedCheck_1744_ = !lean_is_exclusive(v___x_1735_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1739_ = v___x_1735_;
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_a_1737_);
lean_dec(v___x_1735_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1742_; 
if (v_isShared_1740_ == 0)
{
v___x_1742_ = v___x_1739_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_a_1737_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
return v___x_1742_;
}
}
}
}
}
case 9:
{
lean_object* v_a_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
lean_del_object(v___x_1617_);
lean_dec(v_a_1615_);
v_a_1745_ = lean_ctor_get(v___x_1634_, 0);
lean_inc_ref(v_a_1745_);
lean_dec_ref_known(v___x_1634_, 1);
v___x_1746_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1746_, 0, v_a_1745_);
v___x_1747_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
v___x_1748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1748_, 0, v___x_1746_);
lean_ctor_set(v___x_1748_, 1, v___x_1747_);
v___x_1749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1749_, 0, v___x_1748_);
return v___x_1749_;
}
case 11:
{
lean_object* v_typeName_1750_; lean_object* v_idx_1751_; lean_object* v_struct_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; 
lean_del_object(v___x_1617_);
v_typeName_1750_ = lean_ctor_get(v___x_1634_, 0);
lean_inc(v_typeName_1750_);
v_idx_1751_ = lean_ctor_get(v___x_1634_, 1);
lean_inc(v_idx_1751_);
v_struct_1752_ = lean_ctor_get(v___x_1634_, 2);
lean_inc_ref(v_struct_1752_);
lean_dec_ref_known(v___x_1634_, 3);
v___x_1753_ = l_Lean_Expr_getAppNumArgs(v_a_1615_);
lean_inc(v___x_1753_);
v___x_1754_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_1754_, 0, v_typeName_1750_);
lean_ctor_set(v___x_1754_, 1, v_idx_1751_);
lean_ctor_set(v___x_1754_, 2, v___x_1753_);
v___x_1755_ = lean_unsigned_to_nat(1u);
v___x_1756_ = lean_mk_empty_array_with_capacity(v___x_1755_);
v___x_1757_ = lean_array_push(v___x_1756_, v_struct_1752_);
v___x_1758_ = lean_mk_empty_array_with_capacity(v___x_1753_);
lean_dec(v___x_1753_);
v___x_1759_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1615_, v___x_1758_);
v___x_1760_ = l_Array_append___redArg(v___x_1757_, v___x_1759_);
lean_dec_ref(v___x_1759_);
v___x_1761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1754_);
lean_ctor_set(v___x_1761_, 1, v___x_1760_);
v___x_1762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1762_, 0, v___x_1761_);
return v___x_1762_;
}
default: 
{
lean_object* v___x_1763_; lean_object* v___x_1764_; 
lean_dec_ref(v___x_1634_);
lean_del_object(v___x_1617_);
lean_dec(v_a_1615_);
v___x_1763_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
v___x_1764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1764_, 0, v___x_1763_);
return v___x_1764_;
}
}
}
}
}
else
{
lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1785_; 
v_a_1778_ = lean_ctor_get(v___x_1614_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1780_ = v___x_1614_;
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v___x_1614_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1783_; 
if (v_isShared_1781_ == 0)
{
v___x_1783_ = v___x_1780_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_a_1778_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
}
v___jp_1601_:
{
uint8_t v___x_1604_; 
v___x_1604_ = l_Lean_Expr_hasLooseBVars(v_b_1603_);
if (v___x_1604_ == 0)
{
lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; 
v___x_1605_ = lean_box(5);
v___x_1606_ = lean_unsigned_to_nat(2u);
v___x_1607_ = lean_mk_empty_array_with_capacity(v___x_1606_);
v___x_1608_ = lean_array_push(v___x_1607_, v___y_1602_);
v___x_1609_ = lean_array_push(v___x_1608_, v_b_1603_);
v___x_1610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1605_);
lean_ctor_set(v___x_1610_, 1, v___x_1609_);
v___x_1611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1610_);
return v___x_1611_;
}
else
{
lean_object* v___x_1612_; lean_object* v___x_1613_; 
lean_dec_ref(v_b_1603_);
lean_dec_ref(v___y_1602_);
v___x_1612_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
v___x_1613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1612_);
return v___x_1613_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___boxed(lean_object* v_e_1786_, lean_object* v_isMatch_1787_, lean_object* v_root_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_){
_start:
{
uint8_t v_isMatch_boxed_1794_; uint8_t v_root_boxed_1795_; lean_object* v_res_1796_; 
v_isMatch_boxed_1794_ = lean_unbox(v_isMatch_1787_);
v_root_boxed_1795_ = lean_unbox(v_root_1788_);
v_res_1796_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_1786_, v_isMatch_boxed_1794_, v_root_boxed_1795_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_);
lean_dec(v_a_1792_);
lean_dec_ref(v_a_1791_);
lean_dec(v_a_1790_);
lean_dec_ref(v_a_1789_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0(lean_object* v_declName_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_){
_start:
{
lean_object* v___x_1803_; 
v___x_1803_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(v_declName_1797_, v___y_1801_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___boxed(lean_object* v_declName_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_){
_start:
{
lean_object* v_res_1810_; 
v_res_1810_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0(v_declName_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_);
lean_dec(v___y_1808_);
lean_dec_ref(v___y_1807_);
lean_dec(v___y_1806_);
lean_dec_ref(v___y_1805_);
return v_res_1810_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1(lean_object* v_inst_1811_, lean_object* v_R_1812_, lean_object* v_a_1813_, lean_object* v_b_1814_, lean_object* v_c_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
lean_object* v___x_1821_; 
v___x_1821_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(v_a_1813_, v_b_1814_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___boxed(lean_object* v_inst_1822_, lean_object* v_R_1823_, lean_object* v_a_1824_, lean_object* v_b_1825_, lean_object* v_c_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_){
_start:
{
lean_object* v_res_1832_; 
v_res_1832_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1(v_inst_1822_, v_R_1823_, v_a_1824_, v_b_1825_, v_c_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1827_);
return v_res_1832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getMatchKeyArgs(lean_object* v_e_1833_, uint8_t v_root_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_){
_start:
{
uint8_t v___x_1840_; lean_object* v___x_1841_; 
v___x_1840_ = 1;
v___x_1841_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_1833_, v___x_1840_, v_root_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_);
return v___x_1841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getMatchKeyArgs___boxed(lean_object* v_e_1842_, lean_object* v_root_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_){
_start:
{
uint8_t v_root_boxed_1849_; lean_object* v_res_1850_; 
v_root_boxed_1849_ = lean_unbox(v_root_1843_);
v_res_1850_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getMatchKeyArgs(v_e_1842_, v_root_boxed_1849_, v_a_1844_, v_a_1845_, v_a_1846_, v_a_1847_);
lean_dec(v_a_1847_);
lean_dec_ref(v_a_1846_);
lean_dec(v_a_1845_);
lean_dec_ref(v_a_1844_);
return v_res_1850_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__1(void){
_start:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___x_1853_ = lean_box(0);
v___x_1854_ = lean_unsigned_to_nat(16u);
v___x_1855_ = lean_mk_array(v___x_1854_, v___x_1853_);
return v___x_1855_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2(void){
_start:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1856_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__1);
v___x_1857_ = lean_unsigned_to_nat(0u);
v___x_1858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1857_);
lean_ctor_set(v___x_1858_, 1, v___x_1856_);
return v___x_1858_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__4(void){
_start:
{
lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; 
v___x_1861_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__3));
v___x_1862_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2);
v___x_1863_ = lean_unsigned_to_nat(0u);
v___x_1864_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__0));
v___x_1865_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1865_, 0, v___x_1864_);
lean_ctor_set(v___x_1865_, 1, v___x_1863_);
lean_ctor_set(v___x_1865_, 2, v___x_1862_);
lean_ctor_set(v___x_1865_, 3, v___x_1861_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg(){
_start:
{
lean_object* v___x_1867_; 
v___x_1867_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__4);
return v___x_1867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___boxed(lean_object* v___dummy_1868_){
_start:
{
lean_object* v_res_1869_; 
v_res_1869_ = l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg();
return v_res_1869_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0(void){
_start:
{
lean_object* v___x_1870_; 
v___x_1870_ = l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg();
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default(lean_object* v_00_u03b1_1871_){
_start:
{
lean_object* v___x_1872_; 
v___x_1872_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0);
return v___x_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___redArg(){
_start:
{
lean_object* v___x_1874_; 
v___x_1874_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0);
return v___x_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___redArg___boxed(lean_object* v___dummy_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___redArg();
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie(lean_object* v_a_1877_){
_start:
{
lean_object* v___x_1878_; 
v___x_1878_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0);
return v___x_1878_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__1(void){
_start:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___x_1881_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2);
v___x_1882_ = lean_unsigned_to_nat(0u);
v___x_1883_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___x_1884_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1883_);
lean_ctor_set(v___x_1884_, 1, v___x_1882_);
lean_ctor_set(v___x_1884_, 2, v___x_1881_);
lean_ctor_set(v___x_1884_, 3, v___x_1883_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg(){
_start:
{
lean_object* v___x_1886_; 
v___x_1886_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__1);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___boxed(lean_object* v___dummy_1887_){
_start:
{
lean_object* v_res_1888_; 
v_res_1888_ = l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg();
return v_res_1888_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0(void){
_start:
{
lean_object* v___x_1889_; 
v___x_1889_ = l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg();
return v___x_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie(lean_object* v_00_u03b1_1890_){
_start:
{
lean_object* v___x_1891_; 
v___x_1891_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0, &l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Trie_pushPending___redArg(lean_object* v_x_1892_, lean_object* v_x_1893_){
_start:
{
lean_object* v_values_1894_; lean_object* v_star_1895_; lean_object* v_children_1896_; lean_object* v_pending_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1905_; 
v_values_1894_ = lean_ctor_get(v_x_1892_, 0);
v_star_1895_ = lean_ctor_get(v_x_1892_, 1);
v_children_1896_ = lean_ctor_get(v_x_1892_, 2);
v_pending_1897_ = lean_ctor_get(v_x_1892_, 3);
v_isSharedCheck_1905_ = !lean_is_exclusive(v_x_1892_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1899_ = v_x_1892_;
v_isShared_1900_ = v_isSharedCheck_1905_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_pending_1897_);
lean_inc(v_children_1896_);
lean_inc(v_star_1895_);
lean_inc(v_values_1894_);
lean_dec(v_x_1892_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1905_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1901_; lean_object* v___x_1903_; 
v___x_1901_ = lean_array_push(v_pending_1897_, v_x_1893_);
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 3, v___x_1901_);
v___x_1903_ = v___x_1899_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_values_1894_);
lean_ctor_set(v_reuseFailAlloc_1904_, 1, v_star_1895_);
lean_ctor_set(v_reuseFailAlloc_1904_, 2, v_children_1896_);
lean_ctor_set(v_reuseFailAlloc_1904_, 3, v___x_1901_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Trie_pushPending(lean_object* v_00_u03b1_1906_, lean_object* v_x_1907_, lean_object* v_x_1908_){
_start:
{
lean_object* v___x_1909_; 
v___x_1909_ = l_Lean_Meta_LazyDiscrTree_Trie_pushPending___redArg(v_x_1907_, v_x_1908_);
return v___x_1909_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__0(void){
_start:
{
lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; 
v___x_1910_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0);
v___x_1911_ = lean_unsigned_to_nat(1u);
v___x_1912_ = lean_mk_empty_array_with_capacity(v___x_1911_);
v___x_1913_ = lean_array_push(v___x_1912_, v___x_1910_);
return v___x_1913_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__1(void){
_start:
{
lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1914_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2);
v___x_1915_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__0);
v___x_1916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1915_);
lean_ctor_set(v___x_1916_, 1, v___x_1914_);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabited___redArg(){
_start:
{
lean_object* v___x_1918_; 
v___x_1918_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__1);
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___boxed(lean_object* v___dummy_1919_){
_start:
{
lean_object* v_res_1920_; 
v_res_1920_ = l_Lean_Meta_LazyDiscrTree_instInhabited___redArg();
return v_res_1920_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_1921_; 
v___x_1921_ = l_Lean_Meta_LazyDiscrTree_instInhabited___redArg();
return v___x_1921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabited(lean_object* v_00_u03b1_1922_){
_start:
{
lean_object* v___x_1923_; 
v___x_1923_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0);
return v___x_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(lean_object* v_msgData_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_){
_start:
{
lean_object* v___x_1930_; lean_object* v_env_1931_; uint8_t v___x_1932_; lean_object* v_env_1933_; lean_object* v___x_1934_; lean_object* v_toCold_1935_; lean_object* v_mctx_1936_; lean_object* v_lctx_1937_; lean_object* v_options_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; 
v___x_1930_ = lean_st_ref_get(v___y_1928_);
v_env_1931_ = lean_ctor_get(v___x_1930_, 0);
lean_inc_ref(v_env_1931_);
lean_dec(v___x_1930_);
v___x_1932_ = 0;
v_env_1933_ = l_Lean_Environment_setRecordingDeps(v_env_1931_, v___x_1932_);
v___x_1934_ = lean_st_ref_get(v___y_1926_);
v_toCold_1935_ = lean_ctor_get(v___y_1927_, 0);
v_mctx_1936_ = lean_ctor_get(v___x_1934_, 0);
lean_inc_ref(v_mctx_1936_);
lean_dec(v___x_1934_);
v_lctx_1937_ = lean_ctor_get(v___y_1925_, 2);
v_options_1938_ = lean_ctor_get(v_toCold_1935_, 2);
lean_inc_ref(v_options_1938_);
lean_inc_ref(v_lctx_1937_);
v___x_1939_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1939_, 0, v_env_1933_);
lean_ctor_set(v___x_1939_, 1, v_mctx_1936_);
lean_ctor_set(v___x_1939_, 2, v_lctx_1937_);
lean_ctor_set(v___x_1939_, 3, v_options_1938_);
v___x_1940_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1939_);
lean_ctor_set(v___x_1940_, 1, v_msgData_1924_);
v___x_1941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1941_, 0, v___x_1940_);
return v___x_1941_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0___boxed(lean_object* v_msgData_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(v_msgData_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
lean_dec(v___y_1944_);
lean_dec_ref(v___y_1943_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(lean_object* v_msg_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_){
_start:
{
lean_object* v_ref_1955_; lean_object* v___x_1956_; lean_object* v_a_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1965_; 
v_ref_1955_ = lean_ctor_get(v___y_1952_, 2);
v___x_1956_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(v_msg_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_);
v_a_1957_ = lean_ctor_get(v___x_1956_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1959_ = v___x_1956_;
v_isShared_1960_ = v_isSharedCheck_1965_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_a_1957_);
lean_dec(v___x_1956_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1965_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1961_; lean_object* v___x_1963_; 
lean_inc(v_ref_1955_);
v___x_1961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1961_, 0, v_ref_1955_);
lean_ctor_set(v___x_1961_, 1, v_a_1957_);
if (v_isShared_1960_ == 0)
{
lean_ctor_set_tag(v___x_1959_, 1);
lean_ctor_set(v___x_1959_, 0, v___x_1961_);
v___x_1963_ = v___x_1959_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v___x_1961_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg___boxed(lean_object* v_msg_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
lean_object* v_res_1972_; 
v_res_1972_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(v_msg_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
return v_res_1972_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1(void){
_start:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; 
v___x_1974_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_pushArgs___closed__0));
v___x_1975_ = l_Lean_stringToMessageData(v___x_1974_);
return v___x_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushArgs(uint8_t v_root_1976_, lean_object* v_todo_1977_, lean_object* v_e_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_){
_start:
{
lean_object* v_v_1985_; uint8_t v___x_1989_; 
v___x_1989_ = l_Lean_Meta_DiscrTree_hasNoindexAnnotation(v_e_1978_);
if (v___x_1989_ == 0)
{
lean_object* v___x_1990_; 
v___x_1990_ = l_Lean_Meta_DiscrTree_reduceDT(v_e_1978_, v_root_1976_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_);
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_object* v_a_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_2133_; 
v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
v_isSharedCheck_2133_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_1993_ = v___x_1990_;
v_isShared_1994_ = v_isSharedCheck_2133_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_a_1991_);
lean_dec(v___x_1990_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_2133_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v___x_1995_; lean_object* v_k_1997_; lean_object* v_nargs_1998_; lean_object* v_todo_1999_; lean_object* v___y_2000_; lean_object* v___y_2001_; lean_object* v___y_2002_; lean_object* v___y_2003_; 
v___x_1995_ = l_Lean_Expr_getAppFn(v_a_1991_);
switch(lean_obj_tag(v___x_1995_))
{
case 9:
{
lean_object* v_a_2042_; 
lean_del_object(v___x_1993_);
lean_dec(v_a_1991_);
v_a_2042_ = lean_ctor_get(v___x_1995_, 0);
lean_inc_ref(v_a_2042_);
lean_dec_ref_known(v___x_1995_, 1);
v_v_1985_ = v_a_2042_;
goto v___jp_1984_;
}
case 4:
{
lean_object* v_declName_2043_; lean_object* v___y_2045_; lean_object* v___y_2046_; lean_object* v___y_2047_; lean_object* v___y_2048_; 
lean_del_object(v___x_1993_);
v_declName_2043_ = lean_ctor_get(v___x_1995_, 0);
if (v_root_1976_ == 0)
{
lean_object* v___x_2051_; 
lean_inc(v_a_1991_);
v___x_2051_ = l_Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f(v_a_1991_);
if (lean_obj_tag(v___x_2051_) == 1)
{
lean_object* v_val_2052_; 
lean_dec_ref_known(v___x_1995_, 2);
lean_dec(v_a_1991_);
v_val_2052_ = lean_ctor_get(v___x_2051_, 0);
lean_inc(v_val_2052_);
lean_dec_ref_known(v___x_2051_, 1);
v_v_1985_ = v_val_2052_;
goto v___jp_1984_;
}
else
{
lean_object* v___x_2053_; 
lean_dec(v___x_2051_);
v___x_2053_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset(v_declName_2043_, v_a_1991_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_);
if (lean_obj_tag(v___x_2053_) == 0)
{
lean_object* v_a_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2064_; 
v_a_2054_ = lean_ctor_get(v___x_2053_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2056_ = v___x_2053_;
v_isShared_2057_ = v_isSharedCheck_2064_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_a_2054_);
lean_dec(v___x_2053_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2064_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
uint8_t v___x_2058_; 
v___x_2058_ = lean_unbox(v_a_2054_);
lean_dec(v_a_2054_);
if (v___x_2058_ == 0)
{
lean_del_object(v___x_2056_);
v___y_2045_ = v_a_1979_;
v___y_2046_ = v_a_1980_;
v___y_2047_ = v_a_1981_;
v___y_2048_ = v_a_1982_;
goto v___jp_2044_;
}
else
{
lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2062_; 
lean_dec_ref_known(v___x_1995_, 2);
lean_dec(v_a_1991_);
v___x_2059_ = lean_box(3);
v___x_2060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2060_, 0, v___x_2059_);
lean_ctor_set(v___x_2060_, 1, v_todo_1977_);
if (v_isShared_2057_ == 0)
{
lean_ctor_set(v___x_2056_, 0, v___x_2060_);
v___x_2062_ = v___x_2056_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v___x_2060_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
}
else
{
lean_object* v_a_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2072_; 
lean_dec_ref_known(v___x_1995_, 2);
lean_dec(v_a_1991_);
lean_dec_ref(v_todo_1977_);
v_a_2065_ = lean_ctor_get(v___x_2053_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2067_ = v___x_2053_;
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_a_2065_);
lean_dec(v___x_2053_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2070_; 
if (v_isShared_2068_ == 0)
{
v___x_2070_ = v___x_2067_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_a_2065_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
return v___x_2070_;
}
}
}
}
}
else
{
v___y_2045_ = v_a_1979_;
v___y_2046_ = v_a_1980_;
v___y_2047_ = v_a_1981_;
v___y_2048_ = v_a_1982_;
goto v___jp_2044_;
}
v___jp_2044_:
{
lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2049_ = l_Lean_Expr_getAppNumArgs(v_a_1991_);
lean_inc(v___x_2049_);
lean_inc(v_declName_2043_);
v___x_2050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2050_, 0, v_declName_2043_);
lean_ctor_set(v___x_2050_, 1, v___x_2049_);
v_k_1997_ = v___x_2050_;
v_nargs_1998_ = v___x_2049_;
v_todo_1999_ = v_todo_1977_;
v___y_2000_ = v___y_2045_;
v___y_2001_ = v___y_2046_;
v___y_2002_ = v___y_2047_;
v___y_2003_ = v___y_2048_;
goto v___jp_1996_;
}
}
case 11:
{
lean_object* v_typeName_2073_; lean_object* v_idx_2074_; lean_object* v_struct_2075_; lean_object* v___x_2076_; lean_object* v___y_2078_; lean_object* v_env_2082_; uint8_t v___x_2083_; 
lean_del_object(v___x_1993_);
v_typeName_2073_ = lean_ctor_get(v___x_1995_, 0);
v_idx_2074_ = lean_ctor_get(v___x_1995_, 1);
v_struct_2075_ = lean_ctor_get(v___x_1995_, 2);
v___x_2076_ = lean_st_ref_get(v_a_1982_);
v_env_2082_ = lean_ctor_get(v___x_2076_, 0);
lean_inc_ref(v_env_2082_);
lean_dec(v___x_2076_);
v___x_2083_ = l_Lean_isClass(v_env_2082_, v_typeName_2073_);
if (v___x_2083_ == 0)
{
lean_inc_ref(v_struct_2075_);
v___y_2078_ = v_struct_2075_;
goto v___jp_2077_;
}
else
{
lean_object* v___x_2084_; 
lean_inc_ref(v_struct_2075_);
v___x_2084_ = l_Lean_Meta_DiscrTree_mkNoindexAnnotation(v_struct_2075_);
v___y_2078_ = v___x_2084_;
goto v___jp_2077_;
}
v___jp_2077_:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2079_ = l_Lean_Expr_getAppNumArgs(v_a_1991_);
lean_inc(v___x_2079_);
lean_inc(v_idx_2074_);
lean_inc(v_typeName_2073_);
v___x_2080_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_2080_, 0, v_typeName_2073_);
lean_ctor_set(v___x_2080_, 1, v_idx_2074_);
lean_ctor_set(v___x_2080_, 2, v___x_2079_);
v___x_2081_ = lean_array_push(v_todo_1977_, v___y_2078_);
v_k_1997_ = v___x_2080_;
v_nargs_1998_ = v___x_2079_;
v_todo_1999_ = v___x_2081_;
v___y_2000_ = v_a_1979_;
v___y_2001_ = v_a_1980_;
v___y_2002_ = v_a_1981_;
v___y_2003_ = v_a_1982_;
goto v___jp_1996_;
}
}
case 1:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2088_; 
lean_dec_ref_known(v___x_1995_, 1);
lean_dec(v_a_1991_);
v___x_2085_ = lean_box(3);
v___x_2086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2085_);
lean_ctor_set(v___x_2086_, 1, v_todo_1977_);
if (v_isShared_1994_ == 0)
{
lean_ctor_set(v___x_1993_, 0, v___x_2086_);
v___x_2088_ = v___x_1993_;
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
case 2:
{
lean_object* v_mvarId_2090_; lean_object* v___x_2091_; uint8_t v___x_2092_; 
lean_dec(v_a_1991_);
v_mvarId_2090_ = lean_ctor_get(v___x_1995_, 0);
lean_inc(v_mvarId_2090_);
lean_dec_ref_known(v___x_1995_, 1);
v___x_2091_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_tmpMVarId));
v___x_2092_ = l_Lean_instBEqMVarId_beq(v_mvarId_2090_, v___x_2091_);
lean_dec(v_mvarId_2090_);
if (v___x_2092_ == 0)
{
lean_object* v___x_2093_; lean_object* v___x_2094_; 
lean_del_object(v___x_1993_);
lean_dec_ref(v_todo_1977_);
v___x_2093_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1, &l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1);
v___x_2094_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(v___x_2093_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_);
return v___x_2094_;
}
else
{
lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2098_; 
v___x_2095_ = lean_box(3);
v___x_2096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2096_, 0, v___x_2095_);
lean_ctor_set(v___x_2096_, 1, v_todo_1977_);
if (v_isShared_1994_ == 0)
{
lean_ctor_set(v___x_1993_, 0, v___x_2096_);
v___x_2098_ = v___x_1993_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v___x_2096_);
v___x_2098_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
return v___x_2098_;
}
}
}
case 7:
{
lean_object* v_binderType_2100_; lean_object* v_body_2101_; lean_object* v_b_2103_; uint8_t v___x_2117_; 
lean_dec(v_a_1991_);
v_binderType_2100_ = lean_ctor_get(v___x_1995_, 1);
lean_inc_ref(v_binderType_2100_);
v_body_2101_ = lean_ctor_get(v___x_1995_, 2);
lean_inc_ref(v_body_2101_);
lean_dec_ref_known(v___x_1995_, 3);
v___x_2117_ = l_Lean_Expr_hasLooseBVars(v_body_2101_);
if (v___x_2117_ == 0)
{
v_b_2103_ = v_body_2101_;
goto v___jp_2102_;
}
else
{
lean_object* v___x_2118_; 
v___x_2118_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(v_body_2101_, v_a_1981_, v_a_1982_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v_a_2119_; 
v_a_2119_ = lean_ctor_get(v___x_2118_, 0);
lean_inc(v_a_2119_);
lean_dec_ref_known(v___x_2118_, 1);
v_b_2103_ = v_a_2119_;
goto v___jp_2102_;
}
else
{
lean_object* v_a_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2127_; 
lean_dec_ref(v_binderType_2100_);
lean_del_object(v___x_1993_);
lean_dec_ref(v_todo_1977_);
v_a_2120_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2122_ = v___x_2118_;
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_a_2120_);
lean_dec(v___x_2118_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2125_; 
if (v_isShared_2123_ == 0)
{
v___x_2125_ = v___x_2122_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_a_2120_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
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
lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2110_; 
v___x_2105_ = lean_box(5);
v___x_2106_ = lean_array_push(v_todo_1977_, v_binderType_2100_);
v___x_2107_ = lean_array_push(v___x_2106_, v_b_2103_);
v___x_2108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2105_);
lean_ctor_set(v___x_2108_, 1, v___x_2107_);
if (v_isShared_1994_ == 0)
{
lean_ctor_set(v___x_1993_, 0, v___x_2108_);
v___x_2110_ = v___x_1993_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v___x_2108_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
else
{
lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2115_; 
lean_dec_ref(v_b_2103_);
lean_dec_ref(v_binderType_2100_);
v___x_2112_ = lean_box(4);
v___x_2113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2112_);
lean_ctor_set(v___x_2113_, 1, v_todo_1977_);
if (v_isShared_1994_ == 0)
{
lean_ctor_set(v___x_1993_, 0, v___x_2113_);
v___x_2115_ = v___x_1993_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v___x_2113_);
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
default: 
{
lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2131_; 
lean_dec_ref(v___x_1995_);
lean_dec(v_a_1991_);
v___x_2128_ = lean_box(4);
v___x_2129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2128_);
lean_ctor_set(v___x_2129_, 1, v_todo_1977_);
if (v_isShared_1994_ == 0)
{
lean_ctor_set(v___x_1993_, 0, v___x_2129_);
v___x_2131_ = v___x_1993_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v___x_2129_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
}
v___jp_1996_:
{
lean_object* v___x_2004_; 
lean_inc(v_nargs_1998_);
v___x_2004_ = l_Lean_Meta_getFunInfoNArgs(v___x_1995_, v_nargs_1998_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v_a_2005_; lean_object* v_paramInfo_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2032_; 
v_a_2005_ = lean_ctor_get(v___x_2004_, 0);
lean_inc(v_a_2005_);
lean_dec_ref_known(v___x_2004_, 1);
v_paramInfo_2006_ = lean_ctor_get(v_a_2005_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v_a_2005_);
if (v_isSharedCheck_2032_ == 0)
{
lean_object* v_unused_2033_; 
v_unused_2033_ = lean_ctor_get(v_a_2005_, 1);
lean_dec(v_unused_2033_);
v___x_2008_ = v_a_2005_;
v_isShared_2009_ = v_isSharedCheck_2032_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_paramInfo_2006_);
lean_dec(v_a_2005_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2032_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
v___x_2010_ = lean_unsigned_to_nat(1u);
v___x_2011_ = lean_nat_sub(v_nargs_1998_, v___x_2010_);
lean_dec(v_nargs_1998_);
v___x_2012_ = l_Lean_Meta_LazyDiscrTree_MatchClone_pushArgsAux(v_paramInfo_2006_, v___x_2011_, v_a_1991_, v_todo_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_);
lean_dec_ref(v_paramInfo_2006_);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2023_; 
v_a_2013_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2015_ = v___x_2012_;
v_isShared_2016_ = v_isSharedCheck_2023_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_dec(v___x_2012_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2023_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2018_; 
if (v_isShared_2009_ == 0)
{
lean_ctor_set(v___x_2008_, 1, v_a_2013_);
lean_ctor_set(v___x_2008_, 0, v_k_1997_);
v___x_2018_ = v___x_2008_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_k_1997_);
lean_ctor_set(v_reuseFailAlloc_2022_, 1, v_a_2013_);
v___x_2018_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
lean_object* v___x_2020_; 
if (v_isShared_2016_ == 0)
{
lean_ctor_set(v___x_2015_, 0, v___x_2018_);
v___x_2020_ = v___x_2015_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v___x_2018_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
return v___x_2020_;
}
}
}
}
else
{
lean_object* v_a_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2031_; 
lean_del_object(v___x_2008_);
lean_dec(v_k_1997_);
v_a_2024_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_2026_ = v___x_2012_;
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_a_2024_);
lean_dec(v___x_2012_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2029_; 
if (v_isShared_2027_ == 0)
{
v___x_2029_ = v___x_2026_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_a_2024_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
}
}
}
else
{
lean_object* v_a_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2041_; 
lean_dec_ref(v_todo_1999_);
lean_dec(v_nargs_1998_);
lean_dec(v_k_1997_);
lean_dec(v_a_1991_);
v_a_2034_ = lean_ctor_get(v___x_2004_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2036_ = v___x_2004_;
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_a_2034_);
lean_dec(v___x_2004_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2039_; 
if (v_isShared_2037_ == 0)
{
v___x_2039_ = v___x_2036_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_a_2034_);
v___x_2039_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
return v___x_2039_;
}
}
}
}
}
}
else
{
lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2141_; 
lean_dec_ref(v_todo_1977_);
v_a_2134_ = lean_ctor_get(v___x_1990_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2136_ = v___x_1990_;
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_1990_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2139_; 
if (v_isShared_2137_ == 0)
{
v___x_2139_ = v___x_2136_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_a_2134_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
}
}
else
{
lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; 
lean_dec_ref(v_e_1978_);
v___x_2142_ = lean_box(3);
v___x_2143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2142_);
lean_ctor_set(v___x_2143_, 1, v_todo_1977_);
v___x_2144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2144_, 0, v___x_2143_);
return v___x_2144_;
}
v___jp_1984_:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1986_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1986_, 0, v_v_1985_);
v___x_1987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1987_, 0, v___x_1986_);
lean_ctor_set(v___x_1987_, 1, v_todo_1977_);
v___x_1988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1987_);
return v___x_1988_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushArgs___boxed(lean_object* v_root_2145_, lean_object* v_todo_2146_, lean_object* v_e_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_){
_start:
{
uint8_t v_root_boxed_2153_; lean_object* v_res_2154_; 
v_root_boxed_2153_ = lean_unbox(v_root_2145_);
v_res_2154_ = l_Lean_Meta_LazyDiscrTree_pushArgs(v_root_boxed_2153_, v_todo_2146_, v_e_2147_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_);
lean_dec(v_a_2151_);
lean_dec_ref(v_a_2150_);
lean_dec(v_a_2149_);
lean_dec_ref(v_a_2148_);
return v_res_2154_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0(lean_object* v_00_u03b1_2155_, lean_object* v_msg_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_){
_start:
{
lean_object* v___x_2162_; 
v___x_2162_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(v_msg_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_);
return v___x_2162_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___boxed(lean_object* v_00_u03b1_2163_, lean_object* v_msg_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_){
_start:
{
lean_object* v_res_2170_; 
v_res_2170_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0(v_00_u03b1_2163_, v_msg_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_);
lean_dec(v___y_2168_);
lean_dec_ref(v___y_2167_);
lean_dec(v___y_2166_);
lean_dec_ref(v___y_2165_);
return v_res_2170_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_initCapacity(void){
_start:
{
lean_object* v___x_2171_; 
v___x_2171_ = lean_unsigned_to_nat(8u);
return v___x_2171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_rootKey(lean_object* v_e_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_){
_start:
{
uint8_t v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2178_ = 1;
v___x_2179_ = lean_unsigned_to_nat(8u);
v___x_2180_ = lean_mk_empty_array_with_capacity(v___x_2179_);
v___x_2181_ = l_Lean_Meta_LazyDiscrTree_pushArgs(v___x_2178_, v___x_2180_, v_e_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_);
return v___x_2181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_rootKey___boxed(lean_object* v_e_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_){
_start:
{
lean_object* v_res_2188_; 
v_res_2188_ = l_Lean_Meta_LazyDiscrTree_rootKey(v_e_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_);
lean_dec(v_a_2186_);
lean_dec_ref(v_a_2185_);
lean_dec(v_a_2184_);
lean_dec_ref(v_a_2183_);
return v_res_2188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_buildPath(lean_object* v_op_2189_, uint8_t v_root_2190_, lean_object* v_todo_2191_, lean_object* v_keys_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_){
_start:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; uint8_t v___x_2200_; 
v___x_2198_ = lean_array_get_size(v_todo_2191_);
v___x_2199_ = lean_unsigned_to_nat(0u);
v___x_2200_ = lean_nat_dec_eq(v___x_2198_, v___x_2199_);
if (v___x_2200_ == 0)
{
lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v_e_2204_; lean_object* v_todo_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2201_ = l_Lean_instInhabitedExpr;
v___x_2202_ = lean_unsigned_to_nat(1u);
v___x_2203_ = lean_nat_sub(v___x_2198_, v___x_2202_);
v_e_2204_ = lean_array_get(v___x_2201_, v_todo_2191_, v___x_2203_);
lean_dec(v___x_2203_);
v_todo_2205_ = lean_array_pop(v_todo_2191_);
v___x_2206_ = lean_box(v_root_2190_);
lean_inc_ref(v_op_2189_);
lean_inc(v_a_2196_);
lean_inc_ref(v_a_2195_);
lean_inc(v_a_2194_);
lean_inc_ref(v_a_2193_);
v___x_2207_ = lean_apply_8(v_op_2189_, v___x_2206_, v_todo_2205_, v_e_2204_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_, lean_box(0));
if (lean_obj_tag(v___x_2207_) == 0)
{
lean_object* v_a_2208_; lean_object* v_fst_2209_; lean_object* v_snd_2210_; lean_object* v___x_2211_; 
v_a_2208_ = lean_ctor_get(v___x_2207_, 0);
lean_inc(v_a_2208_);
lean_dec_ref_known(v___x_2207_, 1);
v_fst_2209_ = lean_ctor_get(v_a_2208_, 0);
lean_inc(v_fst_2209_);
v_snd_2210_ = lean_ctor_get(v_a_2208_, 1);
lean_inc(v_snd_2210_);
lean_dec(v_a_2208_);
v___x_2211_ = lean_array_push(v_keys_2192_, v_fst_2209_);
v_root_2190_ = v___x_2200_;
v_todo_2191_ = v_snd_2210_;
v_keys_2192_ = v___x_2211_;
goto _start;
}
else
{
lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2220_; 
lean_dec_ref(v_keys_2192_);
lean_dec_ref(v_op_2189_);
v_a_2213_ = lean_ctor_get(v___x_2207_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2207_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2215_ = v___x_2207_;
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_dec(v___x_2207_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2218_; 
if (v_isShared_2216_ == 0)
{
v___x_2218_ = v___x_2215_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_a_2213_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
}
else
{
lean_object* v___x_2221_; 
lean_dec_ref(v_todo_2191_);
lean_dec_ref(v_op_2189_);
v___x_2221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2221_, 0, v_keys_2192_);
return v___x_2221_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_buildPath___boxed(lean_object* v_op_2222_, lean_object* v_root_2223_, lean_object* v_todo_2224_, lean_object* v_keys_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_){
_start:
{
uint8_t v_root_boxed_2231_; lean_object* v_res_2232_; 
v_root_boxed_2231_ = lean_unbox(v_root_2223_);
v_res_2232_ = l_Lean_Meta_LazyDiscrTree_buildPath(v_op_2222_, v_root_boxed_2231_, v_todo_2224_, v_keys_2225_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_);
lean_dec(v_a_2229_);
lean_dec_ref(v_a_2228_);
lean_dec(v_a_2227_);
lean_dec_ref(v_a_2226_);
return v_res_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_patternPath(lean_object* v_e_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_){
_start:
{
lean_object* v_op_2240_; lean_object* v___x_2241_; lean_object* v_todo_2242_; uint8_t v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; 
v_op_2240_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_patternPath___closed__0));
v___x_2241_ = lean_unsigned_to_nat(8u);
v_todo_2242_ = lean_mk_empty_array_with_capacity(v___x_2241_);
v___x_2243_ = 1;
lean_inc_ref(v_todo_2242_);
v___x_2244_ = lean_array_push(v_todo_2242_, v_e_2234_);
v___x_2245_ = l_Lean_Meta_LazyDiscrTree_buildPath(v_op_2240_, v___x_2243_, v___x_2244_, v_todo_2242_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_);
return v___x_2245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_patternPath___boxed(lean_object* v_e_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_){
_start:
{
lean_object* v_res_2252_; 
v_res_2252_ = l_Lean_Meta_LazyDiscrTree_patternPath(v_e_2246_, v_a_2247_, v_a_2248_, v_a_2249_, v_a_2250_);
lean_dec(v_a_2250_);
lean_dec_ref(v_a_2249_);
lean_dec(v_a_2248_);
lean_dec_ref(v_a_2247_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath___lam__0(uint8_t v_root_2253_, lean_object* v_todo_2254_, lean_object* v_e_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_){
_start:
{
uint8_t v___x_2261_; lean_object* v___x_2262_; 
v___x_2261_ = 1;
v___x_2262_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_2255_, v___x_2261_, v_root_2253_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_);
if (lean_obj_tag(v___x_2262_) == 0)
{
lean_object* v_a_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2280_; 
v_a_2263_ = lean_ctor_get(v___x_2262_, 0);
v_isSharedCheck_2280_ = !lean_is_exclusive(v___x_2262_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2265_ = v___x_2262_;
v_isShared_2266_ = v_isSharedCheck_2280_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_a_2263_);
lean_dec(v___x_2262_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2280_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v_fst_2267_; lean_object* v_snd_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2279_; 
v_fst_2267_ = lean_ctor_get(v_a_2263_, 0);
v_snd_2268_ = lean_ctor_get(v_a_2263_, 1);
v_isSharedCheck_2279_ = !lean_is_exclusive(v_a_2263_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2270_ = v_a_2263_;
v_isShared_2271_ = v_isSharedCheck_2279_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_snd_2268_);
lean_inc(v_fst_2267_);
lean_dec(v_a_2263_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2279_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v___x_2272_; lean_object* v___x_2274_; 
v___x_2272_ = l_Array_append___redArg(v_todo_2254_, v_snd_2268_);
lean_dec(v_snd_2268_);
if (v_isShared_2271_ == 0)
{
lean_ctor_set(v___x_2270_, 1, v___x_2272_);
v___x_2274_ = v___x_2270_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v_fst_2267_);
lean_ctor_set(v_reuseFailAlloc_2278_, 1, v___x_2272_);
v___x_2274_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
lean_object* v___x_2276_; 
if (v_isShared_2266_ == 0)
{
lean_ctor_set(v___x_2265_, 0, v___x_2274_);
v___x_2276_ = v___x_2265_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v___x_2274_);
v___x_2276_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
return v___x_2276_;
}
}
}
}
}
else
{
lean_dec_ref(v_todo_2254_);
return v___x_2262_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath___lam__0___boxed(lean_object* v_root_2281_, lean_object* v_todo_2282_, lean_object* v_e_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_){
_start:
{
uint8_t v_root_boxed_2289_; lean_object* v_res_2290_; 
v_root_boxed_2289_ = lean_unbox(v_root_2281_);
v_res_2290_ = l_Lean_Meta_LazyDiscrTree_targetPath___lam__0(v_root_boxed_2289_, v_todo_2282_, v_e_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_);
lean_dec(v___y_2287_);
lean_dec_ref(v___y_2286_);
lean_dec(v___y_2285_);
lean_dec_ref(v___y_2284_);
return v_res_2290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath(lean_object* v_e_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_){
_start:
{
lean_object* v_op_2298_; lean_object* v___x_2299_; lean_object* v_todo_2300_; uint8_t v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; 
v_op_2298_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_targetPath___closed__0));
v___x_2299_ = lean_unsigned_to_nat(8u);
v_todo_2300_ = lean_mk_empty_array_with_capacity(v___x_2299_);
v___x_2301_ = 1;
lean_inc_ref(v_todo_2300_);
v___x_2302_ = lean_array_push(v_todo_2300_, v_e_2292_);
v___x_2303_ = l_Lean_Meta_LazyDiscrTree_buildPath(v_op_2298_, v___x_2301_, v___x_2302_, v_todo_2300_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath___boxed(lean_object* v_e_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_){
_start:
{
lean_object* v_res_2310_; 
v_res_2310_ = l_Lean_Meta_LazyDiscrTree_targetPath(v_e_2304_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_);
lean_dec(v_a_2308_);
lean_dec_ref(v_a_2307_);
lean_dec(v_a_2306_);
lean_dec_ref(v_a_2305_);
return v_res_2310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___redArg___lam__0(lean_object* v_tries_2311_, lean_object* v_m_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_){
_start:
{
lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2318_ = lean_st_mk_ref(v_tries_2311_);
lean_inc(v___x_2318_);
v___x_2319_ = lean_apply_6(v_m_2312_, v___x_2318_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, lean_box(0));
if (lean_obj_tag(v___x_2319_) == 0)
{
lean_object* v_a_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2329_; 
v_a_2320_ = lean_ctor_get(v___x_2319_, 0);
v_isSharedCheck_2329_ = !lean_is_exclusive(v___x_2319_);
if (v_isSharedCheck_2329_ == 0)
{
v___x_2322_ = v___x_2319_;
v_isShared_2323_ = v_isSharedCheck_2329_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_a_2320_);
lean_dec(v___x_2319_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2329_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2327_; 
v___x_2324_ = lean_st_ref_get(v___x_2318_);
lean_dec(v___x_2318_);
v___x_2325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2325_, 0, v_a_2320_);
lean_ctor_set(v___x_2325_, 1, v___x_2324_);
if (v_isShared_2323_ == 0)
{
lean_ctor_set(v___x_2322_, 0, v___x_2325_);
v___x_2327_ = v___x_2322_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v___x_2325_);
v___x_2327_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
return v___x_2327_;
}
}
}
else
{
lean_object* v_a_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2337_; 
lean_dec(v___x_2318_);
v_a_2330_ = lean_ctor_get(v___x_2319_, 0);
v_isSharedCheck_2337_ = !lean_is_exclusive(v___x_2319_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2332_ = v___x_2319_;
v_isShared_2333_ = v_isSharedCheck_2337_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_a_2330_);
lean_dec(v___x_2319_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2337_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v___x_2335_; 
if (v_isShared_2333_ == 0)
{
v___x_2335_ = v___x_2332_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v_a_2330_);
v___x_2335_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
return v___x_2335_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___redArg___lam__0___boxed(lean_object* v_tries_2338_, lean_object* v_m_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_){
_start:
{
lean_object* v_res_2345_; 
v_res_2345_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg___lam__0(v_tries_2338_, v_m_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_);
return v_res_2345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___redArg(lean_object* v_d_2346_, lean_object* v_m_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_){
_start:
{
lean_object* v_tries_2353_; lean_object* v_roots_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2407_; 
v_tries_2353_ = lean_ctor_get(v_d_2346_, 0);
v_roots_2354_ = lean_ctor_get(v_d_2346_, 1);
v_isSharedCheck_2407_ = !lean_is_exclusive(v_d_2346_);
if (v_isSharedCheck_2407_ == 0)
{
v___x_2356_ = v_d_2346_;
v_isShared_2357_ = v_isSharedCheck_2407_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_roots_2354_);
lean_inc(v_tries_2353_);
lean_dec(v_d_2346_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2407_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___y_2359_; lean_object* v___x_2388_; uint8_t v_transparency_2389_; uint8_t v___x_2390_; uint8_t v___x_2391_; 
v___x_2388_ = l_Lean_Meta_Context_config(v_a_2348_);
v_transparency_2389_ = lean_ctor_get_uint8(v___x_2388_, 9);
lean_dec_ref(v___x_2388_);
v___x_2390_ = 2;
v___x_2391_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2389_, v___x_2390_);
if (v___x_2391_ == 0)
{
lean_object* v_keyedConfig_2392_; uint8_t v_trackZetaDelta_2393_; lean_object* v_zetaDeltaSet_2394_; lean_object* v_lctx_2395_; lean_object* v_localInstances_2396_; lean_object* v_defEqCtx_x3f_2397_; lean_object* v_synthPendingDepth_2398_; lean_object* v_customCanUnfoldPredicate_x3f_2399_; uint8_t v_univApprox_2400_; uint8_t v_inTypeClassResolution_2401_; uint8_t v_cacheInferType_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; 
v_keyedConfig_2392_ = lean_ctor_get(v_a_2348_, 0);
v_trackZetaDelta_2393_ = lean_ctor_get_uint8(v_a_2348_, sizeof(void*)*7);
v_zetaDeltaSet_2394_ = lean_ctor_get(v_a_2348_, 1);
v_lctx_2395_ = lean_ctor_get(v_a_2348_, 2);
v_localInstances_2396_ = lean_ctor_get(v_a_2348_, 3);
v_defEqCtx_x3f_2397_ = lean_ctor_get(v_a_2348_, 4);
v_synthPendingDepth_2398_ = lean_ctor_get(v_a_2348_, 5);
v_customCanUnfoldPredicate_x3f_2399_ = lean_ctor_get(v_a_2348_, 6);
v_univApprox_2400_ = lean_ctor_get_uint8(v_a_2348_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2401_ = lean_ctor_get_uint8(v_a_2348_, sizeof(void*)*7 + 2);
v_cacheInferType_2402_ = lean_ctor_get_uint8(v_a_2348_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2392_);
v___x_2403_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2390_, v_keyedConfig_2392_);
lean_inc(v_customCanUnfoldPredicate_x3f_2399_);
lean_inc(v_synthPendingDepth_2398_);
lean_inc(v_defEqCtx_x3f_2397_);
lean_inc_ref(v_localInstances_2396_);
lean_inc_ref(v_lctx_2395_);
lean_inc(v_zetaDeltaSet_2394_);
v___x_2404_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2404_, 0, v___x_2403_);
lean_ctor_set(v___x_2404_, 1, v_zetaDeltaSet_2394_);
lean_ctor_set(v___x_2404_, 2, v_lctx_2395_);
lean_ctor_set(v___x_2404_, 3, v_localInstances_2396_);
lean_ctor_set(v___x_2404_, 4, v_defEqCtx_x3f_2397_);
lean_ctor_set(v___x_2404_, 5, v_synthPendingDepth_2398_);
lean_ctor_set(v___x_2404_, 6, v_customCanUnfoldPredicate_x3f_2399_);
lean_ctor_set_uint8(v___x_2404_, sizeof(void*)*7, v_trackZetaDelta_2393_);
lean_ctor_set_uint8(v___x_2404_, sizeof(void*)*7 + 1, v_univApprox_2400_);
lean_ctor_set_uint8(v___x_2404_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2401_);
lean_ctor_set_uint8(v___x_2404_, sizeof(void*)*7 + 3, v_cacheInferType_2402_);
lean_inc(v_a_2351_);
lean_inc_ref(v_a_2350_);
lean_inc(v_a_2349_);
v___x_2405_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg___lam__0(v_tries_2353_, v_m_2347_, v___x_2404_, v_a_2349_, v_a_2350_, v_a_2351_);
v___y_2359_ = v___x_2405_;
goto v___jp_2358_;
}
else
{
lean_object* v___x_2406_; 
lean_inc(v_a_2351_);
lean_inc_ref(v_a_2350_);
lean_inc(v_a_2349_);
lean_inc_ref(v_a_2348_);
v___x_2406_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg___lam__0(v_tries_2353_, v_m_2347_, v_a_2348_, v_a_2349_, v_a_2350_, v_a_2351_);
v___y_2359_ = v___x_2406_;
goto v___jp_2358_;
}
v___jp_2358_:
{
if (lean_obj_tag(v___y_2359_) == 0)
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2379_; 
v_a_2360_ = lean_ctor_get(v___y_2359_, 0);
v_isSharedCheck_2379_ = !lean_is_exclusive(v___y_2359_);
if (v_isSharedCheck_2379_ == 0)
{
v___x_2362_ = v___y_2359_;
v_isShared_2363_ = v_isSharedCheck_2379_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___y_2359_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2379_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v_fst_2364_; lean_object* v_snd_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2378_; 
v_fst_2364_ = lean_ctor_get(v_a_2360_, 0);
v_snd_2365_ = lean_ctor_get(v_a_2360_, 1);
v_isSharedCheck_2378_ = !lean_is_exclusive(v_a_2360_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2367_ = v_a_2360_;
v_isShared_2368_ = v_isSharedCheck_2378_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_snd_2365_);
lean_inc(v_fst_2364_);
lean_dec(v_a_2360_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2378_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___x_2370_; 
if (v_isShared_2357_ == 0)
{
lean_ctor_set(v___x_2356_, 0, v_snd_2365_);
v___x_2370_ = v___x_2356_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v_snd_2365_);
lean_ctor_set(v_reuseFailAlloc_2377_, 1, v_roots_2354_);
v___x_2370_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
lean_object* v___x_2372_; 
if (v_isShared_2368_ == 0)
{
lean_ctor_set(v___x_2367_, 1, v___x_2370_);
v___x_2372_ = v___x_2367_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v_fst_2364_);
lean_ctor_set(v_reuseFailAlloc_2376_, 1, v___x_2370_);
v___x_2372_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
lean_object* v___x_2374_; 
if (v_isShared_2363_ == 0)
{
lean_ctor_set(v___x_2362_, 0, v___x_2372_);
v___x_2374_ = v___x_2362_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v___x_2372_);
v___x_2374_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
return v___x_2374_;
}
}
}
}
}
}
else
{
lean_object* v_a_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2387_; 
lean_del_object(v___x_2356_);
lean_dec_ref(v_roots_2354_);
v_a_2380_ = lean_ctor_get(v___y_2359_, 0);
v_isSharedCheck_2387_ = !lean_is_exclusive(v___y_2359_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2382_ = v___y_2359_;
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_a_2380_);
lean_dec(v___y_2359_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v___x_2385_; 
if (v_isShared_2383_ == 0)
{
v___x_2385_ = v___x_2382_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_a_2380_);
v___x_2385_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
return v___x_2385_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___redArg___boxed(lean_object* v_d_2408_, lean_object* v_m_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_){
_start:
{
lean_object* v_res_2415_; 
v_res_2415_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_d_2408_, v_m_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
lean_dec(v_a_2413_);
lean_dec_ref(v_a_2412_);
lean_dec(v_a_2411_);
lean_dec_ref(v_a_2410_);
return v_res_2415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch(lean_object* v_00_u03b1_2416_, lean_object* v_00_u03b2_2417_, lean_object* v_d_2418_, lean_object* v_m_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_){
_start:
{
lean_object* v___x_2425_; 
v___x_2425_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_d_2418_, v_m_2419_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___boxed(lean_object* v_00_u03b1_2426_, lean_object* v_00_u03b2_2427_, lean_object* v_d_2428_, lean_object* v_m_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_){
_start:
{
lean_object* v_res_2435_; 
v_res_2435_ = l_Lean_Meta_LazyDiscrTree_runMatch(v_00_u03b1_2426_, v_00_u03b2_2427_, v_d_2428_, v_m_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_);
lean_dec(v_a_2433_);
lean_dec_ref(v_a_2432_);
lean_dec(v_a_2431_);
lean_dec_ref(v_a_2430_);
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie___redArg(lean_object* v_i_2436_, lean_object* v_v_2437_, lean_object* v_a_2438_){
_start:
{
lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2440_ = lean_st_ref_take(v_a_2438_);
v___x_2441_ = lean_box(0);
v___x_2442_ = lean_array_set(v___x_2440_, v_i_2436_, v_v_2437_);
v___x_2443_ = lean_st_ref_put(v_a_2438_, v___x_2442_);
v___x_2444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2444_, 0, v___x_2441_);
return v___x_2444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie___redArg___boxed(lean_object* v_i_2445_, lean_object* v_v_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_){
_start:
{
lean_object* v_res_2449_; 
v_res_2449_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_i_2445_, v_v_2446_, v_a_2447_);
lean_dec(v_a_2447_);
lean_dec(v_i_2445_);
return v_res_2449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie(lean_object* v_00_u03b1_2450_, lean_object* v_i_2451_, lean_object* v_v_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_){
_start:
{
lean_object* v___x_2459_; 
v___x_2459_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_i_2451_, v_v_2452_, v_a_2453_);
return v___x_2459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie___boxed(lean_object* v_00_u03b1_2460_, lean_object* v_i_2461_, lean_object* v_v_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_){
_start:
{
lean_object* v_res_2469_; 
v_res_2469_ = l_Lean_Meta_LazyDiscrTree_setTrie(v_00_u03b1_2460_, v_i_2461_, v_v_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_);
lean_dec(v_a_2467_);
lean_dec_ref(v_a_2466_);
lean_dec(v_a_2465_);
lean_dec_ref(v_a_2464_);
lean_dec(v_a_2463_);
lean_dec(v_i_2461_);
return v_res_2469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___redArg___lam__0(lean_object* v_e_2470_, lean_object* v_a_2471_){
_start:
{
lean_object* v_sz_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; 
v_sz_2472_ = lean_array_get_size(v_a_2471_);
v___x_2473_ = lean_unsigned_to_nat(0u);
v___x_2474_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___x_2475_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2);
v___x_2476_ = lean_unsigned_to_nat(1u);
v___x_2477_ = lean_mk_empty_array_with_capacity(v___x_2476_);
v___x_2478_ = lean_array_push(v___x_2477_, v_e_2470_);
v___x_2479_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2479_, 0, v___x_2474_);
lean_ctor_set(v___x_2479_, 1, v___x_2473_);
lean_ctor_set(v___x_2479_, 2, v___x_2475_);
lean_ctor_set(v___x_2479_, 3, v___x_2478_);
v___x_2480_ = lean_array_push(v_a_2471_, v___x_2479_);
v___x_2481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2481_, 0, v_sz_2472_);
lean_ctor_set(v___x_2481_, 1, v___x_2480_);
return v___x_2481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___redArg(lean_object* v_inst_2482_, lean_object* v_e_2483_){
_start:
{
lean_object* v_modifyGet_2484_; lean_object* v___f_2485_; lean_object* v___x_2486_; 
v_modifyGet_2484_ = lean_ctor_get(v_inst_2482_, 2);
lean_inc(v_modifyGet_2484_);
lean_dec_ref(v_inst_2482_);
v___f_2485_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_newTrie___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2485_, 0, v_e_2483_);
v___x_2486_ = lean_apply_2(v_modifyGet_2484_, lean_box(0), v___f_2485_);
return v___x_2486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie(lean_object* v_m_2487_, lean_object* v_00_u03b1_2488_, lean_object* v_inst_2489_, lean_object* v_inst_2490_, lean_object* v_e_2491_){
_start:
{
lean_object* v___x_2492_; 
v___x_2492_ = l_Lean_Meta_LazyDiscrTree_newTrie___redArg(v_inst_2490_, v_e_2491_);
return v___x_2492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___boxed(lean_object* v_m_2493_, lean_object* v_00_u03b1_2494_, lean_object* v_inst_2495_, lean_object* v_inst_2496_, lean_object* v_e_2497_){
_start:
{
lean_object* v_res_2498_; 
v_res_2498_ = l_Lean_Meta_LazyDiscrTree_newTrie(v_m_2493_, v_00_u03b1_2494_, v_inst_2495_, v_inst_2496_, v_e_2497_);
lean_dec_ref(v_inst_2495_);
return v_res_2498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(lean_object* v_i_2499_, lean_object* v_e_2500_, lean_object* v_a_2501_){
_start:
{
lean_object* v___x_2503_; lean_object* v_fst_2505_; lean_object* v_snd_2506_; lean_object* v___x_2509_; lean_object* v___x_2510_; uint8_t v___x_2511_; 
v___x_2503_ = lean_st_ref_take(v_a_2501_);
v___x_2509_ = lean_box(0);
v___x_2510_ = lean_array_get_size(v___x_2503_);
v___x_2511_ = lean_nat_dec_lt(v_i_2499_, v___x_2510_);
if (v___x_2511_ == 0)
{
lean_dec_ref(v_e_2500_);
v_fst_2505_ = v___x_2509_;
v_snd_2506_ = v___x_2503_;
goto v___jp_2504_;
}
else
{
lean_object* v_v_2512_; lean_object* v_xs_x27_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; 
v_v_2512_ = lean_array_fget(v___x_2503_, v_i_2499_);
v_xs_x27_2513_ = lean_array_fset(v___x_2503_, v_i_2499_, v___x_2509_);
v___x_2514_ = l_Lean_Meta_LazyDiscrTree_Trie_pushPending___redArg(v_v_2512_, v_e_2500_);
v___x_2515_ = lean_array_fset(v_xs_x27_2513_, v_i_2499_, v___x_2514_);
v_fst_2505_ = v___x_2509_;
v_snd_2506_ = v___x_2515_;
goto v___jp_2504_;
}
v___jp_2504_:
{
lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___x_2507_ = lean_st_ref_put(v_a_2501_, v_snd_2506_);
v___x_2508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2508_, 0, v_fst_2505_);
return v___x_2508_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg___boxed(lean_object* v_i_2516_, lean_object* v_e_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_){
_start:
{
lean_object* v_res_2520_; 
v_res_2520_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_i_2516_, v_e_2517_, v_a_2518_);
lean_dec(v_a_2518_);
lean_dec(v_i_2516_);
return v_res_2520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie(lean_object* v_00_u03b1_2521_, lean_object* v_i_2522_, lean_object* v_e_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_){
_start:
{
lean_object* v___x_2530_; 
v___x_2530_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_i_2522_, v_e_2523_, v_a_2524_);
return v___x_2530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___boxed(lean_object* v_00_u03b1_2531_, lean_object* v_i_2532_, lean_object* v_e_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_){
_start:
{
lean_object* v_res_2540_; 
v_res_2540_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie(v_00_u03b1_2531_, v_i_2532_, v_e_2533_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_);
lean_dec(v_a_2538_);
lean_dec_ref(v_a_2537_);
lean_dec(v_a_2536_);
lean_dec_ref(v_a_2535_);
lean_dec(v_a_2534_);
lean_dec(v_i_2532_);
return v_res_2540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0(lean_object* v_x_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_){
_start:
{
lean_object* v___x_2548_; 
lean_inc(v___y_2542_);
v___x_2548_ = lean_apply_6(v_x_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, lean_box(0));
return v___x_2548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0___boxed(lean_object* v_x_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_){
_start:
{
lean_object* v_res_2556_; 
v_res_2556_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0(v_x_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_);
lean_dec(v___y_2550_);
return v_res_2556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(lean_object* v_lctx_2557_, lean_object* v_localInsts_2558_, lean_object* v_x_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_){
_start:
{
lean_object* v___f_2566_; lean_object* v___x_2567_; 
lean_inc(v___y_2560_);
v___f_2566_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2566_, 0, v_x_2559_);
lean_closure_set(v___f_2566_, 1, v___y_2560_);
v___x_2567_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_2557_, v_localInsts_2558_, v___f_2566_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_);
if (lean_obj_tag(v___x_2567_) == 0)
{
return v___x_2567_;
}
else
{
lean_object* v_a_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2575_; 
v_a_2568_ = lean_ctor_get(v___x_2567_, 0);
v_isSharedCheck_2575_ = !lean_is_exclusive(v___x_2567_);
if (v_isSharedCheck_2575_ == 0)
{
v___x_2570_ = v___x_2567_;
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_a_2568_);
lean_dec(v___x_2567_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2573_; 
if (v_isShared_2571_ == 0)
{
v___x_2573_ = v___x_2570_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v_a_2568_);
v___x_2573_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
return v___x_2573_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___boxed(lean_object* v_lctx_2576_, lean_object* v_localInsts_2577_, lean_object* v_x_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_){
_start:
{
lean_object* v_res_2585_; 
v_res_2585_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(v_lctx_2576_, v_localInsts_2577_, v_x_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_);
lean_dec(v___y_2583_);
lean_dec_ref(v___y_2582_);
lean_dec(v___y_2581_);
lean_dec_ref(v___y_2580_);
lean_dec(v___y_2579_);
return v_res_2585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0(lean_object* v_00_u03b1_2586_, lean_object* v_00_u03b1_2587_, lean_object* v_lctx_2588_, lean_object* v_localInsts_2589_, lean_object* v_x_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_){
_start:
{
lean_object* v___x_2597_; 
v___x_2597_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(v_lctx_2588_, v_localInsts_2589_, v_x_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_);
return v___x_2597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___boxed(lean_object* v_00_u03b1_2598_, lean_object* v_00_u03b1_2599_, lean_object* v_lctx_2600_, lean_object* v_localInsts_2601_, lean_object* v_x_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_){
_start:
{
lean_object* v_res_2609_; 
v_res_2609_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0(v_00_u03b1_2598_, v_00_u03b1_2599_, v_lctx_2600_, v_localInsts_2601_, v_x_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
lean_dec(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec(v___y_2605_);
lean_dec_ref(v___y_2604_);
lean_dec(v___y_2603_);
return v_res_2609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(lean_object* v_e_2610_, lean_object* v___y_2611_){
_start:
{
lean_object* v___x_2613_; lean_object* v_sz_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___x_2613_ = lean_st_ref_take(v___y_2611_);
v_sz_2614_ = lean_array_get_size(v___x_2613_);
v___x_2615_ = lean_unsigned_to_nat(0u);
v___x_2616_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___x_2617_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2);
v___x_2618_ = lean_unsigned_to_nat(1u);
v___x_2619_ = lean_mk_empty_array_with_capacity(v___x_2618_);
v___x_2620_ = lean_array_push(v___x_2619_, v_e_2610_);
v___x_2621_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2621_, 0, v___x_2616_);
lean_ctor_set(v___x_2621_, 1, v___x_2615_);
lean_ctor_set(v___x_2621_, 2, v___x_2617_);
lean_ctor_set(v___x_2621_, 3, v___x_2620_);
v___x_2622_ = lean_array_push(v___x_2613_, v___x_2621_);
v___x_2623_ = lean_st_ref_put(v___y_2611_, v___x_2622_);
v___x_2624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2624_, 0, v_sz_2614_);
return v___x_2624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg___boxed(lean_object* v_e_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_){
_start:
{
lean_object* v_res_2628_; 
v_res_2628_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v_e_2625_, v___y_2626_);
lean_dec(v___y_2626_);
return v_res_2628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2(lean_object* v_00_u03b1_2629_, lean_object* v_e_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_){
_start:
{
lean_object* v___x_2637_; 
v___x_2637_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v_e_2630_, v___y_2631_);
return v___x_2637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___boxed(lean_object* v_00_u03b1_2638_, lean_object* v_e_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_){
_start:
{
lean_object* v_res_2646_; 
v_res_2646_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2(v_00_u03b1_2638_, v_e_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
lean_dec(v___y_2644_);
lean_dec_ref(v___y_2643_);
lean_dec(v___y_2642_);
lean_dec_ref(v___y_2641_);
lean_dec(v___y_2640_);
return v_res_2646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0(uint8_t v___x_2647_, lean_object* v_todo_2648_, lean_object* v_e_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_){
_start:
{
lean_object* v___x_2656_; 
v___x_2656_ = l_Lean_Meta_LazyDiscrTree_pushArgs(v___x_2647_, v_todo_2648_, v_e_2649_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_);
return v___x_2656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0___boxed(lean_object* v___x_2657_, lean_object* v_todo_2658_, lean_object* v_e_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_){
_start:
{
uint8_t v___x_3423__boxed_2666_; lean_object* v_res_2667_; 
v___x_3423__boxed_2666_ = lean_unbox(v___x_2657_);
v_res_2667_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0(v___x_3423__boxed_2666_, v_todo_2658_, v_e_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_);
lean_dec(v___y_2664_);
lean_dec_ref(v___y_2663_);
lean_dec(v___y_2662_);
lean_dec_ref(v___y_2661_);
lean_dec(v___y_2660_);
return v_res_2667_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(lean_object* v_a_2668_, lean_object* v_b_2669_, lean_object* v_x_2670_){
_start:
{
if (lean_obj_tag(v_x_2670_) == 0)
{
lean_dec(v_b_2669_);
lean_dec(v_a_2668_);
return v_x_2670_;
}
else
{
lean_object* v_key_2671_; lean_object* v_value_2672_; lean_object* v_tail_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2685_; 
v_key_2671_ = lean_ctor_get(v_x_2670_, 0);
v_value_2672_ = lean_ctor_get(v_x_2670_, 1);
v_tail_2673_ = lean_ctor_get(v_x_2670_, 2);
v_isSharedCheck_2685_ = !lean_is_exclusive(v_x_2670_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2675_ = v_x_2670_;
v_isShared_2676_ = v_isSharedCheck_2685_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_tail_2673_);
lean_inc(v_value_2672_);
lean_inc(v_key_2671_);
lean_dec(v_x_2670_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2685_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
uint8_t v___x_2677_; 
v___x_2677_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_2671_, v_a_2668_);
if (v___x_2677_ == 0)
{
lean_object* v___x_2678_; lean_object* v___x_2680_; 
v___x_2678_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(v_a_2668_, v_b_2669_, v_tail_2673_);
if (v_isShared_2676_ == 0)
{
lean_ctor_set(v___x_2675_, 2, v___x_2678_);
v___x_2680_ = v___x_2675_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_key_2671_);
lean_ctor_set(v_reuseFailAlloc_2681_, 1, v_value_2672_);
lean_ctor_set(v_reuseFailAlloc_2681_, 2, v___x_2678_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
return v___x_2680_;
}
}
else
{
lean_object* v___x_2683_; 
lean_dec(v_value_2672_);
lean_dec(v_key_2671_);
if (v_isShared_2676_ == 0)
{
lean_ctor_set(v___x_2675_, 1, v_b_2669_);
lean_ctor_set(v___x_2675_, 0, v_a_2668_);
v___x_2683_ = v___x_2675_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_a_2668_);
lean_ctor_set(v_reuseFailAlloc_2684_, 1, v_b_2669_);
lean_ctor_set(v_reuseFailAlloc_2684_, 2, v_tail_2673_);
v___x_2683_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
return v___x_2683_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(lean_object* v_a_2686_, lean_object* v_x_2687_){
_start:
{
if (lean_obj_tag(v_x_2687_) == 0)
{
uint8_t v___x_2688_; 
v___x_2688_ = 0;
return v___x_2688_;
}
else
{
lean_object* v_key_2689_; lean_object* v_tail_2690_; uint8_t v___x_2691_; 
v_key_2689_ = lean_ctor_get(v_x_2687_, 0);
v_tail_2690_ = lean_ctor_get(v_x_2687_, 2);
v___x_2691_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_2689_, v_a_2686_);
if (v___x_2691_ == 0)
{
v_x_2687_ = v_tail_2690_;
goto _start;
}
else
{
return v___x_2691_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg___boxed(lean_object* v_a_2693_, lean_object* v_x_2694_){
_start:
{
uint8_t v_res_2695_; lean_object* v_r_2696_; 
v_res_2695_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(v_a_2693_, v_x_2694_);
lean_dec(v_x_2694_);
lean_dec(v_a_2693_);
v_r_2696_ = lean_box(v_res_2695_);
return v_r_2696_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7___redArg(lean_object* v_x_2697_, lean_object* v_x_2698_){
_start:
{
if (lean_obj_tag(v_x_2698_) == 0)
{
return v_x_2697_;
}
else
{
lean_object* v_key_2699_; lean_object* v_value_2700_; lean_object* v_tail_2701_; lean_object* v___x_2703_; uint8_t v_isShared_2704_; uint8_t v_isSharedCheck_2724_; 
v_key_2699_ = lean_ctor_get(v_x_2698_, 0);
v_value_2700_ = lean_ctor_get(v_x_2698_, 1);
v_tail_2701_ = lean_ctor_get(v_x_2698_, 2);
v_isSharedCheck_2724_ = !lean_is_exclusive(v_x_2698_);
if (v_isSharedCheck_2724_ == 0)
{
v___x_2703_ = v_x_2698_;
v_isShared_2704_ = v_isSharedCheck_2724_;
goto v_resetjp_2702_;
}
else
{
lean_inc(v_tail_2701_);
lean_inc(v_value_2700_);
lean_inc(v_key_2699_);
lean_dec(v_x_2698_);
v___x_2703_ = lean_box(0);
v_isShared_2704_ = v_isSharedCheck_2724_;
goto v_resetjp_2702_;
}
v_resetjp_2702_:
{
lean_object* v___x_2705_; uint64_t v___x_2706_; uint64_t v___x_2707_; uint64_t v___x_2708_; uint64_t v_fold_2709_; uint64_t v___x_2710_; uint64_t v___x_2711_; uint64_t v___x_2712_; size_t v___x_2713_; size_t v___x_2714_; size_t v___x_2715_; size_t v___x_2716_; size_t v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2720_; 
v___x_2705_ = lean_array_get_size(v_x_2697_);
v___x_2706_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_key_2699_);
v___x_2707_ = 32ULL;
v___x_2708_ = lean_uint64_shift_right(v___x_2706_, v___x_2707_);
v_fold_2709_ = lean_uint64_xor(v___x_2706_, v___x_2708_);
v___x_2710_ = 16ULL;
v___x_2711_ = lean_uint64_shift_right(v_fold_2709_, v___x_2710_);
v___x_2712_ = lean_uint64_xor(v_fold_2709_, v___x_2711_);
v___x_2713_ = lean_uint64_to_usize(v___x_2712_);
v___x_2714_ = lean_usize_of_nat(v___x_2705_);
v___x_2715_ = ((size_t)1ULL);
v___x_2716_ = lean_usize_sub(v___x_2714_, v___x_2715_);
v___x_2717_ = lean_usize_land(v___x_2713_, v___x_2716_);
v___x_2718_ = lean_array_uget_borrowed(v_x_2697_, v___x_2717_);
lean_inc(v___x_2718_);
if (v_isShared_2704_ == 0)
{
lean_ctor_set(v___x_2703_, 2, v___x_2718_);
v___x_2720_ = v___x_2703_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v_key_2699_);
lean_ctor_set(v_reuseFailAlloc_2723_, 1, v_value_2700_);
lean_ctor_set(v_reuseFailAlloc_2723_, 2, v___x_2718_);
v___x_2720_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
lean_object* v___x_2721_; 
v___x_2721_ = lean_array_uset(v_x_2697_, v___x_2717_, v___x_2720_);
v_x_2697_ = v___x_2721_;
v_x_2698_ = v_tail_2701_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6___redArg(lean_object* v_i_2725_, lean_object* v_source_2726_, lean_object* v_target_2727_){
_start:
{
lean_object* v___x_2728_; uint8_t v___x_2729_; 
v___x_2728_ = lean_array_get_size(v_source_2726_);
v___x_2729_ = lean_nat_dec_lt(v_i_2725_, v___x_2728_);
if (v___x_2729_ == 0)
{
lean_dec_ref(v_source_2726_);
lean_dec(v_i_2725_);
return v_target_2727_;
}
else
{
lean_object* v_es_2730_; lean_object* v___x_2731_; lean_object* v_source_2732_; lean_object* v_target_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; 
v_es_2730_ = lean_array_fget(v_source_2726_, v_i_2725_);
v___x_2731_ = lean_box(0);
v_source_2732_ = lean_array_fset(v_source_2726_, v_i_2725_, v___x_2731_);
v_target_2733_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7___redArg(v_target_2727_, v_es_2730_);
v___x_2734_ = lean_unsigned_to_nat(1u);
v___x_2735_ = lean_nat_add(v_i_2725_, v___x_2734_);
lean_dec(v_i_2725_);
v_i_2725_ = v___x_2735_;
v_source_2726_ = v_source_2732_;
v_target_2727_ = v_target_2733_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5___redArg(lean_object* v_data_2737_){
_start:
{
lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v_nbuckets_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; 
v___x_2738_ = lean_array_get_size(v_data_2737_);
v___x_2739_ = lean_unsigned_to_nat(2u);
v_nbuckets_2740_ = lean_nat_mul(v___x_2738_, v___x_2739_);
v___x_2741_ = lean_unsigned_to_nat(0u);
v___x_2742_ = lean_box(0);
v___x_2743_ = lean_mk_array(v_nbuckets_2740_, v___x_2742_);
v___x_2744_ = lean_array_propagate_mark(v_data_2737_, v___x_2743_);
v___x_2745_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6___redArg(v___x_2741_, v_data_2737_, v___x_2744_);
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
v___x_3163_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0);
v___x_3164_ = lean_st_ref_get(v_a_3157_);
v___x_3165_ = lean_array_get(v___x_3163_, v___x_3164_, v_c_3156_);
lean_dec(v___x_3164_);
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
v___x_3176_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_c_3156_, v___x_3163_, v_a_3157_);
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
v___x_3183_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__3));
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
v___x_3280_ = lean_box(0);
v___x_3281_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___x_3282_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3282_, 0, v___x_3281_);
lean_ctor_set(v___x_3282_, 1, v_fst_3277_);
lean_ctor_set(v___x_3282_, 2, v_snd_3278_);
lean_ctor_set(v___x_3282_, 3, v___x_3281_);
v___x_3283_ = lean_array_set(v___x_3279_, v_next_3261_, v___x_3282_);
lean_dec(v_next_3261_);
v___x_3284_ = lean_st_ref_put(v_a_3263_, v___x_3283_);
if (v_isShared_3275_ == 0)
{
lean_ctor_set(v___x_3274_, 0, v___x_3280_);
v___x_3286_ = v___x_3274_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3287_; 
v_reuseFailAlloc_3287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3287_, 0, v___x_3280_);
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
size_t v___x_3690_; size_t v___x_3691_; lean_object* v___x_3692_; 
v___x_3690_ = ((size_t)0ULL);
v___x_3691_ = lean_usize_of_nat(v___x_3687_);
v___x_3692_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(v_b_3686_, v___x_3690_, v___x_3691_, v_a_3678_);
v_j_3677_ = v_n_3682_;
v_a_3678_ = v___x_3692_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg___boxed(lean_object* v_n_3694_, lean_object* v_aa_3695_, lean_object* v_n_3696_, lean_object* v_j_3697_, lean_object* v_a_3698_){
_start:
{
lean_object* v_res_3699_; 
v_res_3699_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(v_n_3694_, v_aa_3695_, v_n_3696_, v_j_3697_, v_a_3698_);
lean_dec(v_n_3696_);
lean_dec_ref(v_aa_3695_);
lean_dec(v_n_3694_);
return v_res_3699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(lean_object* v_mr_3700_, lean_object* v_a_3701_){
_start:
{
lean_object* v_n_3702_; lean_object* v___x_3703_; 
v_n_3702_ = lean_array_get_size(v_mr_3700_);
v___x_3703_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(v_n_3702_, v_mr_3700_, v_n_3702_, v_n_3702_, v_a_3701_);
return v___x_3703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg___boxed(lean_object* v_mr_3704_, lean_object* v_a_3705_){
_start:
{
lean_object* v_res_3706_; 
v_res_3706_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3704_, v_a_3705_);
lean_dec_ref(v_mr_3704_);
return v_res_3706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___redArg(lean_object* v_mr_3707_, lean_object* v_a_3708_){
_start:
{
lean_object* v___x_3709_; 
v___x_3709_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3707_, v_a_3708_);
return v___x_3709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___redArg___boxed(lean_object* v_mr_3710_, lean_object* v_a_3711_){
_start:
{
lean_object* v_res_3712_; 
v_res_3712_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___redArg(v_mr_3710_, v_a_3711_);
lean_dec_ref(v_mr_3710_);
return v_res_3712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults(lean_object* v_00_u03b1_3713_, lean_object* v_mr_3714_, lean_object* v_a_3715_){
_start:
{
lean_object* v___x_3716_; 
v___x_3716_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3714_, v_a_3715_);
return v___x_3716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___boxed(lean_object* v_00_u03b1_3717_, lean_object* v_mr_3718_, lean_object* v_a_3719_){
_start:
{
lean_object* v_res_3720_; 
v_res_3720_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults(v_00_u03b1_3717_, v_mr_3718_, v_a_3719_);
lean_dec_ref(v_mr_3718_);
return v_res_3720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0(lean_object* v_00_u03b1_3721_, lean_object* v_mr_3722_, lean_object* v_a_3723_){
_start:
{
lean_object* v___x_3724_; 
v___x_3724_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3722_, v_a_3723_);
return v___x_3724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___boxed(lean_object* v_00_u03b1_3725_, lean_object* v_mr_3726_, lean_object* v_a_3727_){
_start:
{
lean_object* v_res_3728_; 
v_res_3728_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0(v_00_u03b1_3725_, v_mr_3726_, v_a_3727_);
lean_dec_ref(v_mr_3726_);
return v_res_3728_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0(lean_object* v_00_u03b1_3729_, size_t v_sz_3730_, size_t v_i_3731_, lean_object* v_bs_3732_){
_start:
{
lean_object* v___x_3733_; 
v___x_3733_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(v_sz_3730_, v_i_3731_, v_bs_3732_);
return v___x_3733_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3734_, lean_object* v_sz_3735_, lean_object* v_i_3736_, lean_object* v_bs_3737_){
_start:
{
size_t v_sz_boxed_3738_; size_t v_i_boxed_3739_; lean_object* v_res_3740_; 
v_sz_boxed_3738_ = lean_unbox_usize(v_sz_3735_);
lean_dec(v_sz_3735_);
v_i_boxed_3739_ = lean_unbox_usize(v_i_3736_);
lean_dec(v_i_3736_);
v_res_3740_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0(v_00_u03b1_3734_, v_sz_boxed_3738_, v_i_boxed_3739_, v_bs_3737_);
return v_res_3740_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1(lean_object* v_00_u03b1_3741_, lean_object* v_as_3742_, size_t v_i_3743_, size_t v_stop_3744_, lean_object* v_b_3745_){
_start:
{
lean_object* v___x_3746_; 
v___x_3746_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(v_as_3742_, v_i_3743_, v_stop_3744_, v_b_3745_);
return v___x_3746_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3747_, lean_object* v_as_3748_, lean_object* v_i_3749_, lean_object* v_stop_3750_, lean_object* v_b_3751_){
_start:
{
size_t v_i_boxed_3752_; size_t v_stop_boxed_3753_; lean_object* v_res_3754_; 
v_i_boxed_3752_ = lean_unbox_usize(v_i_3749_);
lean_dec(v_i_3749_);
v_stop_boxed_3753_ = lean_unbox_usize(v_stop_3750_);
lean_dec(v_stop_3750_);
v_res_3754_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1(v_00_u03b1_3747_, v_as_3748_, v_i_boxed_3752_, v_stop_boxed_3753_, v_b_3751_);
lean_dec_ref(v_as_3748_);
return v_res_3754_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2(lean_object* v_00_u03b1_3755_, lean_object* v_n_3756_, lean_object* v_aa_3757_, lean_object* v_n_3758_, lean_object* v_j_3759_, lean_object* v_a_3760_, lean_object* v_a_3761_){
_start:
{
lean_object* v___x_3762_; 
v___x_3762_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(v_n_3756_, v_aa_3757_, v_n_3758_, v_j_3759_, v_a_3761_);
return v___x_3762_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___boxed(lean_object* v_00_u03b1_3763_, lean_object* v_n_3764_, lean_object* v_aa_3765_, lean_object* v_n_3766_, lean_object* v_j_3767_, lean_object* v_a_3768_, lean_object* v_a_3769_){
_start:
{
lean_object* v_res_3770_; 
v_res_3770_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2(v_00_u03b1_3763_, v_n_3764_, v_aa_3765_, v_n_3766_, v_j_3767_, v_a_3768_, v_a_3769_);
lean_dec(v_n_3766_);
lean_dec_ref(v_aa_3765_);
lean_dec(v_n_3764_);
return v_res_3770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0(lean_object* v_snd_3778_, lean_object* v___x_3779_, lean_object* v_score_3780_, lean_object* v___x_3781_, lean_object* v_k_3782_, lean_object* v_args_3783_, lean_object* v_cases_3784_){
_start:
{
lean_object* v___x_3785_; 
v___x_3785_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_snd_3778_, v_k_3782_);
if (lean_obj_tag(v___x_3785_) == 0)
{
lean_dec_ref(v___x_3779_);
return v_cases_3784_;
}
else
{
lean_object* v_val_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; 
v_val_3786_ = lean_ctor_get(v___x_3785_, 0);
lean_inc(v_val_3786_);
lean_dec_ref_known(v___x_3785_, 1);
v___x_3787_ = l_Array_append___redArg(v___x_3779_, v_args_3783_);
v___x_3788_ = lean_nat_add(v_score_3780_, v___x_3781_);
v___x_3789_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3789_, 0, v___x_3787_);
lean_ctor_set(v___x_3789_, 1, v___x_3788_);
lean_ctor_set(v___x_3789_, 2, v_val_3786_);
v___x_3790_ = lean_array_push(v_cases_3784_, v___x_3789_);
return v___x_3790_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0___boxed(lean_object* v_snd_3791_, lean_object* v___x_3792_, lean_object* v_score_3793_, lean_object* v___x_3794_, lean_object* v_k_3795_, lean_object* v_args_3796_, lean_object* v_cases_3797_){
_start:
{
lean_object* v_res_3798_; 
v_res_3798_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0(v_snd_3791_, v___x_3792_, v_score_3793_, v___x_3794_, v_k_3795_, v_args_3796_, v_cases_3797_);
lean_dec_ref(v_args_3796_);
lean_dec(v_k_3795_);
lean_dec(v___x_3794_);
lean_dec(v_score_3793_);
lean_dec_ref(v_snd_3791_);
return v_res_3798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(lean_object* v_cases_3799_, lean_object* v_result_3800_, lean_object* v_a_3801_, lean_object* v_a_3802_, lean_object* v_a_3803_, lean_object* v_a_3804_, lean_object* v_a_3805_){
_start:
{
lean_object* v___x_3807_; lean_object* v___x_3808_; uint8_t v___x_3809_; 
v___x_3807_ = lean_array_get_size(v_cases_3799_);
v___x_3808_ = lean_unsigned_to_nat(0u);
v___x_3809_ = lean_nat_dec_eq(v___x_3807_, v___x_3808_);
if (v___x_3809_ == 0)
{
lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v_ca_3813_; lean_object* v_todo_3814_; lean_object* v_score_3815_; lean_object* v_c_3816_; lean_object* v___x_3818_; uint8_t v_isShared_3819_; uint8_t v_isSharedCheck_3882_; 
v___x_3810_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedPartialMatch_default));
v___x_3811_ = lean_unsigned_to_nat(1u);
v___x_3812_ = lean_nat_sub(v___x_3807_, v___x_3811_);
v_ca_3813_ = lean_array_get(v___x_3810_, v_cases_3799_, v___x_3812_);
lean_dec(v___x_3812_);
v_todo_3814_ = lean_ctor_get(v_ca_3813_, 0);
v_score_3815_ = lean_ctor_get(v_ca_3813_, 1);
v_c_3816_ = lean_ctor_get(v_ca_3813_, 2);
v_isSharedCheck_3882_ = !lean_is_exclusive(v_ca_3813_);
if (v_isSharedCheck_3882_ == 0)
{
v___x_3818_ = v_ca_3813_;
v_isShared_3819_ = v_isSharedCheck_3882_;
goto v_resetjp_3817_;
}
else
{
lean_inc(v_c_3816_);
lean_inc(v_score_3815_);
lean_inc(v_todo_3814_);
lean_dec(v_ca_3813_);
v___x_3818_ = lean_box(0);
v_isShared_3819_ = v_isSharedCheck_3882_;
goto v_resetjp_3817_;
}
v_resetjp_3817_:
{
lean_object* v___x_3820_; lean_object* v_cases_3821_; lean_object* v___x_3822_; 
v___x_3820_ = l_Lean_instInhabitedExpr;
v_cases_3821_ = lean_array_pop(v_cases_3799_);
v___x_3822_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_c_3816_, v_a_3801_, v_a_3802_, v_a_3803_, v_a_3804_, v_a_3805_);
lean_dec(v_c_3816_);
if (lean_obj_tag(v___x_3822_) == 0)
{
lean_object* v_a_3823_; uint8_t v___y_3825_; lean_object* v___y_3826_; lean_object* v___y_3827_; lean_object* v___y_3828_; lean_object* v_snd_3851_; lean_object* v_fst_3852_; lean_object* v_fst_3853_; lean_object* v_snd_3854_; lean_object* v___x_3855_; uint8_t v___y_3857_; uint8_t v___x_3867_; 
v_a_3823_ = lean_ctor_get(v___x_3822_, 0);
lean_inc(v_a_3823_);
lean_dec_ref_known(v___x_3822_, 1);
v_snd_3851_ = lean_ctor_get(v_a_3823_, 1);
lean_inc(v_snd_3851_);
v_fst_3852_ = lean_ctor_get(v_a_3823_, 0);
lean_inc(v_fst_3852_);
lean_dec(v_a_3823_);
v_fst_3853_ = lean_ctor_get(v_snd_3851_, 0);
lean_inc(v_fst_3853_);
v_snd_3854_ = lean_ctor_get(v_snd_3851_, 1);
lean_inc(v_snd_3854_);
lean_dec(v_snd_3851_);
v___x_3855_ = lean_array_get_size(v_todo_3814_);
v___x_3867_ = lean_nat_dec_eq(v___x_3855_, v___x_3808_);
if (v___x_3867_ == 0)
{
uint8_t v___x_3868_; 
lean_dec(v_fst_3852_);
v___x_3868_ = lean_nat_dec_eq(v_fst_3853_, v___x_3808_);
if (v___x_3868_ == 0)
{
v___y_3857_ = v___x_3867_;
goto v___jp_3856_;
}
else
{
lean_object* v_size_3869_; uint8_t v___x_3870_; 
v_size_3869_ = lean_ctor_get(v_snd_3854_, 0);
v___x_3870_ = lean_nat_dec_eq(v_size_3869_, v___x_3808_);
if (v___x_3870_ == 0)
{
v___y_3857_ = v___x_3870_;
goto v___jp_3856_;
}
else
{
lean_dec(v_snd_3854_);
lean_dec(v_fst_3853_);
lean_del_object(v___x_3818_);
lean_dec(v_score_3815_);
lean_dec_ref(v_todo_3814_);
v_cases_3799_ = v_cases_3821_;
goto _start;
}
}
}
else
{
lean_object* v___x_3872_; 
lean_dec(v_snd_3854_);
lean_dec(v_fst_3853_);
lean_del_object(v___x_3818_);
lean_dec_ref(v_todo_3814_);
v___x_3872_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v_result_3800_, v_score_3815_, v_fst_3852_);
lean_dec(v_score_3815_);
v_cases_3799_ = v_cases_3821_;
v_result_3800_ = v___x_3872_;
goto _start;
}
v___jp_3824_:
{
uint8_t v___x_3829_; lean_object* v___x_3830_; 
v___x_3829_ = 1;
v___x_3830_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v___y_3826_, v___x_3829_, v___y_3825_, v_a_3802_, v_a_3803_, v_a_3804_, v_a_3805_);
if (lean_obj_tag(v___x_3830_) == 0)
{
lean_object* v_a_3831_; lean_object* v_fst_3832_; 
v_a_3831_ = lean_ctor_get(v___x_3830_, 0);
lean_inc(v_a_3831_);
lean_dec_ref_known(v___x_3830_, 1);
v_fst_3832_ = lean_ctor_get(v_a_3831_, 0);
lean_inc(v_fst_3832_);
switch(lean_obj_tag(v_fst_3832_))
{
case 3:
{
lean_dec(v_a_3831_);
lean_dec_ref(v___y_3827_);
v_cases_3799_ = v___y_3828_;
goto _start;
}
case 5:
{
lean_object* v_snd_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; 
v_snd_3834_ = lean_ctor_get(v_a_3831_, 1);
lean_inc(v_snd_3834_);
lean_dec(v_a_3831_);
v___x_3835_ = lean_box(4);
v___x_3836_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
lean_inc_ref(v___y_3827_);
v___x_3837_ = lean_apply_3(v___y_3827_, v___x_3835_, v___x_3836_, v___y_3828_);
v___x_3838_ = lean_apply_3(v___y_3827_, v_fst_3832_, v_snd_3834_, v___x_3837_);
v_cases_3799_ = v___x_3838_;
goto _start;
}
default: 
{
lean_object* v_snd_3840_; lean_object* v___x_3841_; 
v_snd_3840_ = lean_ctor_get(v_a_3831_, 1);
lean_inc(v_snd_3840_);
lean_dec(v_a_3831_);
v___x_3841_ = lean_apply_3(v___y_3827_, v_fst_3832_, v_snd_3840_, v___y_3828_);
v_cases_3799_ = v___x_3841_;
goto _start;
}
}
}
else
{
lean_object* v_a_3843_; lean_object* v___x_3845_; uint8_t v_isShared_3846_; uint8_t v_isSharedCheck_3850_; 
lean_dec_ref(v___y_3828_);
lean_dec_ref(v___y_3827_);
lean_dec_ref(v_result_3800_);
v_a_3843_ = lean_ctor_get(v___x_3830_, 0);
v_isSharedCheck_3850_ = !lean_is_exclusive(v___x_3830_);
if (v_isSharedCheck_3850_ == 0)
{
v___x_3845_ = v___x_3830_;
v_isShared_3846_ = v_isSharedCheck_3850_;
goto v_resetjp_3844_;
}
else
{
lean_inc(v_a_3843_);
lean_dec(v___x_3830_);
v___x_3845_ = lean_box(0);
v_isShared_3846_ = v_isSharedCheck_3850_;
goto v_resetjp_3844_;
}
v_resetjp_3844_:
{
lean_object* v___x_3848_; 
if (v_isShared_3846_ == 0)
{
v___x_3848_ = v___x_3845_;
goto v_reusejp_3847_;
}
else
{
lean_object* v_reuseFailAlloc_3849_; 
v_reuseFailAlloc_3849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3849_, 0, v_a_3843_);
v___x_3848_ = v_reuseFailAlloc_3849_;
goto v_reusejp_3847_;
}
v_reusejp_3847_:
{
return v___x_3848_;
}
}
}
}
v___jp_3856_:
{
lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___f_3861_; uint8_t v___x_3862_; 
v___x_3858_ = lean_nat_sub(v___x_3855_, v___x_3811_);
v___x_3859_ = lean_array_get(v___x_3820_, v_todo_3814_, v___x_3858_);
lean_dec(v___x_3858_);
v___x_3860_ = lean_array_pop(v_todo_3814_);
lean_inc(v_score_3815_);
lean_inc_ref(v___x_3860_);
v___f_3861_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0___boxed), 7, 4);
lean_closure_set(v___f_3861_, 0, v_snd_3854_);
lean_closure_set(v___f_3861_, 1, v___x_3860_);
lean_closure_set(v___f_3861_, 2, v_score_3815_);
lean_closure_set(v___f_3861_, 3, v___x_3811_);
v___x_3862_ = lean_nat_dec_eq(v_fst_3853_, v___x_3808_);
if (v___x_3862_ == 0)
{
lean_object* v___x_3864_; 
if (v_isShared_3819_ == 0)
{
lean_ctor_set(v___x_3818_, 2, v_fst_3853_);
lean_ctor_set(v___x_3818_, 0, v___x_3860_);
v___x_3864_ = v___x_3818_;
goto v_reusejp_3863_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v___x_3860_);
lean_ctor_set(v_reuseFailAlloc_3866_, 1, v_score_3815_);
lean_ctor_set(v_reuseFailAlloc_3866_, 2, v_fst_3853_);
v___x_3864_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3863_;
}
v_reusejp_3863_:
{
lean_object* v___x_3865_; 
v___x_3865_ = lean_array_push(v_cases_3821_, v___x_3864_);
v___y_3825_ = v___y_3857_;
v___y_3826_ = v___x_3859_;
v___y_3827_ = v___f_3861_;
v___y_3828_ = v___x_3865_;
goto v___jp_3824_;
}
}
else
{
lean_dec_ref(v___x_3860_);
lean_dec(v_fst_3853_);
lean_del_object(v___x_3818_);
lean_dec(v_score_3815_);
v___y_3825_ = v___y_3857_;
v___y_3826_ = v___x_3859_;
v___y_3827_ = v___f_3861_;
v___y_3828_ = v_cases_3821_;
goto v___jp_3824_;
}
}
}
else
{
lean_object* v_a_3874_; lean_object* v___x_3876_; uint8_t v_isShared_3877_; uint8_t v_isSharedCheck_3881_; 
lean_dec_ref(v_cases_3821_);
lean_del_object(v___x_3818_);
lean_dec(v_score_3815_);
lean_dec_ref(v_todo_3814_);
lean_dec_ref(v_result_3800_);
v_a_3874_ = lean_ctor_get(v___x_3822_, 0);
v_isSharedCheck_3881_ = !lean_is_exclusive(v___x_3822_);
if (v_isSharedCheck_3881_ == 0)
{
v___x_3876_ = v___x_3822_;
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
else
{
lean_inc(v_a_3874_);
lean_dec(v___x_3822_);
v___x_3876_ = lean_box(0);
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
v_resetjp_3875_:
{
lean_object* v___x_3879_; 
if (v_isShared_3877_ == 0)
{
v___x_3879_ = v___x_3876_;
goto v_reusejp_3878_;
}
else
{
lean_object* v_reuseFailAlloc_3880_; 
v_reuseFailAlloc_3880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3880_, 0, v_a_3874_);
v___x_3879_ = v_reuseFailAlloc_3880_;
goto v_reusejp_3878_;
}
v_reusejp_3878_:
{
return v___x_3879_;
}
}
}
}
}
else
{
lean_object* v___x_3883_; 
lean_dec_ref(v_cases_3799_);
v___x_3883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3883_, 0, v_result_3800_);
return v___x_3883_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___boxed(lean_object* v_cases_3884_, lean_object* v_result_3885_, lean_object* v_a_3886_, lean_object* v_a_3887_, lean_object* v_a_3888_, lean_object* v_a_3889_, lean_object* v_a_3890_, lean_object* v_a_3891_){
_start:
{
lean_object* v_res_3892_; 
v_res_3892_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v_cases_3884_, v_result_3885_, v_a_3886_, v_a_3887_, v_a_3888_, v_a_3889_, v_a_3890_);
lean_dec(v_a_3890_);
lean_dec_ref(v_a_3889_);
lean_dec(v_a_3888_);
lean_dec_ref(v_a_3887_);
lean_dec(v_a_3886_);
return v_res_3892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop(lean_object* v_00_u03b1_3893_, lean_object* v_cases_3894_, lean_object* v_result_3895_, lean_object* v_a_3896_, lean_object* v_a_3897_, lean_object* v_a_3898_, lean_object* v_a_3899_, lean_object* v_a_3900_){
_start:
{
lean_object* v___x_3902_; 
v___x_3902_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v_cases_3894_, v_result_3895_, v_a_3896_, v_a_3897_, v_a_3898_, v_a_3899_, v_a_3900_);
return v___x_3902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___boxed(lean_object* v_00_u03b1_3903_, lean_object* v_cases_3904_, lean_object* v_result_3905_, lean_object* v_a_3906_, lean_object* v_a_3907_, lean_object* v_a_3908_, lean_object* v_a_3909_, lean_object* v_a_3910_, lean_object* v_a_3911_){
_start:
{
lean_object* v_res_3912_; 
v_res_3912_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop(v_00_u03b1_3903_, v_cases_3904_, v_result_3905_, v_a_3906_, v_a_3907_, v_a_3908_, v_a_3909_, v_a_3910_);
lean_dec(v_a_3910_);
lean_dec_ref(v_a_3909_);
lean_dec(v_a_3908_);
lean_dec_ref(v_a_3907_);
lean_dec(v_a_3906_);
return v_res_3912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult___redArg(lean_object* v_root_3915_, lean_object* v_a_3916_, lean_object* v_a_3917_, lean_object* v_a_3918_, lean_object* v_a_3919_, lean_object* v_a_3920_){
_start:
{
lean_object* v___x_3922_; lean_object* v___x_3923_; 
v___x_3922_ = lean_box(3);
v___x_3923_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_root_3915_, v___x_3922_);
if (lean_obj_tag(v___x_3923_) == 0)
{
lean_object* v___x_3924_; lean_object* v___x_3925_; 
v___x_3924_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_getStarResult___redArg___closed__0));
v___x_3925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3925_, 0, v___x_3924_);
return v___x_3925_;
}
else
{
lean_object* v_val_3926_; lean_object* v___x_3927_; 
v_val_3926_ = lean_ctor_get(v___x_3923_, 0);
lean_inc(v_val_3926_);
lean_dec_ref_known(v___x_3923_, 1);
v___x_3927_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_val_3926_, v_a_3916_, v_a_3917_, v_a_3918_, v_a_3919_, v_a_3920_);
lean_dec(v_val_3926_);
if (lean_obj_tag(v___x_3927_) == 0)
{
lean_object* v_a_3928_; lean_object* v___x_3930_; uint8_t v_isShared_3931_; uint8_t v_isSharedCheck_3939_; 
v_a_3928_ = lean_ctor_get(v___x_3927_, 0);
v_isSharedCheck_3939_ = !lean_is_exclusive(v___x_3927_);
if (v_isSharedCheck_3939_ == 0)
{
v___x_3930_ = v___x_3927_;
v_isShared_3931_ = v_isSharedCheck_3939_;
goto v_resetjp_3929_;
}
else
{
lean_inc(v_a_3928_);
lean_dec(v___x_3927_);
v___x_3930_ = lean_box(0);
v_isShared_3931_ = v_isSharedCheck_3939_;
goto v_resetjp_3929_;
}
v_resetjp_3929_:
{
lean_object* v_fst_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3937_; 
v_fst_3932_ = lean_ctor_get(v_a_3928_, 0);
lean_inc(v_fst_3932_);
lean_dec(v_a_3928_);
v___x_3933_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_getStarResult___redArg___closed__0));
v___x_3934_ = lean_unsigned_to_nat(1u);
v___x_3935_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v___x_3933_, v___x_3934_, v_fst_3932_);
if (v_isShared_3931_ == 0)
{
lean_ctor_set(v___x_3930_, 0, v___x_3935_);
v___x_3937_ = v___x_3930_;
goto v_reusejp_3936_;
}
else
{
lean_object* v_reuseFailAlloc_3938_; 
v_reuseFailAlloc_3938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3938_, 0, v___x_3935_);
v___x_3937_ = v_reuseFailAlloc_3938_;
goto v_reusejp_3936_;
}
v_reusejp_3936_:
{
return v___x_3937_;
}
}
}
else
{
lean_object* v_a_3940_; lean_object* v___x_3942_; uint8_t v_isShared_3943_; uint8_t v_isSharedCheck_3947_; 
v_a_3940_ = lean_ctor_get(v___x_3927_, 0);
v_isSharedCheck_3947_ = !lean_is_exclusive(v___x_3927_);
if (v_isSharedCheck_3947_ == 0)
{
v___x_3942_ = v___x_3927_;
v_isShared_3943_ = v_isSharedCheck_3947_;
goto v_resetjp_3941_;
}
else
{
lean_inc(v_a_3940_);
lean_dec(v___x_3927_);
v___x_3942_ = lean_box(0);
v_isShared_3943_ = v_isSharedCheck_3947_;
goto v_resetjp_3941_;
}
v_resetjp_3941_:
{
lean_object* v___x_3945_; 
if (v_isShared_3943_ == 0)
{
v___x_3945_ = v___x_3942_;
goto v_reusejp_3944_;
}
else
{
lean_object* v_reuseFailAlloc_3946_; 
v_reuseFailAlloc_3946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3946_, 0, v_a_3940_);
v___x_3945_ = v_reuseFailAlloc_3946_;
goto v_reusejp_3944_;
}
v_reusejp_3944_:
{
return v___x_3945_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult___redArg___boxed(lean_object* v_root_3948_, lean_object* v_a_3949_, lean_object* v_a_3950_, lean_object* v_a_3951_, lean_object* v_a_3952_, lean_object* v_a_3953_, lean_object* v_a_3954_){
_start:
{
lean_object* v_res_3955_; 
v_res_3955_ = l_Lean_Meta_LazyDiscrTree_getStarResult___redArg(v_root_3948_, v_a_3949_, v_a_3950_, v_a_3951_, v_a_3952_, v_a_3953_);
lean_dec(v_a_3953_);
lean_dec_ref(v_a_3952_);
lean_dec(v_a_3951_);
lean_dec_ref(v_a_3950_);
lean_dec(v_a_3949_);
lean_dec_ref(v_root_3948_);
return v_res_3955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult(lean_object* v_00_u03b1_3956_, lean_object* v_root_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_, lean_object* v_a_3960_, lean_object* v_a_3961_, lean_object* v_a_3962_){
_start:
{
lean_object* v___x_3964_; 
v___x_3964_ = l_Lean_Meta_LazyDiscrTree_getStarResult___redArg(v_root_3957_, v_a_3958_, v_a_3959_, v_a_3960_, v_a_3961_, v_a_3962_);
return v___x_3964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult___boxed(lean_object* v_00_u03b1_3965_, lean_object* v_root_3966_, lean_object* v_a_3967_, lean_object* v_a_3968_, lean_object* v_a_3969_, lean_object* v_a_3970_, lean_object* v_a_3971_, lean_object* v_a_3972_){
_start:
{
lean_object* v_res_3973_; 
v_res_3973_ = l_Lean_Meta_LazyDiscrTree_getStarResult(v_00_u03b1_3965_, v_root_3966_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_, v_a_3971_);
lean_dec(v_a_3971_);
lean_dec_ref(v_a_3970_);
lean_dec(v_a_3969_);
lean_dec_ref(v_a_3968_);
lean_dec(v_a_3967_);
lean_dec_ref(v_root_3966_);
return v_res_3973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushRootCase(lean_object* v_r_3974_, lean_object* v_k_3975_, lean_object* v_args_3976_, lean_object* v_cases_3977_){
_start:
{
lean_object* v___x_3978_; 
v___x_3978_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_r_3974_, v_k_3975_);
if (lean_obj_tag(v___x_3978_) == 0)
{
lean_dec_ref(v_args_3976_);
return v_cases_3977_;
}
else
{
lean_object* v_val_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; 
v_val_3979_ = lean_ctor_get(v___x_3978_, 0);
lean_inc(v_val_3979_);
lean_dec_ref_known(v___x_3978_, 1);
v___x_3980_ = lean_unsigned_to_nat(1u);
v___x_3981_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3981_, 0, v_args_3976_);
lean_ctor_set(v___x_3981_, 1, v___x_3980_);
lean_ctor_set(v___x_3981_, 2, v_val_3979_);
v___x_3982_ = lean_array_push(v_cases_3977_, v___x_3981_);
return v___x_3982_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushRootCase___boxed(lean_object* v_r_3983_, lean_object* v_k_3984_, lean_object* v_args_3985_, lean_object* v_cases_3986_){
_start:
{
lean_object* v_res_3987_; 
v_res_3987_ = l_Lean_Meta_LazyDiscrTree_pushRootCase(v_r_3983_, v_k_3984_, v_args_3985_, v_cases_3986_);
lean_dec(v_k_3984_);
lean_dec_ref(v_r_3983_);
return v_res_3987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg(lean_object* v_root_3990_, lean_object* v_e_3991_, lean_object* v_a_3992_, lean_object* v_a_3993_, lean_object* v_a_3994_, lean_object* v_a_3995_, lean_object* v_a_3996_){
_start:
{
lean_object* v___x_3998_; 
v___x_3998_ = l_Lean_Meta_LazyDiscrTree_getStarResult___redArg(v_root_3990_, v_a_3992_, v_a_3993_, v_a_3994_, v_a_3995_, v_a_3996_);
if (lean_obj_tag(v___x_3998_) == 0)
{
lean_object* v_a_3999_; uint8_t v___x_4000_; lean_object* v___x_4001_; 
v_a_3999_ = lean_ctor_get(v___x_3998_, 0);
lean_inc(v_a_3999_);
lean_dec_ref_known(v___x_3998_, 1);
v___x_4000_ = 1;
v___x_4001_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_3991_, v___x_4000_, v___x_4000_, v_a_3993_, v_a_3994_, v_a_3995_, v_a_3996_);
if (lean_obj_tag(v___x_4001_) == 0)
{
lean_object* v_a_4002_; lean_object* v_fst_4003_; 
v_a_4002_ = lean_ctor_get(v___x_4001_, 0);
lean_inc(v_a_4002_);
lean_dec_ref_known(v___x_4001_, 1);
v_fst_4003_ = lean_ctor_get(v_a_4002_, 0);
lean_inc(v_fst_4003_);
switch(lean_obj_tag(v_fst_4003_))
{
case 3:
{
lean_object* v___x_4004_; lean_object* v___x_4005_; 
lean_dec(v_a_4002_);
v___x_4004_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg___closed__0));
v___x_4005_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v___x_4004_, v_a_3999_, v_a_3992_, v_a_3993_, v_a_3994_, v_a_3995_, v_a_3996_);
return v___x_4005_;
}
case 5:
{
lean_object* v_snd_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; 
v_snd_4006_ = lean_ctor_get(v_a_4002_, 1);
lean_inc(v_snd_4006_);
lean_dec(v_a_4002_);
v___x_4007_ = lean_box(4);
v___x_4008_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
v___x_4009_ = l_Lean_Meta_LazyDiscrTree_pushRootCase(v_root_3990_, v___x_4007_, v___x_4008_, v___x_4008_);
v___x_4010_ = l_Lean_Meta_LazyDiscrTree_pushRootCase(v_root_3990_, v_fst_4003_, v_snd_4006_, v___x_4009_);
v___x_4011_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v___x_4010_, v_a_3999_, v_a_3992_, v_a_3993_, v_a_3994_, v_a_3995_, v_a_3996_);
return v___x_4011_;
}
default: 
{
lean_object* v_snd_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; 
v_snd_4012_ = lean_ctor_get(v_a_4002_, 1);
lean_inc(v_snd_4012_);
lean_dec(v_a_4002_);
v___x_4013_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg___closed__0));
v___x_4014_ = l_Lean_Meta_LazyDiscrTree_pushRootCase(v_root_3990_, v_fst_4003_, v_snd_4012_, v___x_4013_);
lean_dec(v_fst_4003_);
v___x_4015_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v___x_4014_, v_a_3999_, v_a_3992_, v_a_3993_, v_a_3994_, v_a_3995_, v_a_3996_);
return v___x_4015_;
}
}
}
else
{
lean_object* v_a_4016_; lean_object* v___x_4018_; uint8_t v_isShared_4019_; uint8_t v_isSharedCheck_4023_; 
lean_dec(v_a_3999_);
v_a_4016_ = lean_ctor_get(v___x_4001_, 0);
v_isSharedCheck_4023_ = !lean_is_exclusive(v___x_4001_);
if (v_isSharedCheck_4023_ == 0)
{
v___x_4018_ = v___x_4001_;
v_isShared_4019_ = v_isSharedCheck_4023_;
goto v_resetjp_4017_;
}
else
{
lean_inc(v_a_4016_);
lean_dec(v___x_4001_);
v___x_4018_ = lean_box(0);
v_isShared_4019_ = v_isSharedCheck_4023_;
goto v_resetjp_4017_;
}
v_resetjp_4017_:
{
lean_object* v___x_4021_; 
if (v_isShared_4019_ == 0)
{
v___x_4021_ = v___x_4018_;
goto v_reusejp_4020_;
}
else
{
lean_object* v_reuseFailAlloc_4022_; 
v_reuseFailAlloc_4022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4022_, 0, v_a_4016_);
v___x_4021_ = v_reuseFailAlloc_4022_;
goto v_reusejp_4020_;
}
v_reusejp_4020_:
{
return v___x_4021_;
}
}
}
}
else
{
lean_dec_ref(v_e_3991_);
return v___x_3998_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg___boxed(lean_object* v_root_4024_, lean_object* v_e_4025_, lean_object* v_a_4026_, lean_object* v_a_4027_, lean_object* v_a_4028_, lean_object* v_a_4029_, lean_object* v_a_4030_, lean_object* v_a_4031_){
_start:
{
lean_object* v_res_4032_; 
v_res_4032_ = l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg(v_root_4024_, v_e_4025_, v_a_4026_, v_a_4027_, v_a_4028_, v_a_4029_, v_a_4030_);
lean_dec(v_a_4030_);
lean_dec_ref(v_a_4029_);
lean_dec(v_a_4028_);
lean_dec_ref(v_a_4027_);
lean_dec(v_a_4026_);
lean_dec_ref(v_root_4024_);
return v_res_4032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore(lean_object* v_00_u03b1_4033_, lean_object* v_root_4034_, lean_object* v_e_4035_, lean_object* v_a_4036_, lean_object* v_a_4037_, lean_object* v_a_4038_, lean_object* v_a_4039_, lean_object* v_a_4040_){
_start:
{
lean_object* v___x_4042_; 
v___x_4042_ = l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg(v_root_4034_, v_e_4035_, v_a_4036_, v_a_4037_, v_a_4038_, v_a_4039_, v_a_4040_);
return v___x_4042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore___boxed(lean_object* v_00_u03b1_4043_, lean_object* v_root_4044_, lean_object* v_e_4045_, lean_object* v_a_4046_, lean_object* v_a_4047_, lean_object* v_a_4048_, lean_object* v_a_4049_, lean_object* v_a_4050_, lean_object* v_a_4051_){
_start:
{
lean_object* v_res_4052_; 
v_res_4052_ = l_Lean_Meta_LazyDiscrTree_getMatchCore(v_00_u03b1_4043_, v_root_4044_, v_e_4045_, v_a_4046_, v_a_4047_, v_a_4048_, v_a_4049_, v_a_4050_);
lean_dec(v_a_4050_);
lean_dec_ref(v_a_4049_);
lean_dec(v_a_4048_);
lean_dec_ref(v_a_4047_);
lean_dec(v_a_4046_);
lean_dec_ref(v_root_4044_);
return v_res_4052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch___redArg(lean_object* v_d_4053_, lean_object* v_e_4054_, lean_object* v_a_4055_, lean_object* v_a_4056_, lean_object* v_a_4057_, lean_object* v_a_4058_){
_start:
{
lean_object* v___y_4061_; lean_object* v_roots_4078_; lean_object* v___x_4079_; uint8_t v_transparency_4080_; lean_object* v___x_4081_; uint8_t v___x_4082_; uint8_t v___x_4083_; 
v_roots_4078_ = lean_ctor_get(v_d_4053_, 1);
v___x_4079_ = l_Lean_Meta_Context_config(v_a_4055_);
v_transparency_4080_ = lean_ctor_get_uint8(v___x_4079_, 9);
lean_dec_ref(v___x_4079_);
lean_inc_ref(v_roots_4078_);
v___x_4081_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getMatchCore___boxed), 9, 3);
lean_closure_set(v___x_4081_, 0, lean_box(0));
lean_closure_set(v___x_4081_, 1, v_roots_4078_);
lean_closure_set(v___x_4081_, 2, v_e_4054_);
v___x_4082_ = 2;
v___x_4083_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_4080_, v___x_4082_);
if (v___x_4083_ == 0)
{
lean_object* v_keyedConfig_4084_; uint8_t v_trackZetaDelta_4085_; lean_object* v_zetaDeltaSet_4086_; lean_object* v_lctx_4087_; lean_object* v_localInstances_4088_; lean_object* v_defEqCtx_x3f_4089_; lean_object* v_synthPendingDepth_4090_; lean_object* v_customCanUnfoldPredicate_x3f_4091_; uint8_t v_univApprox_4092_; uint8_t v_inTypeClassResolution_4093_; uint8_t v_cacheInferType_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; 
v_keyedConfig_4084_ = lean_ctor_get(v_a_4055_, 0);
v_trackZetaDelta_4085_ = lean_ctor_get_uint8(v_a_4055_, sizeof(void*)*7);
v_zetaDeltaSet_4086_ = lean_ctor_get(v_a_4055_, 1);
v_lctx_4087_ = lean_ctor_get(v_a_4055_, 2);
v_localInstances_4088_ = lean_ctor_get(v_a_4055_, 3);
v_defEqCtx_x3f_4089_ = lean_ctor_get(v_a_4055_, 4);
v_synthPendingDepth_4090_ = lean_ctor_get(v_a_4055_, 5);
v_customCanUnfoldPredicate_x3f_4091_ = lean_ctor_get(v_a_4055_, 6);
v_univApprox_4092_ = lean_ctor_get_uint8(v_a_4055_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4093_ = lean_ctor_get_uint8(v_a_4055_, sizeof(void*)*7 + 2);
v_cacheInferType_4094_ = lean_ctor_get_uint8(v_a_4055_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_4084_);
v___x_4095_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4082_, v_keyedConfig_4084_);
lean_inc(v_customCanUnfoldPredicate_x3f_4091_);
lean_inc(v_synthPendingDepth_4090_);
lean_inc(v_defEqCtx_x3f_4089_);
lean_inc_ref(v_localInstances_4088_);
lean_inc_ref(v_lctx_4087_);
lean_inc(v_zetaDeltaSet_4086_);
v___x_4096_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4096_, 0, v___x_4095_);
lean_ctor_set(v___x_4096_, 1, v_zetaDeltaSet_4086_);
lean_ctor_set(v___x_4096_, 2, v_lctx_4087_);
lean_ctor_set(v___x_4096_, 3, v_localInstances_4088_);
lean_ctor_set(v___x_4096_, 4, v_defEqCtx_x3f_4089_);
lean_ctor_set(v___x_4096_, 5, v_synthPendingDepth_4090_);
lean_ctor_set(v___x_4096_, 6, v_customCanUnfoldPredicate_x3f_4091_);
lean_ctor_set_uint8(v___x_4096_, sizeof(void*)*7, v_trackZetaDelta_4085_);
lean_ctor_set_uint8(v___x_4096_, sizeof(void*)*7 + 1, v_univApprox_4092_);
lean_ctor_set_uint8(v___x_4096_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4093_);
lean_ctor_set_uint8(v___x_4096_, sizeof(void*)*7 + 3, v_cacheInferType_4094_);
v___x_4097_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_d_4053_, v___x_4081_, v___x_4096_, v_a_4056_, v_a_4057_, v_a_4058_);
lean_dec_ref_known(v___x_4096_, 7);
v___y_4061_ = v___x_4097_;
goto v___jp_4060_;
}
else
{
lean_object* v___x_4098_; 
v___x_4098_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_d_4053_, v___x_4081_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_);
v___y_4061_ = v___x_4098_;
goto v___jp_4060_;
}
v___jp_4060_:
{
if (lean_obj_tag(v___y_4061_) == 0)
{
lean_object* v_a_4062_; lean_object* v___x_4064_; uint8_t v_isShared_4065_; uint8_t v_isSharedCheck_4069_; 
v_a_4062_ = lean_ctor_get(v___y_4061_, 0);
v_isSharedCheck_4069_ = !lean_is_exclusive(v___y_4061_);
if (v_isSharedCheck_4069_ == 0)
{
v___x_4064_ = v___y_4061_;
v_isShared_4065_ = v_isSharedCheck_4069_;
goto v_resetjp_4063_;
}
else
{
lean_inc(v_a_4062_);
lean_dec(v___y_4061_);
v___x_4064_ = lean_box(0);
v_isShared_4065_ = v_isSharedCheck_4069_;
goto v_resetjp_4063_;
}
v_resetjp_4063_:
{
lean_object* v___x_4067_; 
if (v_isShared_4065_ == 0)
{
v___x_4067_ = v___x_4064_;
goto v_reusejp_4066_;
}
else
{
lean_object* v_reuseFailAlloc_4068_; 
v_reuseFailAlloc_4068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4068_, 0, v_a_4062_);
v___x_4067_ = v_reuseFailAlloc_4068_;
goto v_reusejp_4066_;
}
v_reusejp_4066_:
{
return v___x_4067_;
}
}
}
else
{
lean_object* v_a_4070_; lean_object* v___x_4072_; uint8_t v_isShared_4073_; uint8_t v_isSharedCheck_4077_; 
v_a_4070_ = lean_ctor_get(v___y_4061_, 0);
v_isSharedCheck_4077_ = !lean_is_exclusive(v___y_4061_);
if (v_isSharedCheck_4077_ == 0)
{
v___x_4072_ = v___y_4061_;
v_isShared_4073_ = v_isSharedCheck_4077_;
goto v_resetjp_4071_;
}
else
{
lean_inc(v_a_4070_);
lean_dec(v___y_4061_);
v___x_4072_ = lean_box(0);
v_isShared_4073_ = v_isSharedCheck_4077_;
goto v_resetjp_4071_;
}
v_resetjp_4071_:
{
lean_object* v___x_4075_; 
if (v_isShared_4073_ == 0)
{
v___x_4075_ = v___x_4072_;
goto v_reusejp_4074_;
}
else
{
lean_object* v_reuseFailAlloc_4076_; 
v_reuseFailAlloc_4076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4076_, 0, v_a_4070_);
v___x_4075_ = v_reuseFailAlloc_4076_;
goto v_reusejp_4074_;
}
v_reusejp_4074_:
{
return v___x_4075_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch___redArg___boxed(lean_object* v_d_4099_, lean_object* v_e_4100_, lean_object* v_a_4101_, lean_object* v_a_4102_, lean_object* v_a_4103_, lean_object* v_a_4104_, lean_object* v_a_4105_){
_start:
{
lean_object* v_res_4106_; 
v_res_4106_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v_d_4099_, v_e_4100_, v_a_4101_, v_a_4102_, v_a_4103_, v_a_4104_);
lean_dec(v_a_4104_);
lean_dec_ref(v_a_4103_);
lean_dec(v_a_4102_);
lean_dec_ref(v_a_4101_);
return v_res_4106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch(lean_object* v_00_u03b1_4107_, lean_object* v_d_4108_, lean_object* v_e_4109_, lean_object* v_a_4110_, lean_object* v_a_4111_, lean_object* v_a_4112_, lean_object* v_a_4113_){
_start:
{
lean_object* v___x_4115_; 
v___x_4115_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v_d_4108_, v_e_4109_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_);
return v___x_4115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch___boxed(lean_object* v_00_u03b1_4116_, lean_object* v_d_4117_, lean_object* v_e_4118_, lean_object* v_a_4119_, lean_object* v_a_4120_, lean_object* v_a_4121_, lean_object* v_a_4122_, lean_object* v_a_4123_){
_start:
{
lean_object* v_res_4124_; 
v_res_4124_ = l_Lean_Meta_LazyDiscrTree_getMatch(v_00_u03b1_4116_, v_d_4117_, v_e_4118_, v_a_4119_, v_a_4120_, v_a_4121_, v_a_4122_);
lean_dec(v_a_4122_);
lean_dec_ref(v_a_4121_);
lean_dec(v_a_4120_);
lean_dec_ref(v_a_4119_);
return v_res_4124_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1(void){
_start:
{
lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; 
v___x_4127_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__0));
v___x_4128_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2);
v___x_4129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4129_, 0, v___x_4128_);
lean_ctor_set(v___x_4129_, 1, v___x_4127_);
return v___x_4129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg(){
_start:
{
lean_object* v___x_4131_; 
v___x_4131_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1);
return v___x_4131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___boxed(lean_object* v___dummy_4132_){
_start:
{
lean_object* v_res_4133_; 
v_res_4133_ = l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg();
return v_res_4133_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0(void){
_start:
{
lean_object* v___x_4134_; 
v___x_4134_ = l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg();
return v___x_4134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default(lean_object* v_00_u03b1_4135_){
_start:
{
lean_object* v___x_4136_; 
v___x_4136_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0);
return v___x_4136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___redArg(){
_start:
{
lean_object* v___x_4138_; 
v___x_4138_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0);
return v___x_4138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___redArg___boxed(lean_object* v___dummy_4139_){
_start:
{
lean_object* v_res_4140_; 
v_res_4140_ = l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___redArg();
return v_res_4140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree(lean_object* v_a_4141_){
_start:
{
lean_object* v___x_4142_; 
v___x_4142_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0);
return v___x_4142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(lean_object* v_d_4143_, lean_object* v_k_4144_, lean_object* v_f_4145_){
_start:
{
lean_object* v_roots_4146_; lean_object* v_tries_4147_; lean_object* v___x_4148_; 
v_roots_4146_ = lean_ctor_get(v_d_4143_, 0);
v_tries_4147_ = lean_ctor_get(v_d_4143_, 1);
v___x_4148_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_roots_4146_, v_k_4144_);
if (lean_obj_tag(v___x_4148_) == 0)
{
lean_object* v___x_4150_; uint8_t v_isShared_4151_; uint8_t v_isSharedCheck_4160_; 
lean_inc_ref(v_tries_4147_);
lean_inc_ref(v_roots_4146_);
v_isSharedCheck_4160_ = !lean_is_exclusive(v_d_4143_);
if (v_isSharedCheck_4160_ == 0)
{
lean_object* v_unused_4161_; lean_object* v_unused_4162_; 
v_unused_4161_ = lean_ctor_get(v_d_4143_, 1);
lean_dec(v_unused_4161_);
v_unused_4162_ = lean_ctor_get(v_d_4143_, 0);
lean_dec(v_unused_4162_);
v___x_4150_ = v_d_4143_;
v_isShared_4151_ = v_isSharedCheck_4160_;
goto v_resetjp_4149_;
}
else
{
lean_dec(v_d_4143_);
v___x_4150_ = lean_box(0);
v_isShared_4151_ = v_isSharedCheck_4160_;
goto v_resetjp_4149_;
}
v_resetjp_4149_:
{
lean_object* v___x_4152_; lean_object* v_roots_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4158_; 
v___x_4152_ = lean_array_get_size(v_tries_4147_);
v_roots_4153_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_roots_4146_, v_k_4144_, v___x_4152_);
v___x_4154_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__3));
v___x_4155_ = lean_apply_1(v_f_4145_, v___x_4154_);
v___x_4156_ = lean_array_push(v_tries_4147_, v___x_4155_);
if (v_isShared_4151_ == 0)
{
lean_ctor_set(v___x_4150_, 1, v___x_4156_);
lean_ctor_set(v___x_4150_, 0, v_roots_4153_);
v___x_4158_ = v___x_4150_;
goto v_reusejp_4157_;
}
else
{
lean_object* v_reuseFailAlloc_4159_; 
v_reuseFailAlloc_4159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4159_, 0, v_roots_4153_);
lean_ctor_set(v_reuseFailAlloc_4159_, 1, v___x_4156_);
v___x_4158_ = v_reuseFailAlloc_4159_;
goto v_reusejp_4157_;
}
v_reusejp_4157_:
{
return v___x_4158_;
}
}
}
else
{
lean_object* v_val_4163_; lean_object* v___x_4164_; uint8_t v___x_4165_; 
lean_dec(v_k_4144_);
v_val_4163_ = lean_ctor_get(v___x_4148_, 0);
lean_inc(v_val_4163_);
lean_dec_ref_known(v___x_4148_, 1);
v___x_4164_ = lean_array_get_size(v_tries_4147_);
v___x_4165_ = lean_nat_dec_lt(v_val_4163_, v___x_4164_);
if (v___x_4165_ == 0)
{
lean_dec(v_val_4163_);
lean_dec_ref(v_f_4145_);
return v_d_4143_;
}
else
{
lean_object* v___x_4167_; uint8_t v_isShared_4168_; uint8_t v_isSharedCheck_4177_; 
lean_inc_ref(v_tries_4147_);
lean_inc_ref(v_roots_4146_);
v_isSharedCheck_4177_ = !lean_is_exclusive(v_d_4143_);
if (v_isSharedCheck_4177_ == 0)
{
lean_object* v_unused_4178_; lean_object* v_unused_4179_; 
v_unused_4178_ = lean_ctor_get(v_d_4143_, 1);
lean_dec(v_unused_4178_);
v_unused_4179_ = lean_ctor_get(v_d_4143_, 0);
lean_dec(v_unused_4179_);
v___x_4167_ = v_d_4143_;
v_isShared_4168_ = v_isSharedCheck_4177_;
goto v_resetjp_4166_;
}
else
{
lean_dec(v_d_4143_);
v___x_4167_ = lean_box(0);
v_isShared_4168_ = v_isSharedCheck_4177_;
goto v_resetjp_4166_;
}
v_resetjp_4166_:
{
lean_object* v_v_4169_; lean_object* v___x_4170_; lean_object* v_xs_x27_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4175_; 
v_v_4169_ = lean_array_fget(v_tries_4147_, v_val_4163_);
v___x_4170_ = lean_box(0);
v_xs_x27_4171_ = lean_array_fset(v_tries_4147_, v_val_4163_, v___x_4170_);
v___x_4172_ = lean_apply_1(v_f_4145_, v_v_4169_);
v___x_4173_ = lean_array_fset(v_xs_x27_4171_, v_val_4163_, v___x_4172_);
lean_dec(v_val_4163_);
if (v_isShared_4168_ == 0)
{
lean_ctor_set(v___x_4167_, 1, v___x_4173_);
v___x_4175_ = v___x_4167_;
goto v_reusejp_4174_;
}
else
{
lean_object* v_reuseFailAlloc_4176_; 
v_reuseFailAlloc_4176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4176_, 0, v_roots_4146_);
lean_ctor_set(v_reuseFailAlloc_4176_, 1, v___x_4173_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt(lean_object* v_00_u03b1_4180_, lean_object* v_d_4181_, lean_object* v_k_4182_, lean_object* v_f_4183_){
_start:
{
lean_object* v___x_4184_; 
v___x_4184_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(v_d_4181_, v_k_4182_, v_f_4183_);
return v___x_4184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg___lam__0(lean_object* v_e_4185_, lean_object* v_x_4186_){
_start:
{
lean_object* v___x_4187_; 
v___x_4187_ = lean_array_push(v_x_4186_, v_e_4185_);
return v___x_4187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg(lean_object* v_d_4188_, lean_object* v_k_4189_, lean_object* v_e_4190_){
_start:
{
lean_object* v___f_4191_; lean_object* v___x_4192_; 
v___f_4191_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4191_, 0, v_e_4190_);
v___x_4192_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(v_d_4188_, v_k_4189_, v___f_4191_);
return v___x_4192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push(lean_object* v_00_u03b1_4193_, lean_object* v_d_4194_, lean_object* v_k_4195_, lean_object* v_e_4196_){
_start:
{
lean_object* v___x_4197_; 
v___x_4197_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg(v_d_4194_, v_k_4195_, v_e_4196_);
return v___x_4197_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(size_t v_sz_4198_, size_t v_i_4199_, lean_object* v_bs_4200_){
_start:
{
uint8_t v___x_4201_; 
v___x_4201_ = lean_usize_dec_lt(v_i_4199_, v_sz_4198_);
if (v___x_4201_ == 0)
{
return v_bs_4200_;
}
else
{
lean_object* v_v_4202_; lean_object* v___x_4203_; lean_object* v_bs_x27_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; size_t v___x_4208_; size_t v___x_4209_; lean_object* v___x_4210_; 
v_v_4202_ = lean_array_uget(v_bs_4200_, v_i_4199_);
v___x_4203_ = lean_unsigned_to_nat(0u);
v_bs_x27_4204_ = lean_array_uset(v_bs_4200_, v_i_4199_, v___x_4203_);
v___x_4205_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__0));
v___x_4206_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2);
v___x_4207_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4207_, 0, v___x_4205_);
lean_ctor_set(v___x_4207_, 1, v___x_4203_);
lean_ctor_set(v___x_4207_, 2, v___x_4206_);
lean_ctor_set(v___x_4207_, 3, v_v_4202_);
v___x_4208_ = ((size_t)1ULL);
v___x_4209_ = lean_usize_add(v_i_4199_, v___x_4208_);
v___x_4210_ = lean_array_uset(v_bs_x27_4204_, v_i_4199_, v___x_4207_);
v_i_4199_ = v___x_4209_;
v_bs_4200_ = v___x_4210_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg___boxed(lean_object* v_sz_4212_, lean_object* v_i_4213_, lean_object* v_bs_4214_){
_start:
{
size_t v_sz_boxed_4215_; size_t v_i_boxed_4216_; lean_object* v_res_4217_; 
v_sz_boxed_4215_ = lean_unbox_usize(v_sz_4212_);
lean_dec(v_sz_4212_);
v_i_boxed_4216_ = lean_unbox_usize(v_i_4213_);
lean_dec(v_i_4213_);
v_res_4217_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(v_sz_boxed_4215_, v_i_boxed_4216_, v_bs_4214_);
return v_res_4217_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__1(lean_object* v_x_4218_, lean_object* v_x_4219_){
_start:
{
if (lean_obj_tag(v_x_4219_) == 0)
{
return v_x_4218_;
}
else
{
lean_object* v_key_4220_; lean_object* v_value_4221_; lean_object* v_tail_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; 
v_key_4220_ = lean_ctor_get(v_x_4219_, 0);
lean_inc(v_key_4220_);
v_value_4221_ = lean_ctor_get(v_x_4219_, 1);
lean_inc(v_value_4221_);
v_tail_4222_ = lean_ctor_get(v_x_4219_, 2);
lean_inc(v_tail_4222_);
lean_dec_ref_known(v_x_4219_, 3);
v___x_4223_ = lean_unsigned_to_nat(1u);
v___x_4224_ = lean_nat_add(v_value_4221_, v___x_4223_);
lean_dec(v_value_4221_);
v___x_4225_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_x_4218_, v_key_4220_, v___x_4224_);
v_x_4218_ = v___x_4225_;
v_x_4219_ = v_tail_4222_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(lean_object* v_as_4227_, size_t v_i_4228_, size_t v_stop_4229_, lean_object* v_b_4230_){
_start:
{
uint8_t v___x_4231_; 
v___x_4231_ = lean_usize_dec_eq(v_i_4228_, v_stop_4229_);
if (v___x_4231_ == 0)
{
lean_object* v___x_4232_; lean_object* v___x_4233_; size_t v___x_4234_; size_t v___x_4235_; 
v___x_4232_ = lean_array_uget_borrowed(v_as_4227_, v_i_4228_);
lean_inc(v___x_4232_);
v___x_4233_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__1(v_b_4230_, v___x_4232_);
v___x_4234_ = ((size_t)1ULL);
v___x_4235_ = lean_usize_add(v_i_4228_, v___x_4234_);
v_i_4228_ = v___x_4235_;
v_b_4230_ = v___x_4233_;
goto _start;
}
else
{
return v_b_4230_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2___boxed(lean_object* v_as_4237_, lean_object* v_i_4238_, lean_object* v_stop_4239_, lean_object* v_b_4240_){
_start:
{
size_t v_i_boxed_4241_; size_t v_stop_boxed_4242_; lean_object* v_res_4243_; 
v_i_boxed_4241_ = lean_unbox_usize(v_i_4238_);
lean_dec(v_i_4238_);
v_stop_boxed_4242_ = lean_unbox_usize(v_stop_4239_);
lean_dec(v_stop_4239_);
v_res_4243_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(v_as_4237_, v_i_boxed_4241_, v_stop_boxed_4242_, v_b_4240_);
lean_dec_ref(v_as_4237_);
return v_res_4243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(lean_object* v_d_4244_){
_start:
{
lean_object* v_roots_4245_; lean_object* v_tries_4246_; lean_object* v___x_4248_; uint8_t v_isShared_4249_; uint8_t v_isSharedCheck_4269_; 
v_roots_4245_ = lean_ctor_get(v_d_4244_, 0);
v_tries_4246_ = lean_ctor_get(v_d_4244_, 1);
v_isSharedCheck_4269_ = !lean_is_exclusive(v_d_4244_);
if (v_isSharedCheck_4269_ == 0)
{
v___x_4248_ = v_d_4244_;
v_isShared_4249_ = v_isSharedCheck_4269_;
goto v_resetjp_4247_;
}
else
{
lean_inc(v_tries_4246_);
lean_inc(v_roots_4245_);
lean_dec(v_d_4244_);
v___x_4248_ = lean_box(0);
v_isShared_4249_ = v_isSharedCheck_4269_;
goto v_resetjp_4247_;
}
v_resetjp_4247_:
{
lean_object* v___y_4251_; lean_object* v_buckets_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; uint8_t v___x_4265_; 
v_buckets_4262_ = lean_ctor_get(v_roots_4245_, 1);
v___x_4263_ = lean_unsigned_to_nat(0u);
v___x_4264_ = lean_array_get_size(v_buckets_4262_);
v___x_4265_ = lean_nat_dec_lt(v___x_4263_, v___x_4264_);
if (v___x_4265_ == 0)
{
v___y_4251_ = v_roots_4245_;
goto v___jp_4250_;
}
else
{
size_t v___x_4266_; size_t v___x_4267_; lean_object* v___x_4268_; 
lean_inc_ref(v_buckets_4262_);
v___x_4266_ = ((size_t)0ULL);
v___x_4267_ = lean_usize_of_nat(v___x_4264_);
v___x_4268_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(v_buckets_4262_, v___x_4266_, v___x_4267_, v_roots_4245_);
lean_dec_ref(v_buckets_4262_);
v___y_4251_ = v___x_4268_;
goto v___jp_4250_;
}
v___jp_4250_:
{
lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; size_t v_sz_4255_; size_t v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4260_; 
v___x_4252_ = lean_unsigned_to_nat(1u);
v___x_4253_ = lean_mk_empty_array_with_capacity(v___x_4252_);
lean_dec_ref(v___x_4253_);
v___x_4254_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__0);
v_sz_4255_ = lean_array_size(v_tries_4246_);
v___x_4256_ = ((size_t)0ULL);
v___x_4257_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(v_sz_4255_, v___x_4256_, v_tries_4246_);
v___x_4258_ = l_Array_append___redArg(v___x_4254_, v___x_4257_);
lean_dec_ref(v___x_4257_);
if (v_isShared_4249_ == 0)
{
lean_ctor_set(v___x_4248_, 1, v___y_4251_);
lean_ctor_set(v___x_4248_, 0, v___x_4258_);
v___x_4260_ = v___x_4248_;
goto v_reusejp_4259_;
}
else
{
lean_object* v_reuseFailAlloc_4261_; 
v_reuseFailAlloc_4261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4261_, 0, v___x_4258_);
lean_ctor_set(v_reuseFailAlloc_4261_, 1, v___y_4251_);
v___x_4260_ = v_reuseFailAlloc_4261_;
goto v_reusejp_4259_;
}
v_reusejp_4259_:
{
return v___x_4260_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy(lean_object* v_00_u03b1_4270_, lean_object* v_d_4271_){
_start:
{
lean_object* v___x_4272_; 
v___x_4272_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_d_4271_);
return v___x_4272_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0(lean_object* v_00_u03b1_4273_, size_t v_sz_4274_, size_t v_i_4275_, lean_object* v_bs_4276_){
_start:
{
lean_object* v___x_4277_; 
v___x_4277_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(v_sz_4274_, v_i_4275_, v_bs_4276_);
return v___x_4277_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___boxed(lean_object* v_00_u03b1_4278_, lean_object* v_sz_4279_, lean_object* v_i_4280_, lean_object* v_bs_4281_){
_start:
{
size_t v_sz_boxed_4282_; size_t v_i_boxed_4283_; lean_object* v_res_4284_; 
v_sz_boxed_4282_ = lean_unbox_usize(v_sz_4279_);
lean_dec(v_sz_4279_);
v_i_boxed_4283_ = lean_unbox_usize(v_i_4280_);
lean_dec(v_i_4280_);
v_res_4284_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0(v_00_u03b1_4278_, v_sz_boxed_4282_, v_i_boxed_4283_, v_bs_4281_);
return v_res_4284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___lam__0(lean_object* v_y_4285_, lean_object* v_x_4286_){
_start:
{
lean_object* v___x_4287_; 
v___x_4287_ = l_Array_append___redArg(v_x_4286_, v_y_4285_);
return v___x_4287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___lam__0___boxed(lean_object* v_y_4288_, lean_object* v_x_4289_){
_start:
{
lean_object* v_res_4290_; 
v_res_4290_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___lam__0(v_y_4288_, v_x_4289_);
lean_dec_ref(v_y_4288_);
return v_res_4290_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4291_; 
v___x_4291_ = l_Array_instInhabited___redArg();
return v___x_4291_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(lean_object* v_tries_4292_, lean_object* v_snd_4293_, lean_object* v_x_4294_, lean_object* v_x_4295_){
_start:
{
if (lean_obj_tag(v_x_4295_) == 0)
{
lean_dec_ref(v_snd_4293_);
return v_x_4294_;
}
else
{
lean_object* v_key_4296_; lean_object* v_value_4297_; lean_object* v_tail_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; 
v_key_4296_ = lean_ctor_get(v_x_4295_, 0);
lean_inc(v_key_4296_);
v_value_4297_ = lean_ctor_get(v_x_4295_, 1);
lean_inc(v_value_4297_);
v_tail_4298_ = lean_ctor_get(v_x_4295_, 2);
lean_inc(v_tail_4298_);
lean_dec_ref_known(v_x_4295_, 3);
v___x_4299_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0);
v___x_4300_ = lean_array_get_borrowed(v___x_4299_, v_tries_4292_, v_value_4297_);
lean_dec(v_value_4297_);
lean_inc_ref(v_snd_4293_);
lean_inc(v___x_4300_);
v___x_4301_ = lean_apply_1(v_snd_4293_, v___x_4300_);
v___x_4302_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(v_x_4294_, v_key_4296_, v___x_4301_);
v_x_4294_ = v___x_4302_;
v_x_4295_ = v_tail_4298_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___boxed(lean_object* v_tries_4304_, lean_object* v_snd_4305_, lean_object* v_x_4306_, lean_object* v_x_4307_){
_start:
{
lean_object* v_res_4308_; 
v_res_4308_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(v_tries_4304_, v_snd_4305_, v_x_4306_, v_x_4307_);
lean_dec_ref(v_tries_4304_);
return v_res_4308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(lean_object* v_tries_4309_, lean_object* v_snd_4310_, lean_object* v_as_4311_, size_t v_i_4312_, size_t v_stop_4313_, lean_object* v_b_4314_){
_start:
{
uint8_t v___x_4315_; 
v___x_4315_ = lean_usize_dec_eq(v_i_4312_, v_stop_4313_);
if (v___x_4315_ == 0)
{
lean_object* v___x_4316_; lean_object* v___x_4317_; size_t v___x_4318_; size_t v___x_4319_; 
v___x_4316_ = lean_array_uget_borrowed(v_as_4311_, v_i_4312_);
lean_inc(v___x_4316_);
lean_inc_ref(v_snd_4310_);
v___x_4317_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(v_tries_4309_, v_snd_4310_, v_b_4314_, v___x_4316_);
v___x_4318_ = ((size_t)1ULL);
v___x_4319_ = lean_usize_add(v_i_4312_, v___x_4318_);
v_i_4312_ = v___x_4319_;
v_b_4314_ = v___x_4317_;
goto _start;
}
else
{
lean_dec_ref(v_snd_4310_);
return v_b_4314_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg___boxed(lean_object* v_tries_4321_, lean_object* v_snd_4322_, lean_object* v_as_4323_, lean_object* v_i_4324_, lean_object* v_stop_4325_, lean_object* v_b_4326_){
_start:
{
size_t v_i_boxed_4327_; size_t v_stop_boxed_4328_; lean_object* v_res_4329_; 
v_i_boxed_4327_ = lean_unbox_usize(v_i_4324_);
lean_dec(v_i_4324_);
v_stop_boxed_4328_ = lean_unbox_usize(v_stop_4325_);
lean_dec(v_stop_4325_);
v_res_4329_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(v_tries_4321_, v_snd_4322_, v_as_4323_, v_i_boxed_4327_, v_stop_boxed_4328_, v_b_4326_);
lean_dec_ref(v_as_4323_);
lean_dec_ref(v_tries_4321_);
return v_res_4329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg(lean_object* v_x_4332_, lean_object* v_y_4333_){
_start:
{
lean_object* v_fst_4335_; lean_object* v_buckets_4336_; lean_object* v_tries_4337_; lean_object* v_snd_4338_; lean_object* v_roots_4345_; lean_object* v_roots_4346_; lean_object* v_tries_4347_; lean_object* v_size_4348_; lean_object* v_buckets_4349_; lean_object* v_tries_4350_; lean_object* v_size_4351_; lean_object* v_buckets_4352_; uint8_t v___x_4353_; 
v_roots_4345_ = lean_ctor_get(v_y_4333_, 0);
v_roots_4346_ = lean_ctor_get(v_x_4332_, 0);
v_tries_4347_ = lean_ctor_get(v_y_4333_, 1);
v_size_4348_ = lean_ctor_get(v_roots_4345_, 0);
v_buckets_4349_ = lean_ctor_get(v_roots_4345_, 1);
v_tries_4350_ = lean_ctor_get(v_x_4332_, 1);
v_size_4351_ = lean_ctor_get(v_roots_4346_, 0);
v_buckets_4352_ = lean_ctor_get(v_roots_4346_, 1);
v___x_4353_ = lean_nat_dec_le(v_size_4348_, v_size_4351_);
if (v___x_4353_ == 0)
{
lean_object* v___f_4354_; 
lean_inc_ref(v_buckets_4352_);
lean_inc_ref(v_tries_4350_);
lean_dec_ref(v_x_4332_);
v___f_4354_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___closed__0));
v_fst_4335_ = v_y_4333_;
v_buckets_4336_ = v_buckets_4352_;
v_tries_4337_ = v_tries_4350_;
v_snd_4338_ = v___f_4354_;
goto v___jp_4334_;
}
else
{
lean_object* v___f_4355_; 
lean_inc_ref(v_buckets_4349_);
lean_inc_ref(v_tries_4347_);
lean_dec_ref(v_y_4333_);
v___f_4355_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___closed__1));
v_fst_4335_ = v_x_4332_;
v_buckets_4336_ = v_buckets_4349_;
v_tries_4337_ = v_tries_4347_;
v_snd_4338_ = v___f_4355_;
goto v___jp_4334_;
}
v___jp_4334_:
{
lean_object* v___x_4339_; lean_object* v___x_4340_; uint8_t v___x_4341_; 
v___x_4339_ = lean_unsigned_to_nat(0u);
v___x_4340_ = lean_array_get_size(v_buckets_4336_);
v___x_4341_ = lean_nat_dec_lt(v___x_4339_, v___x_4340_);
if (v___x_4341_ == 0)
{
lean_dec_ref(v_tries_4337_);
lean_dec_ref(v_buckets_4336_);
return v_fst_4335_;
}
else
{
size_t v___x_4342_; size_t v___x_4343_; lean_object* v___x_4344_; 
v___x_4342_ = ((size_t)0ULL);
v___x_4343_ = lean_usize_of_nat(v___x_4340_);
lean_inc_ref(v_snd_4338_);
v___x_4344_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(v_tries_4337_, v_snd_4338_, v_buckets_4336_, v___x_4342_, v___x_4343_, v_fst_4335_);
lean_dec_ref(v_buckets_4336_);
lean_dec_ref(v_tries_4337_);
return v___x_4344_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append(lean_object* v_00_u03b1_4356_, lean_object* v_x_4357_, lean_object* v_y_4358_){
_start:
{
lean_object* v___x_4359_; 
v___x_4359_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg(v_x_4357_, v_y_4358_);
return v___x_4359_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0(lean_object* v_00_u03b1_4360_, lean_object* v_tries_4361_, lean_object* v_snd_4362_, lean_object* v_x_4363_, lean_object* v_x_4364_){
_start:
{
lean_object* v___x_4365_; 
v___x_4365_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(v_tries_4361_, v_snd_4362_, v_x_4363_, v_x_4364_);
return v___x_4365_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___boxed(lean_object* v_00_u03b1_4366_, lean_object* v_tries_4367_, lean_object* v_snd_4368_, lean_object* v_x_4369_, lean_object* v_x_4370_){
_start:
{
lean_object* v_res_4371_; 
v_res_4371_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0(v_00_u03b1_4366_, v_tries_4367_, v_snd_4368_, v_x_4369_, v_x_4370_);
lean_dec_ref(v_tries_4367_);
return v_res_4371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1(lean_object* v_00_u03b1_4372_, lean_object* v_tries_4373_, lean_object* v_snd_4374_, lean_object* v_as_4375_, size_t v_i_4376_, size_t v_stop_4377_, lean_object* v_b_4378_){
_start:
{
lean_object* v___x_4379_; 
v___x_4379_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(v_tries_4373_, v_snd_4374_, v_as_4375_, v_i_4376_, v_stop_4377_, v_b_4378_);
return v___x_4379_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___boxed(lean_object* v_00_u03b1_4380_, lean_object* v_tries_4381_, lean_object* v_snd_4382_, lean_object* v_as_4383_, lean_object* v_i_4384_, lean_object* v_stop_4385_, lean_object* v_b_4386_){
_start:
{
size_t v_i_boxed_4387_; size_t v_stop_boxed_4388_; lean_object* v_res_4389_; 
v_i_boxed_4387_ = lean_unbox_usize(v_i_4384_);
lean_dec(v_i_4384_);
v_stop_boxed_4388_ = lean_unbox_usize(v_stop_4385_);
lean_dec(v_stop_4385_);
v_res_4389_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1(v_00_u03b1_4380_, v_tries_4381_, v_snd_4382_, v_as_4383_, v_i_boxed_4387_, v_stop_boxed_4388_, v_b_4386_);
lean_dec_ref(v_as_4383_);
lean_dec_ref(v_tries_4381_);
return v_res_4389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend___redArg(){
_start:
{
lean_object* v___x_4392_; 
v___x_4392_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend___redArg___closed__0));
return v___x_4392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend___redArg___boxed(lean_object* v___dummy_4393_){
_start:
{
lean_object* v_res_4394_; 
v_res_4394_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend___redArg();
return v_res_4394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend(lean_object* v_00_u03b1_4395_){
_start:
{
lean_object* v___x_4396_; 
v___x_4396_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend___redArg___closed__0));
return v___x_4396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(lean_object* v_expr_4397_, lean_object* v_value_4398_, lean_object* v_a_4399_, lean_object* v_a_4400_, lean_object* v_a_4401_, lean_object* v_a_4402_){
_start:
{
lean_object* v_lctx_4404_; lean_object* v_localInstances_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; 
v_lctx_4404_ = lean_ctor_get(v_a_4399_, 2);
v_localInstances_4405_ = lean_ctor_get(v_a_4399_, 3);
lean_inc_ref(v_localInstances_4405_);
lean_inc_ref(v_lctx_4404_);
v___x_4406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4406_, 0, v_lctx_4404_);
lean_ctor_set(v___x_4406_, 1, v_localInstances_4405_);
v___x_4407_ = l_Lean_Meta_LazyDiscrTree_rootKey(v_expr_4397_, v_a_4399_, v_a_4400_, v_a_4401_, v_a_4402_);
if (lean_obj_tag(v___x_4407_) == 0)
{
lean_object* v_a_4408_; lean_object* v___x_4410_; uint8_t v_isShared_4411_; uint8_t v_isSharedCheck_4426_; 
v_a_4408_ = lean_ctor_get(v___x_4407_, 0);
v_isSharedCheck_4426_ = !lean_is_exclusive(v___x_4407_);
if (v_isSharedCheck_4426_ == 0)
{
v___x_4410_ = v___x_4407_;
v_isShared_4411_ = v_isSharedCheck_4426_;
goto v_resetjp_4409_;
}
else
{
lean_inc(v_a_4408_);
lean_dec(v___x_4407_);
v___x_4410_ = lean_box(0);
v_isShared_4411_ = v_isSharedCheck_4426_;
goto v_resetjp_4409_;
}
v_resetjp_4409_:
{
lean_object* v_fst_4412_; lean_object* v_snd_4413_; lean_object* v___x_4415_; uint8_t v_isShared_4416_; uint8_t v_isSharedCheck_4425_; 
v_fst_4412_ = lean_ctor_get(v_a_4408_, 0);
v_snd_4413_ = lean_ctor_get(v_a_4408_, 1);
v_isSharedCheck_4425_ = !lean_is_exclusive(v_a_4408_);
if (v_isSharedCheck_4425_ == 0)
{
v___x_4415_ = v_a_4408_;
v_isShared_4416_ = v_isSharedCheck_4425_;
goto v_resetjp_4414_;
}
else
{
lean_inc(v_snd_4413_);
lean_inc(v_fst_4412_);
lean_dec(v_a_4408_);
v___x_4415_ = lean_box(0);
v_isShared_4416_ = v_isSharedCheck_4425_;
goto v_resetjp_4414_;
}
v_resetjp_4414_:
{
lean_object* v___x_4418_; 
if (v_isShared_4416_ == 0)
{
lean_ctor_set(v___x_4415_, 1, v_value_4398_);
lean_ctor_set(v___x_4415_, 0, v___x_4406_);
v___x_4418_ = v___x_4415_;
goto v_reusejp_4417_;
}
else
{
lean_object* v_reuseFailAlloc_4424_; 
v_reuseFailAlloc_4424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4424_, 0, v___x_4406_);
lean_ctor_set(v_reuseFailAlloc_4424_, 1, v_value_4398_);
v___x_4418_ = v_reuseFailAlloc_4424_;
goto v_reusejp_4417_;
}
v_reusejp_4417_:
{
lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4422_; 
v___x_4419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4419_, 0, v_snd_4413_);
lean_ctor_set(v___x_4419_, 1, v___x_4418_);
v___x_4420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4420_, 0, v_fst_4412_);
lean_ctor_set(v___x_4420_, 1, v___x_4419_);
if (v_isShared_4411_ == 0)
{
lean_ctor_set(v___x_4410_, 0, v___x_4420_);
v___x_4422_ = v___x_4410_;
goto v_reusejp_4421_;
}
else
{
lean_object* v_reuseFailAlloc_4423_; 
v_reuseFailAlloc_4423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4423_, 0, v___x_4420_);
v___x_4422_ = v_reuseFailAlloc_4423_;
goto v_reusejp_4421_;
}
v_reusejp_4421_:
{
return v___x_4422_;
}
}
}
}
}
else
{
lean_object* v_a_4427_; lean_object* v___x_4429_; uint8_t v_isShared_4430_; uint8_t v_isSharedCheck_4434_; 
lean_dec_ref_known(v___x_4406_, 2);
lean_dec(v_value_4398_);
v_a_4427_ = lean_ctor_get(v___x_4407_, 0);
v_isSharedCheck_4434_ = !lean_is_exclusive(v___x_4407_);
if (v_isSharedCheck_4434_ == 0)
{
v___x_4429_ = v___x_4407_;
v_isShared_4430_ = v_isSharedCheck_4434_;
goto v_resetjp_4428_;
}
else
{
lean_inc(v_a_4427_);
lean_dec(v___x_4407_);
v___x_4429_ = lean_box(0);
v_isShared_4430_ = v_isSharedCheck_4434_;
goto v_resetjp_4428_;
}
v_resetjp_4428_:
{
lean_object* v___x_4432_; 
if (v_isShared_4430_ == 0)
{
v___x_4432_ = v___x_4429_;
goto v_reusejp_4431_;
}
else
{
lean_object* v_reuseFailAlloc_4433_; 
v_reuseFailAlloc_4433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4433_, 0, v_a_4427_);
v___x_4432_ = v_reuseFailAlloc_4433_;
goto v_reusejp_4431_;
}
v_reusejp_4431_:
{
return v___x_4432_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg___boxed(lean_object* v_expr_4435_, lean_object* v_value_4436_, lean_object* v_a_4437_, lean_object* v_a_4438_, lean_object* v_a_4439_, lean_object* v_a_4440_, lean_object* v_a_4441_){
_start:
{
lean_object* v_res_4442_; 
v_res_4442_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(v_expr_4435_, v_value_4436_, v_a_4437_, v_a_4438_, v_a_4439_, v_a_4440_);
lean_dec(v_a_4440_);
lean_dec_ref(v_a_4439_);
lean_dec(v_a_4438_);
lean_dec_ref(v_a_4437_);
return v_res_4442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr(lean_object* v_00_u03b1_4443_, lean_object* v_expr_4444_, lean_object* v_value_4445_, lean_object* v_a_4446_, lean_object* v_a_4447_, lean_object* v_a_4448_, lean_object* v_a_4449_){
_start:
{
lean_object* v___x_4451_; 
v___x_4451_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(v_expr_4444_, v_value_4445_, v_a_4446_, v_a_4447_, v_a_4448_, v_a_4449_);
return v___x_4451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___boxed(lean_object* v_00_u03b1_4452_, lean_object* v_expr_4453_, lean_object* v_value_4454_, lean_object* v_a_4455_, lean_object* v_a_4456_, lean_object* v_a_4457_, lean_object* v_a_4458_, lean_object* v_a_4459_){
_start:
{
lean_object* v_res_4460_; 
v_res_4460_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr(v_00_u03b1_4452_, v_expr_4453_, v_value_4454_, v_a_4455_, v_a_4456_, v_a_4457_, v_a_4458_);
lean_dec(v_a_4458_);
lean_dec_ref(v_a_4457_);
lean_dec(v_a_4456_);
lean_dec_ref(v_a_4455_);
return v_res_4460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(lean_object* v_e_4461_, lean_object* v_idx_4462_, lean_object* v_value_4463_, lean_object* v_a_4464_, lean_object* v_a_4465_, lean_object* v_a_4466_, lean_object* v_a_4467_){
_start:
{
lean_object* v_entry_4469_; lean_object* v___x_4471_; uint8_t v_isShared_4472_; uint8_t v_isSharedCheck_4515_; 
v_entry_4469_ = lean_ctor_get(v_e_4461_, 1);
v_isSharedCheck_4515_ = !lean_is_exclusive(v_e_4461_);
if (v_isSharedCheck_4515_ == 0)
{
lean_object* v_unused_4516_; 
v_unused_4516_ = lean_ctor_get(v_e_4461_, 0);
lean_dec(v_unused_4516_);
v___x_4471_ = v_e_4461_;
v_isShared_4472_ = v_isSharedCheck_4515_;
goto v_resetjp_4470_;
}
else
{
lean_inc(v_entry_4469_);
lean_dec(v_e_4461_);
v___x_4471_ = lean_box(0);
v_isShared_4472_ = v_isSharedCheck_4515_;
goto v_resetjp_4470_;
}
v_resetjp_4470_:
{
lean_object* v_snd_4473_; lean_object* v_fst_4474_; lean_object* v_fst_4475_; lean_object* v___x_4477_; uint8_t v_isShared_4478_; uint8_t v_isSharedCheck_4513_; 
v_snd_4473_ = lean_ctor_get(v_entry_4469_, 1);
lean_inc(v_snd_4473_);
v_fst_4474_ = lean_ctor_get(v_entry_4469_, 0);
lean_inc(v_fst_4474_);
lean_dec_ref(v_entry_4469_);
v_fst_4475_ = lean_ctor_get(v_snd_4473_, 0);
v_isSharedCheck_4513_ = !lean_is_exclusive(v_snd_4473_);
if (v_isSharedCheck_4513_ == 0)
{
lean_object* v_unused_4514_; 
v_unused_4514_ = lean_ctor_get(v_snd_4473_, 1);
lean_dec(v_unused_4514_);
v___x_4477_ = v_snd_4473_;
v_isShared_4478_ = v_isSharedCheck_4513_;
goto v_resetjp_4476_;
}
else
{
lean_inc(v_fst_4475_);
lean_dec(v_snd_4473_);
v___x_4477_ = lean_box(0);
v_isShared_4478_ = v_isSharedCheck_4513_;
goto v_resetjp_4476_;
}
v_resetjp_4476_:
{
lean_object* v___x_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; 
v___x_4479_ = l_Lean_instInhabitedExpr;
v___x_4480_ = lean_array_get(v___x_4479_, v_fst_4474_, v_idx_4462_);
lean_dec(v_fst_4474_);
v___x_4481_ = l_Lean_Meta_LazyDiscrTree_rootKey(v___x_4480_, v_a_4464_, v_a_4465_, v_a_4466_, v_a_4467_);
if (lean_obj_tag(v___x_4481_) == 0)
{
lean_object* v_a_4482_; lean_object* v___x_4484_; uint8_t v_isShared_4485_; uint8_t v_isSharedCheck_4504_; 
v_a_4482_ = lean_ctor_get(v___x_4481_, 0);
v_isSharedCheck_4504_ = !lean_is_exclusive(v___x_4481_);
if (v_isSharedCheck_4504_ == 0)
{
v___x_4484_ = v___x_4481_;
v_isShared_4485_ = v_isSharedCheck_4504_;
goto v_resetjp_4483_;
}
else
{
lean_inc(v_a_4482_);
lean_dec(v___x_4481_);
v___x_4484_ = lean_box(0);
v_isShared_4485_ = v_isSharedCheck_4504_;
goto v_resetjp_4483_;
}
v_resetjp_4483_:
{
lean_object* v_fst_4486_; lean_object* v_snd_4487_; lean_object* v___x_4489_; uint8_t v_isShared_4490_; uint8_t v_isSharedCheck_4503_; 
v_fst_4486_ = lean_ctor_get(v_a_4482_, 0);
v_snd_4487_ = lean_ctor_get(v_a_4482_, 1);
v_isSharedCheck_4503_ = !lean_is_exclusive(v_a_4482_);
if (v_isSharedCheck_4503_ == 0)
{
v___x_4489_ = v_a_4482_;
v_isShared_4490_ = v_isSharedCheck_4503_;
goto v_resetjp_4488_;
}
else
{
lean_inc(v_snd_4487_);
lean_inc(v_fst_4486_);
lean_dec(v_a_4482_);
v___x_4489_ = lean_box(0);
v_isShared_4490_ = v_isSharedCheck_4503_;
goto v_resetjp_4488_;
}
v_resetjp_4488_:
{
lean_object* v___x_4492_; 
if (v_isShared_4490_ == 0)
{
lean_ctor_set(v___x_4489_, 1, v_value_4463_);
lean_ctor_set(v___x_4489_, 0, v_fst_4475_);
v___x_4492_ = v___x_4489_;
goto v_reusejp_4491_;
}
else
{
lean_object* v_reuseFailAlloc_4502_; 
v_reuseFailAlloc_4502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4502_, 0, v_fst_4475_);
lean_ctor_set(v_reuseFailAlloc_4502_, 1, v_value_4463_);
v___x_4492_ = v_reuseFailAlloc_4502_;
goto v_reusejp_4491_;
}
v_reusejp_4491_:
{
lean_object* v___x_4494_; 
if (v_isShared_4478_ == 0)
{
lean_ctor_set(v___x_4477_, 1, v___x_4492_);
lean_ctor_set(v___x_4477_, 0, v_snd_4487_);
v___x_4494_ = v___x_4477_;
goto v_reusejp_4493_;
}
else
{
lean_object* v_reuseFailAlloc_4501_; 
v_reuseFailAlloc_4501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4501_, 0, v_snd_4487_);
lean_ctor_set(v_reuseFailAlloc_4501_, 1, v___x_4492_);
v___x_4494_ = v_reuseFailAlloc_4501_;
goto v_reusejp_4493_;
}
v_reusejp_4493_:
{
lean_object* v___x_4496_; 
if (v_isShared_4472_ == 0)
{
lean_ctor_set(v___x_4471_, 1, v___x_4494_);
lean_ctor_set(v___x_4471_, 0, v_fst_4486_);
v___x_4496_ = v___x_4471_;
goto v_reusejp_4495_;
}
else
{
lean_object* v_reuseFailAlloc_4500_; 
v_reuseFailAlloc_4500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4500_, 0, v_fst_4486_);
lean_ctor_set(v_reuseFailAlloc_4500_, 1, v___x_4494_);
v___x_4496_ = v_reuseFailAlloc_4500_;
goto v_reusejp_4495_;
}
v_reusejp_4495_:
{
lean_object* v___x_4498_; 
if (v_isShared_4485_ == 0)
{
lean_ctor_set(v___x_4484_, 0, v___x_4496_);
v___x_4498_ = v___x_4484_;
goto v_reusejp_4497_;
}
else
{
lean_object* v_reuseFailAlloc_4499_; 
v_reuseFailAlloc_4499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4499_, 0, v___x_4496_);
v___x_4498_ = v_reuseFailAlloc_4499_;
goto v_reusejp_4497_;
}
v_reusejp_4497_:
{
return v___x_4498_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4505_; lean_object* v___x_4507_; uint8_t v_isShared_4508_; uint8_t v_isSharedCheck_4512_; 
lean_del_object(v___x_4477_);
lean_dec(v_fst_4475_);
lean_del_object(v___x_4471_);
lean_dec(v_value_4463_);
v_a_4505_ = lean_ctor_get(v___x_4481_, 0);
v_isSharedCheck_4512_ = !lean_is_exclusive(v___x_4481_);
if (v_isSharedCheck_4512_ == 0)
{
v___x_4507_ = v___x_4481_;
v_isShared_4508_ = v_isSharedCheck_4512_;
goto v_resetjp_4506_;
}
else
{
lean_inc(v_a_4505_);
lean_dec(v___x_4481_);
v___x_4507_ = lean_box(0);
v_isShared_4508_ = v_isSharedCheck_4512_;
goto v_resetjp_4506_;
}
v_resetjp_4506_:
{
lean_object* v___x_4510_; 
if (v_isShared_4508_ == 0)
{
v___x_4510_ = v___x_4507_;
goto v_reusejp_4509_;
}
else
{
lean_object* v_reuseFailAlloc_4511_; 
v_reuseFailAlloc_4511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4511_, 0, v_a_4505_);
v___x_4510_ = v_reuseFailAlloc_4511_;
goto v_reusejp_4509_;
}
v_reusejp_4509_:
{
return v___x_4510_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg___boxed(lean_object* v_e_4517_, lean_object* v_idx_4518_, lean_object* v_value_4519_, lean_object* v_a_4520_, lean_object* v_a_4521_, lean_object* v_a_4522_, lean_object* v_a_4523_, lean_object* v_a_4524_){
_start:
{
lean_object* v_res_4525_; 
v_res_4525_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(v_e_4517_, v_idx_4518_, v_value_4519_, v_a_4520_, v_a_4521_, v_a_4522_, v_a_4523_);
lean_dec(v_a_4523_);
lean_dec_ref(v_a_4522_);
lean_dec(v_a_4521_);
lean_dec_ref(v_a_4520_);
lean_dec(v_idx_4518_);
return v_res_4525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry(lean_object* v_00_u03b1_4526_, lean_object* v_e_4527_, lean_object* v_idx_4528_, lean_object* v_value_4529_, lean_object* v_a_4530_, lean_object* v_a_4531_, lean_object* v_a_4532_, lean_object* v_a_4533_){
_start:
{
lean_object* v___x_4535_; 
v___x_4535_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(v_e_4527_, v_idx_4528_, v_value_4529_, v_a_4530_, v_a_4531_, v_a_4532_, v_a_4533_);
return v___x_4535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___boxed(lean_object* v_00_u03b1_4536_, lean_object* v_e_4537_, lean_object* v_idx_4538_, lean_object* v_value_4539_, lean_object* v_a_4540_, lean_object* v_a_4541_, lean_object* v_a_4542_, lean_object* v_a_4543_, lean_object* v_a_4544_){
_start:
{
lean_object* v_res_4545_; 
v_res_4545_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry(v_00_u03b1_4536_, v_e_4537_, v_idx_4538_, v_value_4539_, v_a_4540_, v_a_4541_, v_a_4542_, v_a_4543_);
lean_dec(v_a_4543_);
lean_dec_ref(v_a_4542_);
lean_dec(v_a_4541_);
lean_dec_ref(v_a_4540_);
lean_dec(v_idx_4538_);
return v_res_4545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_ImportData_new(){
_start:
{
lean_object* v___x_4549_; lean_object* v___x_4550_; 
v___x_4549_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_ImportData_new___closed__0));
v___x_4550_ = lean_st_mk_ref(v___x_4549_);
return v___x_4550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_ImportData_new___boxed(lean_object* v_a_4551_){
_start:
{
lean_object* v_res_4552_; 
v_res_4552_ = l_Lean_Meta_LazyDiscrTree_ImportData_new();
return v_res_4552_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0(void){
_start:
{
lean_object* v___x_4553_; 
v___x_4553_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_4553_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1(void){
_start:
{
lean_object* v___x_4554_; lean_object* v___x_4555_; 
v___x_4554_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0);
v___x_4555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4555_, 0, v___x_4554_);
return v___x_4555_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2(void){
_start:
{
lean_object* v___x_4556_; lean_object* v___x_4557_; 
v___x_4556_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1);
v___x_4557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4557_, 0, v___x_4556_);
lean_ctor_set(v___x_4557_, 1, v___x_4556_);
return v___x_4557_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3(void){
_start:
{
lean_object* v___x_4558_; lean_object* v___x_4559_; 
v___x_4558_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1);
v___x_4559_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4559_, 0, v___x_4558_);
lean_ctor_set(v___x_4559_, 1, v___x_4558_);
lean_ctor_set(v___x_4559_, 2, v___x_4558_);
lean_ctor_set(v___x_4559_, 3, v___x_4558_);
lean_ctor_set(v___x_4559_, 4, v___x_4558_);
lean_ctor_set(v___x_4559_, 5, v___x_4558_);
return v___x_4559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Cache_empty(lean_object* v_ngen_4560_){
_start:
{
lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; 
v___x_4561_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2);
v___x_4562_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3);
v___x_4563_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4563_, 0, v_ngen_4560_);
lean_ctor_set(v___x_4563_, 1, v___x_4561_);
lean_ctor_set(v___x_4563_, 2, v___x_4562_);
return v___x_4563_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName(lean_object* v_env_4564_, lean_object* v_declName_4565_){
_start:
{
uint8_t v___x_4566_; 
v___x_4566_ = l_Lean_isPrivateName(v_declName_4565_);
if (v___x_4566_ == 0)
{
return v___x_4566_;
}
else
{
lean_object* v___x_4567_; 
v___x_4567_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4564_, v_declName_4565_);
if (lean_obj_tag(v___x_4567_) == 0)
{
return v___x_4566_;
}
else
{
lean_object* v_val_4568_; lean_object* v___x_4569_; uint8_t v_isModule_4570_; lean_object* v_modules_4571_; uint8_t v___x_4572_; 
v_val_4568_ = lean_ctor_get(v___x_4567_, 0);
lean_inc(v_val_4568_);
lean_dec_ref_known(v___x_4567_, 1);
v___x_4569_ = l_Lean_Environment_header(v_env_4564_);
v_isModule_4570_ = lean_ctor_get_uint8(v___x_4569_, sizeof(void*)*7 + 4);
v_modules_4571_ = lean_ctor_get(v___x_4569_, 3);
lean_inc_ref(v_modules_4571_);
lean_dec_ref(v___x_4569_);
v___x_4572_ = 0;
if (v_isModule_4570_ == 0)
{
lean_dec_ref(v_modules_4571_);
lean_dec(v_val_4568_);
return v___x_4572_;
}
else
{
lean_object* v___x_4573_; uint8_t v___x_4574_; 
v___x_4573_ = lean_array_get_size(v_modules_4571_);
v___x_4574_ = lean_nat_dec_lt(v_val_4568_, v___x_4573_);
if (v___x_4574_ == 0)
{
lean_dec_ref(v_modules_4571_);
lean_dec(v_val_4568_);
return v___x_4572_;
}
else
{
lean_object* v___x_4575_; lean_object* v_toImport_4576_; uint8_t v_importAll_4577_; 
v___x_4575_ = lean_array_fget(v_modules_4571_, v_val_4568_);
lean_dec(v_val_4568_);
lean_dec_ref(v_modules_4571_);
v_toImport_4576_ = lean_ctor_get(v___x_4575_, 0);
lean_inc_ref(v_toImport_4576_);
lean_dec(v___x_4575_);
v_importAll_4577_ = lean_ctor_get_uint8(v_toImport_4576_, sizeof(void*)*1);
lean_dec_ref(v_toImport_4576_);
return v_importAll_4577_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName___boxed(lean_object* v_env_4578_, lean_object* v_declName_4579_){
_start:
{
uint8_t v_res_4580_; lean_object* v_r_4581_; 
v_res_4580_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName(v_env_4578_, v_declName_4579_);
lean_dec(v_declName_4579_);
lean_dec_ref(v_env_4578_);
v_r_4581_ = lean_box(v_res_4580_);
return v_r_4581_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_LazyDiscrTree_blacklistInsertion(lean_object* v_env_4587_, lean_object* v_declName_4588_){
_start:
{
uint8_t v___x_4589_; 
lean_inc(v_declName_4588_);
lean_inc_ref(v_env_4587_);
v___x_4589_ = l_Lean_Meta_allowCompletion(v_env_4587_, v_declName_4588_);
if (v___x_4589_ == 0)
{
uint8_t v___x_4590_; 
lean_dec(v_declName_4588_);
lean_dec_ref(v_env_4587_);
v___x_4590_ = 1;
return v___x_4590_;
}
else
{
lean_object* v___x_4591_; uint8_t v___x_4592_; uint8_t v___y_4602_; 
v___x_4591_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__1));
v___x_4592_ = lean_name_eq(v_declName_4588_, v___x_4591_);
if (v___x_4592_ == 0)
{
uint8_t v___x_4603_; 
lean_inc(v_declName_4588_);
v___x_4603_ = l_Lean_Name_isInternalDetail(v_declName_4588_);
if (v___x_4603_ == 0)
{
lean_dec_ref(v_env_4587_);
v___y_4602_ = v___x_4603_;
goto v___jp_4601_;
}
else
{
uint8_t v___x_4604_; 
v___x_4604_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName(v_env_4587_, v_declName_4588_);
lean_dec_ref(v_env_4587_);
if (v___x_4604_ == 0)
{
v___y_4602_ = v___x_4603_;
goto v___jp_4601_;
}
else
{
goto v___jp_4597_;
}
}
}
else
{
lean_dec(v_declName_4588_);
lean_dec_ref(v_env_4587_);
return v___x_4592_;
}
v___jp_4593_:
{
if (lean_obj_tag(v_declName_4588_) == 1)
{
lean_object* v_str_4594_; lean_object* v___x_4595_; uint8_t v___x_4596_; 
v_str_4594_ = lean_ctor_get(v_declName_4588_, 1);
lean_inc_ref(v_str_4594_);
lean_dec_ref_known(v_declName_4588_, 2);
v___x_4595_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__2));
v___x_4596_ = lean_string_dec_eq(v_str_4594_, v___x_4595_);
lean_dec_ref(v_str_4594_);
return v___x_4596_;
}
else
{
lean_dec(v_declName_4588_);
return v___x_4592_;
}
}
v___jp_4597_:
{
if (lean_obj_tag(v_declName_4588_) == 1)
{
lean_object* v_str_4598_; lean_object* v___x_4599_; uint8_t v___x_4600_; 
v_str_4598_ = lean_ctor_get(v_declName_4588_, 1);
v___x_4599_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__3));
v___x_4600_ = lean_string_dec_eq(v_str_4598_, v___x_4599_);
if (v___x_4600_ == 0)
{
goto v___jp_4593_;
}
else
{
lean_dec_ref_known(v_declName_4588_, 2);
return v___x_4600_;
}
}
else
{
goto v___jp_4593_;
}
}
v___jp_4601_:
{
if (v___y_4602_ == 0)
{
goto v___jp_4597_;
}
else
{
lean_dec(v_declName_4588_);
return v___y_4602_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_blacklistInsertion___boxed(lean_object* v_env_4605_, lean_object* v_declName_4606_){
_start:
{
uint8_t v_res_4607_; lean_object* v_r_4608_; 
v_res_4607_ = l_Lean_Meta_LazyDiscrTree_blacklistInsertion(v_env_4605_, v_declName_4606_);
v_r_4608_ = lean_box(v_res_4607_);
return v_r_4608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(lean_object* v_opts_4609_, lean_object* v_opt_4610_){
_start:
{
lean_object* v_name_4611_; lean_object* v_defValue_4612_; lean_object* v_map_4613_; lean_object* v___x_4614_; 
v_name_4611_ = lean_ctor_get(v_opt_4610_, 0);
v_defValue_4612_ = lean_ctor_get(v_opt_4610_, 1);
v_map_4613_ = lean_ctor_get(v_opts_4609_, 0);
v___x_4614_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4613_, v_name_4611_);
if (lean_obj_tag(v___x_4614_) == 0)
{
lean_inc(v_defValue_4612_);
return v_defValue_4612_;
}
else
{
lean_object* v_val_4615_; 
v_val_4615_ = lean_ctor_get(v___x_4614_, 0);
lean_inc(v_val_4615_);
lean_dec_ref_known(v___x_4614_, 1);
if (lean_obj_tag(v_val_4615_) == 3)
{
lean_object* v_v_4616_; 
v_v_4616_ = lean_ctor_get(v_val_4615_, 0);
lean_inc(v_v_4616_);
lean_dec_ref_known(v_val_4615_, 1);
return v_v_4616_;
}
else
{
lean_dec(v_val_4615_);
lean_inc(v_defValue_4612_);
return v_defValue_4612_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0___boxed(lean_object* v_opts_4617_, lean_object* v_opt_4618_){
_start:
{
lean_object* v_res_4619_; 
v_res_4619_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(v_opts_4617_, v_opt_4618_);
lean_dec_ref(v_opt_4618_);
lean_dec_ref(v_opts_4617_);
return v_res_4619_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1___redArg(lean_object* v_as_4620_, size_t v_i_4621_, size_t v_stop_4622_, lean_object* v_b_4623_){
_start:
{
uint8_t v___x_4624_; 
v___x_4624_ = lean_usize_dec_eq(v_i_4621_, v_stop_4622_);
if (v___x_4624_ == 0)
{
lean_object* v___x_4625_; lean_object* v_key_4626_; lean_object* v_entry_4627_; lean_object* v___x_4628_; size_t v___x_4629_; size_t v___x_4630_; 
v___x_4625_ = lean_array_uget_borrowed(v_as_4620_, v_i_4621_);
v_key_4626_ = lean_ctor_get(v___x_4625_, 0);
v_entry_4627_ = lean_ctor_get(v___x_4625_, 1);
lean_inc_ref(v_entry_4627_);
lean_inc(v_key_4626_);
v___x_4628_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg(v_b_4623_, v_key_4626_, v_entry_4627_);
v___x_4629_ = ((size_t)1ULL);
v___x_4630_ = lean_usize_add(v_i_4621_, v___x_4629_);
v_i_4621_ = v___x_4630_;
v_b_4623_ = v___x_4628_;
goto _start;
}
else
{
return v_b_4623_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1___redArg___boxed(lean_object* v_as_4632_, lean_object* v_i_4633_, lean_object* v_stop_4634_, lean_object* v_b_4635_){
_start:
{
size_t v_i_boxed_4636_; size_t v_stop_boxed_4637_; lean_object* v_res_4638_; 
v_i_boxed_4636_ = lean_unbox_usize(v_i_4633_);
lean_dec(v_i_4633_);
v_stop_boxed_4637_ = lean_unbox_usize(v_stop_4634_);
lean_dec(v_stop_4634_);
v_res_4638_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1___redArg(v_as_4632_, v_i_boxed_4636_, v_stop_boxed_4637_, v_b_4635_);
lean_dec_ref(v_as_4632_);
return v_res_4638_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0(void){
_start:
{
lean_object* v___x_4639_; lean_object* v___x_4640_; 
v___x_4639_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0);
v___x_4640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4640_, 0, v___x_4639_);
return v___x_4640_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1(void){
_start:
{
lean_object* v___x_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; 
v___x_4641_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_4642_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0);
v___x_4643_ = lean_unsigned_to_nat(0u);
v___x_4644_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_4644_, 0, v___x_4643_);
lean_ctor_set(v___x_4644_, 1, v___x_4643_);
lean_ctor_set(v___x_4644_, 2, v___x_4643_);
lean_ctor_set(v___x_4644_, 3, v___x_4643_);
lean_ctor_set(v___x_4644_, 4, v___x_4642_);
lean_ctor_set(v___x_4644_, 5, v___x_4642_);
lean_ctor_set(v___x_4644_, 6, v___x_4642_);
lean_ctor_set(v___x_4644_, 7, v___x_4642_);
lean_ctor_set(v___x_4644_, 8, v___x_4642_);
lean_ctor_set(v___x_4644_, 9, v___x_4642_);
lean_ctor_set(v___x_4644_, 10, v___x_4642_);
lean_ctor_set(v___x_4644_, 11, v___x_4641_);
return v___x_4644_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2(void){
_start:
{
lean_object* v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; 
v___x_4645_ = lean_unsigned_to_nat(32u);
v___x_4646_ = lean_mk_empty_array_with_capacity(v___x_4645_);
v___x_4647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4647_, 0, v___x_4646_);
return v___x_4647_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3(void){
_start:
{
size_t v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; 
v___x_4648_ = ((size_t)5ULL);
v___x_4649_ = lean_unsigned_to_nat(0u);
v___x_4650_ = lean_unsigned_to_nat(32u);
v___x_4651_ = lean_mk_empty_array_with_capacity(v___x_4650_);
v___x_4652_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2);
v___x_4653_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4653_, 0, v___x_4652_);
lean_ctor_set(v___x_4653_, 1, v___x_4651_);
lean_ctor_set(v___x_4653_, 2, v___x_4649_);
lean_ctor_set(v___x_4653_, 3, v___x_4649_);
lean_ctor_set_usize(v___x_4653_, 4, v___x_4648_);
return v___x_4653_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4(void){
_start:
{
lean_object* v___x_4654_; lean_object* v___x_4655_; 
v___x_4654_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0);
v___x_4655_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4655_, 0, v___x_4654_);
lean_ctor_set(v___x_4655_, 1, v___x_4654_);
lean_ctor_set(v___x_4655_, 2, v___x_4654_);
lean_ctor_set(v___x_4655_, 3, v___x_4654_);
lean_ctor_set(v___x_4655_, 4, v___x_4654_);
return v___x_4655_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5(void){
_start:
{
lean_object* v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; 
v___x_4656_ = lean_box(1);
v___x_4657_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3);
v___x_4658_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0);
v___x_4659_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4659_, 0, v___x_4658_);
lean_ctor_set(v___x_4659_, 1, v___x_4657_);
lean_ctor_set(v___x_4659_, 2, v___x_4656_);
return v___x_4659_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__7(void){
_start:
{
lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4664_; 
v___x_4662_ = lean_unsigned_to_nat(1u);
v___x_4663_ = l_Lean_firstFrontendMacroScope;
v___x_4664_ = lean_nat_add(v___x_4663_, v___x_4662_);
return v___x_4664_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__9(void){
_start:
{
lean_object* v___x_4669_; uint64_t v___x_4670_; lean_object* v___x_4671_; 
v___x_4669_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3);
v___x_4670_ = 0ULL;
v___x_4671_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4671_, 0, v___x_4669_);
lean_ctor_set_uint64(v___x_4671_, sizeof(void*)*1, v___x_4670_);
return v___x_4671_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10(void){
_start:
{
lean_object* v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; lean_object* v___x_4675_; 
v___x_4672_ = lean_unsigned_to_nat(0u);
v___x_4673_ = l_Lean_Options_empty;
v___x_4674_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6));
v___x_4675_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4675_, 0, v___x_4674_);
lean_ctor_set(v___x_4675_, 1, v___x_4673_);
lean_ctor_set(v___x_4675_, 2, v___x_4674_);
lean_ctor_set(v___x_4675_, 3, v___x_4672_);
lean_ctor_set(v___x_4675_, 4, v___x_4672_);
lean_ctor_set(v___x_4675_, 5, v___x_4672_);
return v___x_4675_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11(void){
_start:
{
lean_object* v___x_4676_; lean_object* v___x_4677_; lean_object* v___x_4678_; 
v___x_4676_ = l_Lean_NameSet_empty;
v___x_4677_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3);
v___x_4678_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4678_, 0, v___x_4677_);
lean_ctor_set(v___x_4678_, 1, v___x_4677_);
lean_ctor_set(v___x_4678_, 2, v___x_4676_);
return v___x_4678_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12(void){
_start:
{
lean_object* v___x_4679_; lean_object* v___x_4680_; uint8_t v___x_4681_; lean_object* v___x_4682_; 
v___x_4679_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3);
v___x_4680_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0);
v___x_4681_ = 1;
v___x_4682_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4682_, 0, v___x_4680_);
lean_ctor_set(v___x_4682_, 1, v___x_4680_);
lean_ctor_set(v___x_4682_, 2, v___x_4679_);
lean_ctor_set_uint8(v___x_4682_, sizeof(void*)*3, v___x_4681_);
return v___x_4682_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13(void){
_start:
{
lean_object* v___x_4683_; lean_object* v___x_4684_; 
v___x_4683_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0);
v___x_4684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4684_, 0, v___x_4683_);
lean_ctor_set(v___x_4684_, 1, v___x_4683_);
return v___x_4684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(lean_object* v_cctx_4685_, lean_object* v_env_4686_, lean_object* v_modName_4687_, lean_object* v_d_4688_, lean_object* v_cacheRef_4689_, lean_object* v_tree_4690_, lean_object* v_act_4691_, lean_object* v_c_4692_){
_start:
{
uint8_t v___x_4694_; 
lean_inc_ref(v_c_4692_);
v___x_4694_ = l_Lean_AsyncConstantInfo_isUnsafe(v_c_4692_);
if (v___x_4694_ == 0)
{
lean_object* v_name_4695_; uint8_t v___x_4696_; 
v_name_4695_ = lean_ctor_get(v_c_4692_, 0);
lean_inc_n(v_name_4695_, 2);
lean_inc_ref(v_env_4686_);
v___x_4696_ = l_Lean_Meta_LazyDiscrTree_blacklistInsertion(v_env_4686_, v_name_4695_);
if (v___x_4696_ == 0)
{
lean_object* v___x_4697_; uint8_t v___x_4698_; lean_object* v___x_4699_; lean_object* v_ngen_4700_; lean_object* v_core_4701_; lean_object* v_meta_4702_; lean_object* v___x_4704_; uint8_t v_isShared_4705_; uint8_t v_isSharedCheck_4835_; 
v___x_4697_ = lean_box(1);
v___x_4698_ = 1;
v___x_4699_ = lean_st_ref_get(v_cacheRef_4689_);
v_ngen_4700_ = lean_ctor_get(v___x_4699_, 0);
v_core_4701_ = lean_ctor_get(v___x_4699_, 1);
v_meta_4702_ = lean_ctor_get(v___x_4699_, 2);
v_isSharedCheck_4835_ = !lean_is_exclusive(v___x_4699_);
if (v_isSharedCheck_4835_ == 0)
{
v___x_4704_ = v___x_4699_;
v_isShared_4705_ = v_isSharedCheck_4835_;
goto v_resetjp_4703_;
}
else
{
lean_inc(v_meta_4702_);
lean_inc(v_core_4701_);
lean_inc(v_ngen_4700_);
lean_dec(v___x_4699_);
v___x_4704_ = lean_box(0);
v_isShared_4705_ = v_isSharedCheck_4835_;
goto v_resetjp_4703_;
}
v_resetjp_4703_:
{
lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; uint8_t v___x_4713_; uint8_t v___x_4714_; uint8_t v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; lean_object* v___x_4729_; uint16_t v___y_4731_; lean_object* v___y_4732_; lean_object* v_fileName_4733_; lean_object* v_fileMap_4734_; lean_object* v_currNamespace_4735_; lean_object* v_openDecls_4736_; lean_object* v_initHeartbeats_4737_; lean_object* v_maxHeartbeats_4738_; lean_object* v_quotContext_4739_; lean_object* v_currMacroScope_4740_; lean_object* v_cancelTk_x3f_4741_; lean_object* v_inheritedTraceOptions_4742_; lean_object* v_currRecDepth_4743_; lean_object* v_ref_4744_; uint8_t v_suppressElabErrors_4745_; uint8_t v_isRecordingDeps_4746_; lean_object* v___x_4777_; lean_object* v___x_4778_; lean_object* v_toCold_4779_; lean_object* v_currRecDepth_4780_; lean_object* v_ref_4781_; uint8_t v_suppressElabErrors_4782_; uint8_t v_isRecordingDeps_4783_; lean_object* v_fileName_4784_; lean_object* v_fileMap_4785_; lean_object* v_options_4786_; lean_object* v_currNamespace_4787_; lean_object* v_openDecls_4788_; lean_object* v_initHeartbeats_4789_; lean_object* v_maxHeartbeats_4790_; lean_object* v_quotContext_4791_; lean_object* v_currMacroScope_4792_; lean_object* v_cancelTk_x3f_4793_; uint8_t v___y_4795_; uint16_t v___y_4796_; lean_object* v___y_4797_; uint8_t v___y_4820_; uint16_t v___y_4821_; lean_object* v___y_4822_; uint8_t v___y_4823_; lean_object* v___y_4825_; 
v___x_4706_ = lean_unsigned_to_nat(0u);
v___x_4707_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4708_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3);
v___x_4709_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4710_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4710_, 0, v___x_4707_);
lean_ctor_set(v___x_4710_, 1, v_meta_4702_);
lean_ctor_set(v___x_4710_, 2, v___x_4697_);
lean_ctor_set(v___x_4710_, 3, v___x_4708_);
lean_ctor_set(v___x_4710_, 4, v___x_4709_);
lean_inc_ref(v_ngen_4700_);
v___x_4711_ = l_Lean_Meta_LazyDiscrTree_Cache_empty(v_ngen_4700_);
v___x_4712_ = lean_st_ref_swap(v_cacheRef_4689_, v___x_4711_);
lean_dec(v___x_4712_);
v___x_4713_ = 2;
v___x_4714_ = 0;
v___x_4715_ = 2;
v___x_4716_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_4716_, 0, v___x_4696_);
lean_ctor_set_uint8(v___x_4716_, 1, v___x_4696_);
lean_ctor_set_uint8(v___x_4716_, 2, v___x_4696_);
lean_ctor_set_uint8(v___x_4716_, 3, v___x_4696_);
lean_ctor_set_uint8(v___x_4716_, 4, v___x_4696_);
lean_ctor_set_uint8(v___x_4716_, 5, v___x_4698_);
lean_ctor_set_uint8(v___x_4716_, 6, v___x_4698_);
lean_ctor_set_uint8(v___x_4716_, 7, v___x_4696_);
lean_ctor_set_uint8(v___x_4716_, 8, v___x_4698_);
lean_ctor_set_uint8(v___x_4716_, 9, v___x_4713_);
lean_ctor_set_uint8(v___x_4716_, 10, v___x_4714_);
lean_ctor_set_uint8(v___x_4716_, 11, v___x_4698_);
lean_ctor_set_uint8(v___x_4716_, 12, v___x_4698_);
lean_ctor_set_uint8(v___x_4716_, 13, v___x_4698_);
lean_ctor_set_uint8(v___x_4716_, 14, v___x_4715_);
lean_ctor_set_uint8(v___x_4716_, 15, v___x_4698_);
lean_ctor_set_uint8(v___x_4716_, 16, v___x_4698_);
lean_ctor_set_uint8(v___x_4716_, 17, v___x_4698_);
lean_ctor_set_uint8(v___x_4716_, 18, v___x_4698_);
lean_ctor_set_uint8(v___x_4716_, 19, v___x_4696_);
v___x_4717_ = l_Lean_Meta_Config_toConfigWithKey(v___x_4716_);
v___x_4718_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5);
v___x_4719_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6));
v___x_4720_ = lean_box(0);
v___x_4721_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4721_, 0, v___x_4717_);
lean_ctor_set(v___x_4721_, 1, v___x_4697_);
lean_ctor_set(v___x_4721_, 2, v___x_4718_);
lean_ctor_set(v___x_4721_, 3, v___x_4719_);
lean_ctor_set(v___x_4721_, 4, v___x_4720_);
lean_ctor_set(v___x_4721_, 5, v___x_4706_);
lean_ctor_set(v___x_4721_, 6, v___x_4720_);
lean_ctor_set_uint8(v___x_4721_, sizeof(void*)*7, v___x_4696_);
lean_ctor_set_uint8(v___x_4721_, sizeof(void*)*7 + 1, v___x_4696_);
lean_ctor_set_uint8(v___x_4721_, sizeof(void*)*7 + 2, v___x_4696_);
lean_ctor_set_uint8(v___x_4721_, sizeof(void*)*7 + 3, v___x_4698_);
v___x_4722_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__7, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__7_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__7);
v___x_4723_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__8));
v___x_4724_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__9, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__9_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__9);
v___x_4725_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10);
v___x_4726_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11);
v___x_4727_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12);
v___x_4728_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4728_, 0, v_env_4686_);
lean_ctor_set(v___x_4728_, 1, v___x_4722_);
lean_ctor_set(v___x_4728_, 2, v_ngen_4700_);
lean_ctor_set(v___x_4728_, 3, v___x_4723_);
lean_ctor_set(v___x_4728_, 4, v___x_4724_);
lean_ctor_set(v___x_4728_, 5, v_core_4701_);
lean_ctor_set(v___x_4728_, 6, v___x_4725_);
lean_ctor_set(v___x_4728_, 7, v___x_4726_);
lean_ctor_set(v___x_4728_, 8, v___x_4727_);
lean_ctor_set(v___x_4728_, 9, v___x_4719_);
v___x_4729_ = lean_st_mk_ref(v___x_4728_);
v___x_4777_ = l_Lean_inheritedTraceOptions;
v___x_4778_ = lean_st_ref_get(v___x_4777_);
v_toCold_4779_ = lean_ctor_get(v_cctx_4685_, 0);
lean_inc_ref(v_toCold_4779_);
v_currRecDepth_4780_ = lean_ctor_get(v_cctx_4685_, 1);
lean_inc(v_currRecDepth_4780_);
v_ref_4781_ = lean_ctor_get(v_cctx_4685_, 2);
lean_inc(v_ref_4781_);
v_suppressElabErrors_4782_ = lean_ctor_get_uint8(v_cctx_4685_, sizeof(void*)*3 + 2);
v_isRecordingDeps_4783_ = lean_ctor_get_uint8(v_cctx_4685_, sizeof(void*)*3 + 3);
lean_dec_ref(v_cctx_4685_);
v_fileName_4784_ = lean_ctor_get(v_toCold_4779_, 0);
lean_inc_ref(v_fileName_4784_);
v_fileMap_4785_ = lean_ctor_get(v_toCold_4779_, 1);
lean_inc_ref(v_fileMap_4785_);
v_options_4786_ = lean_ctor_get(v_toCold_4779_, 2);
lean_inc_ref(v_options_4786_);
v_currNamespace_4787_ = lean_ctor_get(v_toCold_4779_, 4);
lean_inc(v_currNamespace_4787_);
v_openDecls_4788_ = lean_ctor_get(v_toCold_4779_, 5);
lean_inc(v_openDecls_4788_);
v_initHeartbeats_4789_ = lean_ctor_get(v_toCold_4779_, 6);
lean_inc(v_initHeartbeats_4789_);
v_maxHeartbeats_4790_ = lean_ctor_get(v_toCold_4779_, 7);
lean_inc(v_maxHeartbeats_4790_);
v_quotContext_4791_ = lean_ctor_get(v_toCold_4779_, 8);
lean_inc(v_quotContext_4791_);
v_currMacroScope_4792_ = lean_ctor_get(v_toCold_4779_, 9);
lean_inc(v_currMacroScope_4792_);
v_cancelTk_x3f_4793_ = lean_ctor_get(v_toCold_4779_, 10);
lean_inc(v_cancelTk_x3f_4793_);
lean_dec_ref(v_toCold_4779_);
if (v_isRecordingDeps_4783_ == 0)
{
v___y_4825_ = v_options_4786_;
goto v___jp_4824_;
}
else
{
lean_object* v___x_4834_; 
v___x_4834_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_4786_);
v___y_4825_ = v___x_4834_;
goto v___jp_4824_;
}
v___jp_4730_:
{
lean_object* v___x_4747_; lean_object* v___x_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; 
v___x_4747_ = l_Lean_maxRecDepth;
v___x_4748_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(v___y_4732_, v___x_4747_);
v___x_4749_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_4749_, 0, v_fileName_4733_);
lean_ctor_set(v___x_4749_, 1, v_fileMap_4734_);
lean_ctor_set(v___x_4749_, 2, v___y_4732_);
lean_ctor_set(v___x_4749_, 3, v___x_4748_);
lean_ctor_set(v___x_4749_, 4, v_currNamespace_4735_);
lean_ctor_set(v___x_4749_, 5, v_openDecls_4736_);
lean_ctor_set(v___x_4749_, 6, v_initHeartbeats_4737_);
lean_ctor_set(v___x_4749_, 7, v_maxHeartbeats_4738_);
lean_ctor_set(v___x_4749_, 8, v_quotContext_4739_);
lean_ctor_set(v___x_4749_, 9, v_currMacroScope_4740_);
lean_ctor_set(v___x_4749_, 10, v_cancelTk_x3f_4741_);
lean_ctor_set(v___x_4749_, 11, v_inheritedTraceOptions_4742_);
v___x_4750_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_4750_, 0, v___x_4749_);
lean_ctor_set(v___x_4750_, 1, v_currRecDepth_4743_);
lean_ctor_set(v___x_4750_, 2, v_ref_4744_);
lean_ctor_set_uint16(v___x_4750_, sizeof(void*)*3, v___y_4731_);
lean_ctor_set_uint8(v___x_4750_, sizeof(void*)*3 + 2, v_suppressElabErrors_4745_);
lean_ctor_set_uint8(v___x_4750_, sizeof(void*)*3 + 3, v_isRecordingDeps_4746_);
v___x_4751_ = lean_st_mk_ref(v___x_4710_);
lean_inc(v___x_4729_);
lean_inc(v___x_4751_);
lean_inc(v_name_4695_);
v___x_4752_ = lean_apply_7(v_act_4691_, v_name_4695_, v_c_4692_, v___x_4721_, v___x_4751_, v___x_4750_, v___x_4729_, lean_box(0));
if (lean_obj_tag(v___x_4752_) == 0)
{
lean_object* v_a_4753_; lean_object* v___x_4754_; lean_object* v___x_4755_; lean_object* v_ngen_4756_; lean_object* v_cache_4757_; lean_object* v_cache_4758_; lean_object* v___x_4760_; 
lean_dec(v_name_4695_);
lean_dec(v_modName_4687_);
v_a_4753_ = lean_ctor_get(v___x_4752_, 0);
lean_inc(v_a_4753_);
lean_dec_ref_known(v___x_4752_, 1);
v___x_4754_ = lean_st_ref_get(v___x_4751_);
lean_dec(v___x_4751_);
v___x_4755_ = lean_st_ref_get(v___x_4729_);
lean_dec(v___x_4729_);
v_ngen_4756_ = lean_ctor_get(v___x_4755_, 2);
lean_inc_ref(v_ngen_4756_);
v_cache_4757_ = lean_ctor_get(v___x_4755_, 5);
lean_inc_ref(v_cache_4757_);
lean_dec(v___x_4755_);
v_cache_4758_ = lean_ctor_get(v___x_4754_, 1);
lean_inc_ref(v_cache_4758_);
lean_dec(v___x_4754_);
if (v_isShared_4705_ == 0)
{
lean_ctor_set(v___x_4704_, 2, v_cache_4758_);
lean_ctor_set(v___x_4704_, 1, v_cache_4757_);
lean_ctor_set(v___x_4704_, 0, v_ngen_4756_);
v___x_4760_ = v___x_4704_;
goto v_reusejp_4759_;
}
else
{
lean_object* v_reuseFailAlloc_4771_; 
v_reuseFailAlloc_4771_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4771_, 0, v_ngen_4756_);
lean_ctor_set(v_reuseFailAlloc_4771_, 1, v_cache_4757_);
lean_ctor_set(v_reuseFailAlloc_4771_, 2, v_cache_4758_);
v___x_4760_ = v_reuseFailAlloc_4771_;
goto v_reusejp_4759_;
}
v_reusejp_4759_:
{
lean_object* v___x_4761_; lean_object* v___x_4762_; uint8_t v___x_4763_; 
v___x_4761_ = lean_st_ref_swap(v_cacheRef_4689_, v___x_4760_);
lean_dec(v___x_4761_);
v___x_4762_ = lean_array_get_size(v_a_4753_);
v___x_4763_ = lean_nat_dec_lt(v___x_4706_, v___x_4762_);
if (v___x_4763_ == 0)
{
lean_dec(v_a_4753_);
return v_tree_4690_;
}
else
{
uint8_t v___x_4764_; 
v___x_4764_ = lean_nat_dec_le(v___x_4762_, v___x_4762_);
if (v___x_4764_ == 0)
{
if (v___x_4763_ == 0)
{
lean_dec(v_a_4753_);
return v_tree_4690_;
}
else
{
size_t v___x_4765_; size_t v___x_4766_; lean_object* v___x_4767_; 
v___x_4765_ = ((size_t)0ULL);
v___x_4766_ = lean_usize_of_nat(v___x_4762_);
v___x_4767_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1___redArg(v_a_4753_, v___x_4765_, v___x_4766_, v_tree_4690_);
lean_dec(v_a_4753_);
return v___x_4767_;
}
}
else
{
size_t v___x_4768_; size_t v___x_4769_; lean_object* v___x_4770_; 
v___x_4768_ = ((size_t)0ULL);
v___x_4769_ = lean_usize_of_nat(v___x_4762_);
v___x_4770_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1___redArg(v_a_4753_, v___x_4768_, v___x_4769_, v_tree_4690_);
lean_dec(v_a_4753_);
return v___x_4770_;
}
}
}
}
else
{
lean_object* v_a_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; 
lean_dec(v___x_4751_);
lean_dec(v___x_4729_);
lean_del_object(v___x_4704_);
v_a_4772_ = lean_ctor_get(v___x_4752_, 0);
lean_inc(v_a_4772_);
lean_dec_ref_known(v___x_4752_, 1);
v___x_4773_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4773_, 0, v_modName_4687_);
lean_ctor_set(v___x_4773_, 1, v_name_4695_);
lean_ctor_set(v___x_4773_, 2, v_a_4772_);
v___x_4774_ = lean_st_ref_take(v_d_4688_);
v___x_4775_ = lean_array_push(v___x_4774_, v___x_4773_);
v___x_4776_ = lean_st_ref_put(v_d_4688_, v___x_4775_);
return v_tree_4690_;
}
}
v___jp_4794_:
{
lean_object* v___x_4798_; lean_object* v_env_4799_; lean_object* v_nextMacroScope_4800_; lean_object* v_ngen_4801_; lean_object* v_auxDeclNGen_4802_; lean_object* v_traceState_4803_; lean_object* v_recordedDeps_4804_; lean_object* v_messages_4805_; lean_object* v_infoState_4806_; lean_object* v_snapshotTasks_4807_; lean_object* v___x_4809_; uint8_t v_isShared_4810_; uint8_t v_isSharedCheck_4817_; 
v___x_4798_ = lean_st_ref_take(v___x_4729_);
v_env_4799_ = lean_ctor_get(v___x_4798_, 0);
v_nextMacroScope_4800_ = lean_ctor_get(v___x_4798_, 1);
v_ngen_4801_ = lean_ctor_get(v___x_4798_, 2);
v_auxDeclNGen_4802_ = lean_ctor_get(v___x_4798_, 3);
v_traceState_4803_ = lean_ctor_get(v___x_4798_, 4);
v_recordedDeps_4804_ = lean_ctor_get(v___x_4798_, 6);
v_messages_4805_ = lean_ctor_get(v___x_4798_, 7);
v_infoState_4806_ = lean_ctor_get(v___x_4798_, 8);
v_snapshotTasks_4807_ = lean_ctor_get(v___x_4798_, 9);
v_isSharedCheck_4817_ = !lean_is_exclusive(v___x_4798_);
if (v_isSharedCheck_4817_ == 0)
{
lean_object* v_unused_4818_; 
v_unused_4818_ = lean_ctor_get(v___x_4798_, 5);
lean_dec(v_unused_4818_);
v___x_4809_ = v___x_4798_;
v_isShared_4810_ = v_isSharedCheck_4817_;
goto v_resetjp_4808_;
}
else
{
lean_inc(v_snapshotTasks_4807_);
lean_inc(v_infoState_4806_);
lean_inc(v_messages_4805_);
lean_inc(v_recordedDeps_4804_);
lean_inc(v_traceState_4803_);
lean_inc(v_auxDeclNGen_4802_);
lean_inc(v_ngen_4801_);
lean_inc(v_nextMacroScope_4800_);
lean_inc(v_env_4799_);
lean_dec(v___x_4798_);
v___x_4809_ = lean_box(0);
v_isShared_4810_ = v_isSharedCheck_4817_;
goto v_resetjp_4808_;
}
v_resetjp_4808_:
{
lean_object* v___x_4811_; lean_object* v___x_4812_; lean_object* v___x_4814_; 
v___x_4811_ = l_Lean_Kernel_enableDiag(v_env_4799_, v___y_4795_);
v___x_4812_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13);
if (v_isShared_4810_ == 0)
{
lean_ctor_set(v___x_4809_, 5, v___x_4812_);
lean_ctor_set(v___x_4809_, 0, v___x_4811_);
v___x_4814_ = v___x_4809_;
goto v_reusejp_4813_;
}
else
{
lean_object* v_reuseFailAlloc_4816_; 
v_reuseFailAlloc_4816_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4816_, 0, v___x_4811_);
lean_ctor_set(v_reuseFailAlloc_4816_, 1, v_nextMacroScope_4800_);
lean_ctor_set(v_reuseFailAlloc_4816_, 2, v_ngen_4801_);
lean_ctor_set(v_reuseFailAlloc_4816_, 3, v_auxDeclNGen_4802_);
lean_ctor_set(v_reuseFailAlloc_4816_, 4, v_traceState_4803_);
lean_ctor_set(v_reuseFailAlloc_4816_, 5, v___x_4812_);
lean_ctor_set(v_reuseFailAlloc_4816_, 6, v_recordedDeps_4804_);
lean_ctor_set(v_reuseFailAlloc_4816_, 7, v_messages_4805_);
lean_ctor_set(v_reuseFailAlloc_4816_, 8, v_infoState_4806_);
lean_ctor_set(v_reuseFailAlloc_4816_, 9, v_snapshotTasks_4807_);
v___x_4814_ = v_reuseFailAlloc_4816_;
goto v_reusejp_4813_;
}
v_reusejp_4813_:
{
lean_object* v___x_4815_; 
v___x_4815_ = lean_st_ref_put(v___x_4729_, v___x_4814_);
v___y_4731_ = v___y_4796_;
v___y_4732_ = v___y_4797_;
v_fileName_4733_ = v_fileName_4784_;
v_fileMap_4734_ = v_fileMap_4785_;
v_currNamespace_4735_ = v_currNamespace_4787_;
v_openDecls_4736_ = v_openDecls_4788_;
v_initHeartbeats_4737_ = v_initHeartbeats_4789_;
v_maxHeartbeats_4738_ = v_maxHeartbeats_4790_;
v_quotContext_4739_ = v_quotContext_4791_;
v_currMacroScope_4740_ = v_currMacroScope_4792_;
v_cancelTk_x3f_4741_ = v_cancelTk_x3f_4793_;
v_inheritedTraceOptions_4742_ = v___x_4778_;
v_currRecDepth_4743_ = v_currRecDepth_4780_;
v_ref_4744_ = v_ref_4781_;
v_suppressElabErrors_4745_ = v_suppressElabErrors_4782_;
v_isRecordingDeps_4746_ = v_isRecordingDeps_4783_;
goto v___jp_4730_;
}
}
}
v___jp_4819_:
{
if (v___y_4820_ == 0)
{
v___y_4795_ = v___y_4823_;
v___y_4796_ = v___y_4821_;
v___y_4797_ = v___y_4822_;
goto v___jp_4794_;
}
else
{
v___y_4731_ = v___y_4821_;
v___y_4732_ = v___y_4822_;
v_fileName_4733_ = v_fileName_4784_;
v_fileMap_4734_ = v_fileMap_4785_;
v_currNamespace_4735_ = v_currNamespace_4787_;
v_openDecls_4736_ = v_openDecls_4788_;
v_initHeartbeats_4737_ = v_initHeartbeats_4789_;
v_maxHeartbeats_4738_ = v_maxHeartbeats_4790_;
v_quotContext_4739_ = v_quotContext_4791_;
v_currMacroScope_4740_ = v_currMacroScope_4792_;
v_cancelTk_x3f_4741_ = v_cancelTk_x3f_4793_;
v_inheritedTraceOptions_4742_ = v___x_4778_;
v_currRecDepth_4743_ = v_currRecDepth_4780_;
v_ref_4744_ = v_ref_4781_;
v_suppressElabErrors_4745_ = v_suppressElabErrors_4782_;
v_isRecordingDeps_4746_ = v_isRecordingDeps_4783_;
goto v___jp_4730_;
}
}
v___jp_4824_:
{
uint16_t v___x_4826_; lean_object* v___x_4827_; lean_object* v_env_4828_; uint8_t v___x_4829_; uint16_t v___x_4830_; uint16_t v___x_4831_; uint16_t v___x_4832_; uint8_t v___x_4833_; 
v___x_4826_ = l_Lean_OptionFlags_ofOptions(v___y_4825_);
v___x_4827_ = lean_st_ref_get(v___x_4729_);
v_env_4828_ = lean_ctor_get(v___x_4827_, 0);
lean_inc_ref(v_env_4828_);
lean_dec(v___x_4827_);
v___x_4829_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4828_);
lean_dec_ref(v_env_4828_);
v___x_4830_ = 512;
v___x_4831_ = lean_uint16_land(v___x_4826_, v___x_4830_);
v___x_4832_ = 0;
v___x_4833_ = lean_uint16_dec_eq(v___x_4831_, v___x_4832_);
if (v___x_4833_ == 0)
{
v___y_4820_ = v___x_4829_;
v___y_4821_ = v___x_4826_;
v___y_4822_ = v___y_4825_;
v___y_4823_ = v___x_4698_;
goto v___jp_4819_;
}
else
{
if (v___x_4696_ == 0)
{
if (v___x_4829_ == 0)
{
v___y_4731_ = v___x_4826_;
v___y_4732_ = v___y_4825_;
v_fileName_4733_ = v_fileName_4784_;
v_fileMap_4734_ = v_fileMap_4785_;
v_currNamespace_4735_ = v_currNamespace_4787_;
v_openDecls_4736_ = v_openDecls_4788_;
v_initHeartbeats_4737_ = v_initHeartbeats_4789_;
v_maxHeartbeats_4738_ = v_maxHeartbeats_4790_;
v_quotContext_4739_ = v_quotContext_4791_;
v_currMacroScope_4740_ = v_currMacroScope_4792_;
v_cancelTk_x3f_4741_ = v_cancelTk_x3f_4793_;
v_inheritedTraceOptions_4742_ = v___x_4778_;
v_currRecDepth_4743_ = v_currRecDepth_4780_;
v_ref_4744_ = v_ref_4781_;
v_suppressElabErrors_4745_ = v_suppressElabErrors_4782_;
v_isRecordingDeps_4746_ = v_isRecordingDeps_4783_;
goto v___jp_4730_;
}
else
{
v___y_4795_ = v___x_4696_;
v___y_4796_ = v___x_4826_;
v___y_4797_ = v___y_4825_;
goto v___jp_4794_;
}
}
else
{
v___y_4820_ = v___x_4829_;
v___y_4821_ = v___x_4826_;
v___y_4822_ = v___y_4825_;
v___y_4823_ = v___x_4696_;
goto v___jp_4819_;
}
}
}
}
}
else
{
lean_dec(v_name_4695_);
lean_dec_ref(v_c_4692_);
lean_dec_ref(v_act_4691_);
lean_dec(v_modName_4687_);
lean_dec_ref(v_env_4686_);
lean_dec_ref(v_cctx_4685_);
return v_tree_4690_;
}
}
else
{
lean_dec_ref(v_c_4692_);
lean_dec_ref(v_act_4691_);
lean_dec(v_modName_4687_);
lean_dec_ref(v_env_4686_);
lean_dec_ref(v_cctx_4685_);
return v_tree_4690_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___boxed(lean_object* v_cctx_4836_, lean_object* v_env_4837_, lean_object* v_modName_4838_, lean_object* v_d_4839_, lean_object* v_cacheRef_4840_, lean_object* v_tree_4841_, lean_object* v_act_4842_, lean_object* v_c_4843_, lean_object* v_a_4844_){
_start:
{
lean_object* v_res_4845_; 
v_res_4845_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_4836_, v_env_4837_, v_modName_4838_, v_d_4839_, v_cacheRef_4840_, v_tree_4841_, v_act_4842_, v_c_4843_);
lean_dec(v_cacheRef_4840_);
lean_dec(v_d_4839_);
return v_res_4845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData(lean_object* v_00_u03b1_4846_, lean_object* v_cctx_4847_, lean_object* v_env_4848_, lean_object* v_modName_4849_, lean_object* v_d_4850_, lean_object* v_cacheRef_4851_, lean_object* v_tree_4852_, lean_object* v_act_4853_, lean_object* v_c_4854_){
_start:
{
lean_object* v___x_4856_; 
v___x_4856_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_4847_, v_env_4848_, v_modName_4849_, v_d_4850_, v_cacheRef_4851_, v_tree_4852_, v_act_4853_, v_c_4854_);
return v___x_4856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___boxed(lean_object* v_00_u03b1_4857_, lean_object* v_cctx_4858_, lean_object* v_env_4859_, lean_object* v_modName_4860_, lean_object* v_d_4861_, lean_object* v_cacheRef_4862_, lean_object* v_tree_4863_, lean_object* v_act_4864_, lean_object* v_c_4865_, lean_object* v_a_4866_){
_start:
{
lean_object* v_res_4867_; 
v_res_4867_ = l_Lean_Meta_LazyDiscrTree_addConstImportData(v_00_u03b1_4857_, v_cctx_4858_, v_env_4859_, v_modName_4860_, v_d_4861_, v_cacheRef_4862_, v_tree_4863_, v_act_4864_, v_c_4865_);
lean_dec(v_cacheRef_4862_);
lean_dec(v_d_4861_);
return v_res_4867_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1(lean_object* v_00_u03b1_4868_, lean_object* v_as_4869_, size_t v_i_4870_, size_t v_stop_4871_, lean_object* v_b_4872_){
_start:
{
lean_object* v___x_4873_; 
v___x_4873_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1___redArg(v_as_4869_, v_i_4870_, v_stop_4871_, v_b_4872_);
return v___x_4873_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1___boxed(lean_object* v_00_u03b1_4874_, lean_object* v_as_4875_, lean_object* v_i_4876_, lean_object* v_stop_4877_, lean_object* v_b_4878_){
_start:
{
size_t v_i_boxed_4879_; size_t v_stop_boxed_4880_; lean_object* v_res_4881_; 
v_i_boxed_4879_ = lean_unbox_usize(v_i_4876_);
lean_dec(v_i_4876_);
v_stop_boxed_4880_ = lean_unbox_usize(v_stop_4877_);
lean_dec(v_stop_4877_);
v_res_4881_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1(v_00_u03b1_4874_, v_as_4875_, v_i_boxed_4879_, v_stop_boxed_4880_, v_b_4878_);
lean_dec_ref(v_as_4875_);
return v_res_4881_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___redArg___closed__0(void){
_start:
{
lean_object* v___x_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; 
v___x_4882_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__0));
v___x_4883_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1);
v___x_4884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4884_, 0, v___x_4883_);
lean_ctor_set(v___x_4884_, 1, v___x_4882_);
return v___x_4884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___redArg(){
_start:
{
lean_object* v___x_4886_; 
v___x_4886_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___redArg___closed__0);
return v___x_4886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___redArg___boxed(lean_object* v___dummy_4887_){
_start:
{
lean_object* v_res_4888_; 
v_res_4888_ = l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___redArg();
return v_res_4888_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0(void){
_start:
{
lean_object* v___x_4889_; 
v___x_4889_ = l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___redArg();
return v___x_4889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults(lean_object* v_00_u03b1_4890_){
_start:
{
lean_object* v___x_4891_; 
v___x_4891_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0);
return v___x_4891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_append___redArg(lean_object* v_x_4892_, lean_object* v_y_4893_){
_start:
{
lean_object* v_tree_4894_; lean_object* v_errors_4895_; lean_object* v_tree_4896_; lean_object* v_errors_4897_; lean_object* v___x_4899_; uint8_t v_isShared_4900_; uint8_t v_isSharedCheck_4906_; 
v_tree_4894_ = lean_ctor_get(v_x_4892_, 0);
lean_inc_ref(v_tree_4894_);
v_errors_4895_ = lean_ctor_get(v_x_4892_, 1);
lean_inc_ref(v_errors_4895_);
lean_dec_ref(v_x_4892_);
v_tree_4896_ = lean_ctor_get(v_y_4893_, 0);
v_errors_4897_ = lean_ctor_get(v_y_4893_, 1);
v_isSharedCheck_4906_ = !lean_is_exclusive(v_y_4893_);
if (v_isSharedCheck_4906_ == 0)
{
v___x_4899_ = v_y_4893_;
v_isShared_4900_ = v_isSharedCheck_4906_;
goto v_resetjp_4898_;
}
else
{
lean_inc(v_errors_4897_);
lean_inc(v_tree_4896_);
lean_dec(v_y_4893_);
v___x_4899_ = lean_box(0);
v_isShared_4900_ = v_isSharedCheck_4906_;
goto v_resetjp_4898_;
}
v_resetjp_4898_:
{
lean_object* v___x_4901_; lean_object* v___x_4902_; lean_object* v___x_4904_; 
v___x_4901_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg(v_tree_4894_, v_tree_4896_);
v___x_4902_ = l_Array_append___redArg(v_errors_4895_, v_errors_4897_);
lean_dec_ref(v_errors_4897_);
if (v_isShared_4900_ == 0)
{
lean_ctor_set(v___x_4899_, 1, v___x_4902_);
lean_ctor_set(v___x_4899_, 0, v___x_4901_);
v___x_4904_ = v___x_4899_;
goto v_reusejp_4903_;
}
else
{
lean_object* v_reuseFailAlloc_4905_; 
v_reuseFailAlloc_4905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4905_, 0, v___x_4901_);
lean_ctor_set(v_reuseFailAlloc_4905_, 1, v___x_4902_);
v___x_4904_ = v_reuseFailAlloc_4905_;
goto v_reusejp_4903_;
}
v_reusejp_4903_:
{
return v___x_4904_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_append(lean_object* v_00_u03b1_4907_, lean_object* v_x_4908_, lean_object* v_y_4909_){
_start:
{
lean_object* v___x_4910_; 
v___x_4910_ = l_Lean_Meta_LazyDiscrTree_InitResults_append___redArg(v_x_4908_, v_y_4909_);
return v___x_4910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___redArg(){
_start:
{
lean_object* v___x_4913_; 
v___x_4913_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___redArg___closed__0));
return v___x_4913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___redArg___boxed(lean_object* v___dummy_4914_){
_start:
{
lean_object* v_res_4915_; 
v_res_4915_ = l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___redArg();
return v_res_4915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_instAppend(lean_object* v_00_u03b1_4916_){
_start:
{
lean_object* v___x_4917_; 
v___x_4917_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___redArg___closed__0));
return v___x_4917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat___redArg(lean_object* v_d_4918_, lean_object* v_tree_4919_){
_start:
{
lean_object* v___x_4921_; lean_object* v___x_4922_; lean_object* v___x_4923_; 
v___x_4921_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_ImportData_new___closed__0));
v___x_4922_ = lean_st_ref_swap(v_d_4918_, v___x_4921_);
v___x_4923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4923_, 0, v_tree_4919_);
lean_ctor_set(v___x_4923_, 1, v___x_4922_);
return v___x_4923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat___redArg___boxed(lean_object* v_d_4924_, lean_object* v_tree_4925_, lean_object* v_a_4926_){
_start:
{
lean_object* v_res_4927_; 
v_res_4927_ = l_Lean_Meta_LazyDiscrTree_toFlat___redArg(v_d_4924_, v_tree_4925_);
lean_dec(v_d_4924_);
return v_res_4927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat(lean_object* v_00_u03b1_4928_, lean_object* v_d_4929_, lean_object* v_tree_4930_){
_start:
{
lean_object* v___x_4932_; 
v___x_4932_ = l_Lean_Meta_LazyDiscrTree_toFlat___redArg(v_d_4929_, v_tree_4930_);
return v___x_4932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat___boxed(lean_object* v_00_u03b1_4933_, lean_object* v_d_4934_, lean_object* v_tree_4935_, lean_object* v_a_4936_){
_start:
{
lean_object* v_res_4937_; 
v_res_4937_ = l_Lean_Meta_LazyDiscrTree_toFlat(v_00_u03b1_4933_, v_d_4934_, v_tree_4935_);
lean_dec(v_d_4934_);
return v_res_4937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(lean_object* v_cctx_4938_, lean_object* v_env_4939_, lean_object* v_act_4940_, lean_object* v_d_4941_, lean_object* v_cacheRef_4942_, lean_object* v_tree_4943_, lean_object* v_mname_4944_, lean_object* v_mdata_4945_, lean_object* v_i_4946_){
_start:
{
lean_object* v_constants_4948_; lean_object* v___x_4949_; uint8_t v___x_4950_; 
v_constants_4948_ = lean_ctor_get(v_mdata_4945_, 2);
v___x_4949_ = lean_array_get_size(v_constants_4948_);
v___x_4950_ = lean_nat_dec_lt(v_i_4946_, v___x_4949_);
if (v___x_4950_ == 0)
{
lean_dec(v_i_4946_);
lean_dec(v_mname_4944_);
lean_dec_ref(v_act_4940_);
lean_dec_ref(v_env_4939_);
lean_dec_ref(v_cctx_4938_);
return v_tree_4943_;
}
else
{
lean_object* v___x_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; lean_object* v___x_4954_; lean_object* v___x_4955_; 
v___x_4951_ = lean_array_fget_borrowed(v_constants_4948_, v_i_4946_);
lean_inc(v___x_4951_);
v___x_4952_ = l_Lean_AsyncConstantInfo_ofConstantInfo(v___x_4951_);
lean_inc_ref(v_act_4940_);
lean_inc(v_mname_4944_);
lean_inc_ref(v_env_4939_);
lean_inc_ref(v_cctx_4938_);
v___x_4953_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_4938_, v_env_4939_, v_mname_4944_, v_d_4941_, v_cacheRef_4942_, v_tree_4943_, v_act_4940_, v___x_4952_);
v___x_4954_ = lean_unsigned_to_nat(1u);
v___x_4955_ = lean_nat_add(v_i_4946_, v___x_4954_);
lean_dec(v_i_4946_);
v_tree_4943_ = v___x_4953_;
v_i_4946_ = v___x_4955_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg___boxed(lean_object* v_cctx_4957_, lean_object* v_env_4958_, lean_object* v_act_4959_, lean_object* v_d_4960_, lean_object* v_cacheRef_4961_, lean_object* v_tree_4962_, lean_object* v_mname_4963_, lean_object* v_mdata_4964_, lean_object* v_i_4965_, lean_object* v_a_4966_){
_start:
{
lean_object* v_res_4967_; 
v_res_4967_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(v_cctx_4957_, v_env_4958_, v_act_4959_, v_d_4960_, v_cacheRef_4961_, v_tree_4962_, v_mname_4963_, v_mdata_4964_, v_i_4965_);
lean_dec_ref(v_mdata_4964_);
lean_dec(v_cacheRef_4961_);
lean_dec(v_d_4960_);
return v_res_4967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule(lean_object* v_00_u03b1_4968_, lean_object* v_cctx_4969_, lean_object* v_env_4970_, lean_object* v_act_4971_, lean_object* v_d_4972_, lean_object* v_cacheRef_4973_, lean_object* v_tree_4974_, lean_object* v_mname_4975_, lean_object* v_mdata_4976_, lean_object* v_i_4977_){
_start:
{
lean_object* v___x_4979_; 
v___x_4979_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(v_cctx_4969_, v_env_4970_, v_act_4971_, v_d_4972_, v_cacheRef_4973_, v_tree_4974_, v_mname_4975_, v_mdata_4976_, v_i_4977_);
return v___x_4979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule___boxed(lean_object* v_00_u03b1_4980_, lean_object* v_cctx_4981_, lean_object* v_env_4982_, lean_object* v_act_4983_, lean_object* v_d_4984_, lean_object* v_cacheRef_4985_, lean_object* v_tree_4986_, lean_object* v_mname_4987_, lean_object* v_mdata_4988_, lean_object* v_i_4989_, lean_object* v_a_4990_){
_start:
{
lean_object* v_res_4991_; 
v_res_4991_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule(v_00_u03b1_4980_, v_cctx_4981_, v_env_4982_, v_act_4983_, v_d_4984_, v_cacheRef_4985_, v_tree_4986_, v_mname_4987_, v_mdata_4988_, v_i_4989_);
lean_dec_ref(v_mdata_4988_);
lean_dec(v_cacheRef_4985_);
lean_dec(v_d_4984_);
return v_res_4991_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg(lean_object* v_cctx_4992_, lean_object* v_env_4993_, lean_object* v_act_4994_, lean_object* v_d_4995_, lean_object* v_cacheRef_4996_, lean_object* v_tree_4997_, lean_object* v_start_4998_, lean_object* v_stop_4999_){
_start:
{
uint8_t v___x_5001_; 
v___x_5001_ = lean_nat_dec_lt(v_start_4998_, v_stop_4999_);
if (v___x_5001_ == 0)
{
lean_object* v___x_5002_; 
lean_dec(v_start_4998_);
lean_dec_ref(v_act_4994_);
lean_dec_ref(v_env_4993_);
lean_dec_ref(v_cctx_4992_);
v___x_5002_ = l_Lean_Meta_LazyDiscrTree_toFlat___redArg(v_d_4995_, v_tree_4997_);
return v___x_5002_;
}
else
{
lean_object* v___x_5003_; lean_object* v_moduleData_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; lean_object* v___x_5007_; lean_object* v_mname_5008_; lean_object* v_mdata_5009_; lean_object* v___x_5010_; lean_object* v___x_5011_; lean_object* v___x_5012_; lean_object* v___x_5013_; 
v___x_5003_ = l_Lean_Environment_header(v_env_4993_);
v_moduleData_5004_ = lean_ctor_get(v___x_5003_, 6);
lean_inc_ref(v_moduleData_5004_);
v___x_5005_ = lean_box(0);
v___x_5006_ = l_Lean_instInhabitedModuleData_default;
v___x_5007_ = l_Lean_EnvironmentHeader_moduleNames(v___x_5003_);
v_mname_5008_ = lean_array_get(v___x_5005_, v___x_5007_, v_start_4998_);
lean_dec_ref(v___x_5007_);
v_mdata_5009_ = lean_array_get(v___x_5006_, v_moduleData_5004_, v_start_4998_);
lean_dec_ref(v_moduleData_5004_);
v___x_5010_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_act_4994_);
lean_inc_ref(v_env_4993_);
lean_inc_ref(v_cctx_4992_);
v___x_5011_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(v_cctx_4992_, v_env_4993_, v_act_4994_, v_d_4995_, v_cacheRef_4996_, v_tree_4997_, v_mname_5008_, v_mdata_5009_, v___x_5010_);
lean_dec(v_mdata_5009_);
v___x_5012_ = lean_unsigned_to_nat(1u);
v___x_5013_ = lean_nat_add(v_start_4998_, v___x_5012_);
lean_dec(v_start_4998_);
v_tree_4997_ = v___x_5011_;
v_start_4998_ = v___x_5013_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg___boxed(lean_object* v_cctx_5015_, lean_object* v_env_5016_, lean_object* v_act_5017_, lean_object* v_d_5018_, lean_object* v_cacheRef_5019_, lean_object* v_tree_5020_, lean_object* v_start_5021_, lean_object* v_stop_5022_, lean_object* v_a_5023_){
_start:
{
lean_object* v_res_5024_; 
v_res_5024_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg(v_cctx_5015_, v_env_5016_, v_act_5017_, v_d_5018_, v_cacheRef_5019_, v_tree_5020_, v_start_5021_, v_stop_5022_);
lean_dec(v_stop_5022_);
lean_dec(v_cacheRef_5019_);
lean_dec(v_d_5018_);
return v_res_5024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go(lean_object* v_00_u03b1_5025_, lean_object* v_cctx_5026_, lean_object* v_env_5027_, lean_object* v_act_5028_, lean_object* v_d_5029_, lean_object* v_cacheRef_5030_, lean_object* v_tree_5031_, lean_object* v_start_5032_, lean_object* v_stop_5033_){
_start:
{
lean_object* v___x_5035_; 
v___x_5035_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg(v_cctx_5026_, v_env_5027_, v_act_5028_, v_d_5029_, v_cacheRef_5030_, v_tree_5031_, v_start_5032_, v_stop_5033_);
return v___x_5035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___boxed(lean_object* v_00_u03b1_5036_, lean_object* v_cctx_5037_, lean_object* v_env_5038_, lean_object* v_act_5039_, lean_object* v_d_5040_, lean_object* v_cacheRef_5041_, lean_object* v_tree_5042_, lean_object* v_start_5043_, lean_object* v_stop_5044_, lean_object* v_a_5045_){
_start:
{
lean_object* v_res_5046_; 
v_res_5046_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go(v_00_u03b1_5036_, v_cctx_5037_, v_env_5038_, v_act_5039_, v_d_5040_, v_cacheRef_5041_, v_tree_5042_, v_start_5043_, v_stop_5044_);
lean_dec(v_stop_5044_);
lean_dec(v_cacheRef_5041_);
lean_dec(v_d_5040_);
return v_res_5046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___redArg(lean_object* v_cctx_5047_, lean_object* v_ngen_5048_, lean_object* v_env_5049_, lean_object* v_act_5050_, lean_object* v_start_5051_, lean_object* v_stop_5052_){
_start:
{
lean_object* v___x_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; lean_object* v___x_5057_; lean_object* v___x_5058_; 
v___x_5054_ = l_Lean_Meta_LazyDiscrTree_Cache_empty(v_ngen_5048_);
v___x_5055_ = lean_st_mk_ref(v___x_5054_);
v___x_5056_ = l_Lean_Meta_LazyDiscrTree_ImportData_new();
v___x_5057_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1);
v___x_5058_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg(v_cctx_5047_, v_env_5049_, v_act_5050_, v___x_5056_, v___x_5055_, v___x_5057_, v_start_5051_, v_stop_5052_);
lean_dec(v___x_5055_);
lean_dec(v___x_5056_);
return v___x_5058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___redArg___boxed(lean_object* v_cctx_5059_, lean_object* v_ngen_5060_, lean_object* v_env_5061_, lean_object* v_act_5062_, lean_object* v_start_5063_, lean_object* v_stop_5064_, lean_object* v_a_5065_){
_start:
{
lean_object* v_res_5066_; 
v_res_5066_ = l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___redArg(v_cctx_5059_, v_ngen_5060_, v_env_5061_, v_act_5062_, v_start_5063_, v_stop_5064_);
lean_dec(v_stop_5064_);
return v_res_5066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq(lean_object* v_00_u03b1_5067_, lean_object* v_cctx_5068_, lean_object* v_ngen_5069_, lean_object* v_env_5070_, lean_object* v_act_5071_, lean_object* v_start_5072_, lean_object* v_stop_5073_){
_start:
{
lean_object* v___x_5075_; 
v___x_5075_ = l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___redArg(v_cctx_5068_, v_ngen_5069_, v_env_5070_, v_act_5071_, v_start_5072_, v_stop_5073_);
return v___x_5075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed(lean_object* v_00_u03b1_5076_, lean_object* v_cctx_5077_, lean_object* v_ngen_5078_, lean_object* v_env_5079_, lean_object* v_act_5080_, lean_object* v_start_5081_, lean_object* v_stop_5082_, lean_object* v_a_5083_){
_start:
{
lean_object* v_res_5084_; 
v_res_5084_ = l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq(v_00_u03b1_5076_, v_cctx_5077_, v_ngen_5078_, v_env_5079_, v_act_5080_, v_start_5081_, v_stop_5082_);
lean_dec(v_stop_5082_);
return v_res_5084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___redArg___lam__0(lean_object* v_inst_5085_, lean_object* v_x1_5086_, lean_object* v_x2_5087_){
_start:
{
lean_object* v___x_5088_; lean_object* v___x_5089_; 
v___x_5088_ = lean_task_get_own(v_x2_5087_);
v___x_5089_ = lean_apply_2(v_inst_5085_, v_x1_5086_, v___x_5088_);
return v___x_5089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___redArg(lean_object* v_inst_5090_, lean_object* v_z_5091_, lean_object* v_tasks_5092_){
_start:
{
lean_object* v___x_5093_; lean_object* v___x_5094_; lean_object* v___x_5095_; uint8_t v___x_5096_; 
v___x_5093_ = lean_unsigned_to_nat(0u);
v___x_5094_ = lean_array_get_size(v_tasks_5092_);
v___x_5095_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__9));
v___x_5096_ = lean_nat_dec_lt(v___x_5093_, v___x_5094_);
if (v___x_5096_ == 0)
{
lean_dec_ref(v_tasks_5092_);
lean_dec(v_inst_5090_);
return v_z_5091_;
}
else
{
lean_object* v___f_5097_; uint8_t v___x_5098_; 
v___f_5097_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_combineGet___redArg___lam__0), 3, 1);
lean_closure_set(v___f_5097_, 0, v_inst_5090_);
v___x_5098_ = lean_nat_dec_le(v___x_5094_, v___x_5094_);
if (v___x_5098_ == 0)
{
if (v___x_5096_ == 0)
{
lean_dec_ref(v___f_5097_);
lean_dec_ref(v_tasks_5092_);
return v_z_5091_;
}
else
{
size_t v___x_5099_; size_t v___x_5100_; lean_object* v___x_5101_; 
v___x_5099_ = ((size_t)0ULL);
v___x_5100_ = lean_usize_of_nat(v___x_5094_);
v___x_5101_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_5095_, v___f_5097_, v_tasks_5092_, v___x_5099_, v___x_5100_, v_z_5091_);
return v___x_5101_;
}
}
else
{
size_t v___x_5102_; size_t v___x_5103_; lean_object* v___x_5104_; 
v___x_5102_ = ((size_t)0ULL);
v___x_5103_ = lean_usize_of_nat(v___x_5094_);
v___x_5104_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_5095_, v___f_5097_, v_tasks_5092_, v___x_5102_, v___x_5103_, v_z_5091_);
return v___x_5104_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet(lean_object* v_00_u03b1_5105_, lean_object* v_inst_5106_, lean_object* v_z_5107_, lean_object* v_tasks_5108_){
_start:
{
lean_object* v___x_5109_; 
v___x_5109_ = l_Lean_Meta_LazyDiscrTree_combineGet___redArg(v_inst_5106_, v_z_5107_, v_tasks_5108_);
return v___x_5109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg___lam__0(lean_object* v_toPure_5110_, lean_object* v___x_5111_, lean_object* v_____r_5112_){
_start:
{
lean_object* v___x_5113_; 
v___x_5113_ = lean_apply_2(v_toPure_5110_, lean_box(0), v___x_5111_);
return v___x_5113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg___lam__1(lean_object* v_toPure_5114_, lean_object* v_setNGen_5115_, lean_object* v_toBind_5116_, lean_object* v_ngen_5117_){
_start:
{
lean_object* v_namePrefix_5118_; lean_object* v_idx_5119_; lean_object* v___x_5121_; uint8_t v_isShared_5122_; uint8_t v_isSharedCheck_5133_; 
v_namePrefix_5118_ = lean_ctor_get(v_ngen_5117_, 0);
v_idx_5119_ = lean_ctor_get(v_ngen_5117_, 1);
v_isSharedCheck_5133_ = !lean_is_exclusive(v_ngen_5117_);
if (v_isSharedCheck_5133_ == 0)
{
v___x_5121_ = v_ngen_5117_;
v_isShared_5122_ = v_isSharedCheck_5133_;
goto v_resetjp_5120_;
}
else
{
lean_inc(v_idx_5119_);
lean_inc(v_namePrefix_5118_);
lean_dec(v_ngen_5117_);
v___x_5121_ = lean_box(0);
v_isShared_5122_ = v_isSharedCheck_5133_;
goto v_resetjp_5120_;
}
v_resetjp_5120_:
{
lean_object* v___x_5123_; lean_object* v___x_5124_; lean_object* v___x_5126_; 
lean_inc(v_idx_5119_);
lean_inc(v_namePrefix_5118_);
v___x_5123_ = l_Lean_Name_num___override(v_namePrefix_5118_, v_idx_5119_);
v___x_5124_ = lean_unsigned_to_nat(1u);
if (v_isShared_5122_ == 0)
{
lean_ctor_set(v___x_5121_, 1, v___x_5124_);
lean_ctor_set(v___x_5121_, 0, v___x_5123_);
v___x_5126_ = v___x_5121_;
goto v_reusejp_5125_;
}
else
{
lean_object* v_reuseFailAlloc_5132_; 
v_reuseFailAlloc_5132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5132_, 0, v___x_5123_);
lean_ctor_set(v_reuseFailAlloc_5132_, 1, v___x_5124_);
v___x_5126_ = v_reuseFailAlloc_5132_;
goto v_reusejp_5125_;
}
v_reusejp_5125_:
{
lean_object* v___f_5127_; lean_object* v___x_5128_; lean_object* v___x_5129_; lean_object* v___x_5130_; lean_object* v___x_5131_; 
v___f_5127_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5127_, 0, v_toPure_5114_);
lean_closure_set(v___f_5127_, 1, v___x_5126_);
v___x_5128_ = lean_nat_add(v_idx_5119_, v___x_5124_);
lean_dec(v_idx_5119_);
v___x_5129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5129_, 0, v_namePrefix_5118_);
lean_ctor_set(v___x_5129_, 1, v___x_5128_);
v___x_5130_ = lean_apply_1(v_setNGen_5115_, v___x_5129_);
v___x_5131_ = lean_apply_4(v_toBind_5116_, lean_box(0), lean_box(0), v___x_5130_, v___f_5127_);
return v___x_5131_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg(lean_object* v_inst_5134_, lean_object* v_inst_5135_){
_start:
{
lean_object* v_toApplicative_5136_; lean_object* v_toBind_5137_; lean_object* v_getNGen_5138_; lean_object* v_setNGen_5139_; lean_object* v_toPure_5140_; lean_object* v___f_5141_; lean_object* v___x_5142_; 
v_toApplicative_5136_ = lean_ctor_get(v_inst_5134_, 0);
lean_inc_ref(v_toApplicative_5136_);
v_toBind_5137_ = lean_ctor_get(v_inst_5134_, 1);
lean_inc_n(v_toBind_5137_, 2);
lean_dec_ref(v_inst_5134_);
v_getNGen_5138_ = lean_ctor_get(v_inst_5135_, 0);
lean_inc(v_getNGen_5138_);
v_setNGen_5139_ = lean_ctor_get(v_inst_5135_, 1);
lean_inc(v_setNGen_5139_);
lean_dec_ref(v_inst_5135_);
v_toPure_5140_ = lean_ctor_get(v_toApplicative_5136_, 1);
lean_inc(v_toPure_5140_);
lean_dec_ref(v_toApplicative_5136_);
v___f_5141_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg___lam__1), 4, 3);
lean_closure_set(v___f_5141_, 0, v_toPure_5140_);
lean_closure_set(v___f_5141_, 1, v_setNGen_5139_);
lean_closure_set(v___f_5141_, 2, v_toBind_5137_);
v___x_5142_ = lean_apply_4(v_toBind_5137_, lean_box(0), lean_box(0), v_getNGen_5138_, v___f_5141_);
return v___x_5142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen(lean_object* v_M_5143_, lean_object* v_inst_5144_, lean_object* v_inst_5145_){
_start:
{
lean_object* v___x_5146_; 
v___x_5146_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg(v_inst_5144_, v_inst_5145_);
return v___x_5146_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg(lean_object* v_cctx_5147_, lean_object* v_env_5148_, lean_object* v_modName_5149_, lean_object* v_d_5150_, lean_object* v_val_5151_, lean_object* v_act_5152_, lean_object* v_as_5153_, size_t v_sz_5154_, size_t v_i_5155_, lean_object* v_b_5156_){
_start:
{
uint8_t v___x_5158_; 
v___x_5158_ = lean_usize_dec_lt(v_i_5155_, v_sz_5154_);
if (v___x_5158_ == 0)
{
lean_dec_ref(v_act_5152_);
lean_dec(v_modName_5149_);
lean_dec_ref(v_env_5148_);
lean_dec_ref(v_cctx_5147_);
return v_b_5156_;
}
else
{
lean_object* v_a_5159_; lean_object* v___x_5160_; size_t v___x_5161_; size_t v___x_5162_; 
v_a_5159_ = lean_array_uget_borrowed(v_as_5153_, v_i_5155_);
lean_inc(v_a_5159_);
lean_inc_ref(v_act_5152_);
lean_inc(v_modName_5149_);
lean_inc_ref(v_env_5148_);
lean_inc_ref(v_cctx_5147_);
v___x_5160_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_5147_, v_env_5148_, v_modName_5149_, v_d_5150_, v_val_5151_, v_b_5156_, v_act_5152_, v_a_5159_);
v___x_5161_ = ((size_t)1ULL);
v___x_5162_ = lean_usize_add(v_i_5155_, v___x_5161_);
v_i_5155_ = v___x_5162_;
v_b_5156_ = v___x_5160_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg___boxed(lean_object* v_cctx_5164_, lean_object* v_env_5165_, lean_object* v_modName_5166_, lean_object* v_d_5167_, lean_object* v_val_5168_, lean_object* v_act_5169_, lean_object* v_as_5170_, lean_object* v_sz_5171_, lean_object* v_i_5172_, lean_object* v_b_5173_, lean_object* v___y_5174_){
_start:
{
size_t v_sz_boxed_5175_; size_t v_i_boxed_5176_; lean_object* v_res_5177_; 
v_sz_boxed_5175_ = lean_unbox_usize(v_sz_5171_);
lean_dec(v_sz_5171_);
v_i_boxed_5176_ = lean_unbox_usize(v_i_5172_);
lean_dec(v_i_5172_);
v_res_5177_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg(v_cctx_5164_, v_env_5165_, v_modName_5166_, v_d_5167_, v_val_5168_, v_act_5169_, v_as_5170_, v_sz_boxed_5175_, v_i_boxed_5176_, v_b_5173_);
lean_dec_ref(v_as_5170_);
lean_dec(v_val_5168_);
lean_dec(v_d_5167_);
return v_res_5177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(lean_object* v_cctx_5178_, lean_object* v_ngen_5179_, lean_object* v_env_5180_, lean_object* v_d_5181_, lean_object* v_act_5182_){
_start:
{
lean_object* v___x_5184_; lean_object* v_mainModule_5185_; lean_object* v___x_5186_; lean_object* v___x_5187_; lean_object* v___x_5188_; uint8_t v___x_5189_; lean_object* v___x_5190_; size_t v_sz_5191_; size_t v___x_5192_; lean_object* v___x_5193_; 
v___x_5184_ = l_Lean_Environment_header(v_env_5180_);
v_mainModule_5185_ = lean_ctor_get(v___x_5184_, 0);
lean_inc(v_mainModule_5185_);
lean_dec_ref(v___x_5184_);
v___x_5186_ = l_Lean_Meta_LazyDiscrTree_Cache_empty(v_ngen_5179_);
v___x_5187_ = lean_st_mk_ref(v___x_5186_);
v___x_5188_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1);
v___x_5189_ = 1;
v___x_5190_ = l_Lean_Environment_getLocalConstantInfos(v_env_5180_, v___x_5189_);
v_sz_5191_ = lean_array_size(v___x_5190_);
v___x_5192_ = ((size_t)0ULL);
v___x_5193_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg(v_cctx_5178_, v_env_5180_, v_mainModule_5185_, v_d_5181_, v___x_5187_, v_act_5182_, v___x_5190_, v_sz_5191_, v___x_5192_, v___x_5188_);
lean_dec_ref(v___x_5190_);
lean_dec(v___x_5187_);
return v___x_5193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg___boxed(lean_object* v_cctx_5194_, lean_object* v_ngen_5195_, lean_object* v_env_5196_, lean_object* v_d_5197_, lean_object* v_act_5198_, lean_object* v_a_5199_){
_start:
{
lean_object* v_res_5200_; 
v_res_5200_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(v_cctx_5194_, v_ngen_5195_, v_env_5196_, v_d_5197_, v_act_5198_);
lean_dec(v_d_5197_);
return v_res_5200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree(lean_object* v_00_u03b1_5201_, lean_object* v_cctx_5202_, lean_object* v_ngen_5203_, lean_object* v_env_5204_, lean_object* v_d_5205_, lean_object* v_act_5206_){
_start:
{
lean_object* v___x_5208_; 
v___x_5208_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(v_cctx_5202_, v_ngen_5203_, v_env_5204_, v_d_5205_, v_act_5206_);
return v___x_5208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___boxed(lean_object* v_00_u03b1_5209_, lean_object* v_cctx_5210_, lean_object* v_ngen_5211_, lean_object* v_env_5212_, lean_object* v_d_5213_, lean_object* v_act_5214_, lean_object* v_a_5215_){
_start:
{
lean_object* v_res_5216_; 
v_res_5216_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree(v_00_u03b1_5209_, v_cctx_5210_, v_ngen_5211_, v_env_5212_, v_d_5213_, v_act_5214_);
lean_dec(v_d_5213_);
return v_res_5216_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0(lean_object* v_00_u03b1_5217_, lean_object* v_cctx_5218_, lean_object* v_env_5219_, lean_object* v_modName_5220_, lean_object* v_d_5221_, lean_object* v_val_5222_, lean_object* v_act_5223_, lean_object* v_as_5224_, size_t v_sz_5225_, size_t v_i_5226_, lean_object* v_b_5227_){
_start:
{
lean_object* v___x_5229_; 
v___x_5229_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg(v_cctx_5218_, v_env_5219_, v_modName_5220_, v_d_5221_, v_val_5222_, v_act_5223_, v_as_5224_, v_sz_5225_, v_i_5226_, v_b_5227_);
return v___x_5229_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___boxed(lean_object* v_00_u03b1_5230_, lean_object* v_cctx_5231_, lean_object* v_env_5232_, lean_object* v_modName_5233_, lean_object* v_d_5234_, lean_object* v_val_5235_, lean_object* v_act_5236_, lean_object* v_as_5237_, lean_object* v_sz_5238_, lean_object* v_i_5239_, lean_object* v_b_5240_, lean_object* v___y_5241_){
_start:
{
size_t v_sz_boxed_5242_; size_t v_i_boxed_5243_; lean_object* v_res_5244_; 
v_sz_boxed_5242_ = lean_unbox_usize(v_sz_5238_);
lean_dec(v_sz_5238_);
v_i_boxed_5243_ = lean_unbox_usize(v_i_5239_);
lean_dec(v_i_5239_);
v_res_5244_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0(v_00_u03b1_5230_, v_cctx_5231_, v_env_5232_, v_modName_5233_, v_d_5234_, v_val_5235_, v_act_5236_, v_as_5237_, v_sz_boxed_5242_, v_i_boxed_5243_, v_b_5240_);
lean_dec_ref(v_as_5237_);
lean_dec(v_val_5235_);
lean_dec(v_d_5234_);
return v_res_5244_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(lean_object* v_x_5245_, lean_object* v_x_5246_, lean_object* v___y_5247_, lean_object* v___y_5248_, lean_object* v___y_5249_, lean_object* v___y_5250_){
_start:
{
if (lean_obj_tag(v_x_5246_) == 0)
{
lean_object* v___x_5252_; 
v___x_5252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5252_, 0, v_x_5245_);
return v___x_5252_;
}
else
{
lean_object* v_head_5253_; lean_object* v_tail_5254_; lean_object* v___x_5255_; 
v_head_5253_ = lean_ctor_get(v_x_5246_, 0);
lean_inc(v_head_5253_);
v_tail_5254_ = lean_ctor_get(v_x_5246_, 1);
lean_inc(v_tail_5254_);
lean_dec_ref_known(v_x_5246_, 2);
v___x_5255_ = l_Lean_Meta_LazyDiscrTree_dropKey___redArg(v_x_5245_, v_head_5253_, v___y_5247_, v___y_5248_, v___y_5249_, v___y_5250_);
if (lean_obj_tag(v___x_5255_) == 0)
{
lean_object* v_a_5256_; 
v_a_5256_ = lean_ctor_get(v___x_5255_, 0);
lean_inc(v_a_5256_);
lean_dec_ref_known(v___x_5255_, 1);
v_x_5245_ = v_a_5256_;
v_x_5246_ = v_tail_5254_;
goto _start;
}
else
{
lean_dec(v_tail_5254_);
return v___x_5255_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg___boxed(lean_object* v_x_5258_, lean_object* v_x_5259_, lean_object* v___y_5260_, lean_object* v___y_5261_, lean_object* v___y_5262_, lean_object* v___y_5263_, lean_object* v___y_5264_){
_start:
{
lean_object* v_res_5265_; 
v_res_5265_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_x_5258_, v_x_5259_, v___y_5260_, v___y_5261_, v___y_5262_, v___y_5263_);
lean_dec(v___y_5263_);
lean_dec_ref(v___y_5262_);
lean_dec(v___y_5261_);
lean_dec_ref(v___y_5260_);
return v_res_5265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys___redArg(lean_object* v_t_5266_, lean_object* v_keys_5267_, lean_object* v_a_5268_, lean_object* v_a_5269_, lean_object* v_a_5270_, lean_object* v_a_5271_){
_start:
{
lean_object* v___x_5273_; 
v___x_5273_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_t_5266_, v_keys_5267_, v_a_5268_, v_a_5269_, v_a_5270_, v_a_5271_);
return v___x_5273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys___redArg___boxed(lean_object* v_t_5274_, lean_object* v_keys_5275_, lean_object* v_a_5276_, lean_object* v_a_5277_, lean_object* v_a_5278_, lean_object* v_a_5279_, lean_object* v_a_5280_){
_start:
{
lean_object* v_res_5281_; 
v_res_5281_ = l_Lean_Meta_LazyDiscrTree_dropKeys___redArg(v_t_5274_, v_keys_5275_, v_a_5276_, v_a_5277_, v_a_5278_, v_a_5279_);
lean_dec(v_a_5279_);
lean_dec_ref(v_a_5278_);
lean_dec(v_a_5277_);
lean_dec_ref(v_a_5276_);
return v_res_5281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys(lean_object* v_00_u03b1_5282_, lean_object* v_t_5283_, lean_object* v_keys_5284_, lean_object* v_a_5285_, lean_object* v_a_5286_, lean_object* v_a_5287_, lean_object* v_a_5288_){
_start:
{
lean_object* v___x_5290_; 
v___x_5290_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_t_5283_, v_keys_5284_, v_a_5285_, v_a_5286_, v_a_5287_, v_a_5288_);
return v___x_5290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys___boxed(lean_object* v_00_u03b1_5291_, lean_object* v_t_5292_, lean_object* v_keys_5293_, lean_object* v_a_5294_, lean_object* v_a_5295_, lean_object* v_a_5296_, lean_object* v_a_5297_, lean_object* v_a_5298_){
_start:
{
lean_object* v_res_5299_; 
v_res_5299_ = l_Lean_Meta_LazyDiscrTree_dropKeys(v_00_u03b1_5291_, v_t_5292_, v_keys_5293_, v_a_5294_, v_a_5295_, v_a_5296_, v_a_5297_);
lean_dec(v_a_5297_);
lean_dec_ref(v_a_5296_);
lean_dec(v_a_5295_);
lean_dec_ref(v_a_5294_);
return v_res_5299_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0(lean_object* v_00_u03b1_5300_, lean_object* v_x_5301_, lean_object* v_x_5302_, lean_object* v___y_5303_, lean_object* v___y_5304_, lean_object* v___y_5305_, lean_object* v___y_5306_){
_start:
{
lean_object* v___x_5308_; 
v___x_5308_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_x_5301_, v_x_5302_, v___y_5303_, v___y_5304_, v___y_5305_, v___y_5306_);
return v___x_5308_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___boxed(lean_object* v_00_u03b1_5309_, lean_object* v_x_5310_, lean_object* v_x_5311_, lean_object* v___y_5312_, lean_object* v___y_5313_, lean_object* v___y_5314_, lean_object* v___y_5315_, lean_object* v___y_5316_){
_start:
{
lean_object* v_res_5317_; 
v_res_5317_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0(v_00_u03b1_5309_, v_x_5310_, v_x_5311_, v___y_5312_, v___y_5313_, v___y_5314_, v___y_5315_);
lean_dec(v___y_5315_);
lean_dec_ref(v___y_5314_);
lean_dec(v___y_5313_);
lean_dec_ref(v___y_5312_);
return v_res_5317_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(lean_object* v_as_5318_, size_t v_sz_5319_, size_t v_i_5320_, lean_object* v_b_5321_, lean_object* v___y_5322_, lean_object* v___y_5323_, lean_object* v___y_5324_, lean_object* v___y_5325_, lean_object* v___y_5326_){
_start:
{
uint8_t v___x_5328_; 
v___x_5328_ = lean_usize_dec_lt(v_i_5320_, v_sz_5319_);
if (v___x_5328_ == 0)
{
lean_object* v___x_5329_; 
v___x_5329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5329_, 0, v_b_5321_);
return v___x_5329_;
}
else
{
lean_object* v_a_5330_; lean_object* v___x_5331_; 
v_a_5330_ = lean_array_uget_borrowed(v_as_5318_, v_i_5320_);
v___x_5331_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(v_a_5330_, v_b_5321_, v___y_5322_, v___y_5323_, v___y_5324_, v___y_5325_, v___y_5326_);
if (lean_obj_tag(v___x_5331_) == 0)
{
lean_object* v_a_5332_; lean_object* v___x_5334_; uint8_t v_isShared_5335_; uint8_t v_isSharedCheck_5344_; 
v_a_5332_ = lean_ctor_get(v___x_5331_, 0);
v_isSharedCheck_5344_ = !lean_is_exclusive(v___x_5331_);
if (v_isSharedCheck_5344_ == 0)
{
v___x_5334_ = v___x_5331_;
v_isShared_5335_ = v_isSharedCheck_5344_;
goto v_resetjp_5333_;
}
else
{
lean_inc(v_a_5332_);
lean_dec(v___x_5331_);
v___x_5334_ = lean_box(0);
v_isShared_5335_ = v_isSharedCheck_5344_;
goto v_resetjp_5333_;
}
v_resetjp_5333_:
{
if (lean_obj_tag(v_a_5332_) == 0)
{
lean_object* v_a_5336_; lean_object* v___x_5338_; 
v_a_5336_ = lean_ctor_get(v_a_5332_, 0);
lean_inc(v_a_5336_);
lean_dec_ref_known(v_a_5332_, 1);
if (v_isShared_5335_ == 0)
{
lean_ctor_set(v___x_5334_, 0, v_a_5336_);
v___x_5338_ = v___x_5334_;
goto v_reusejp_5337_;
}
else
{
lean_object* v_reuseFailAlloc_5339_; 
v_reuseFailAlloc_5339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5339_, 0, v_a_5336_);
v___x_5338_ = v_reuseFailAlloc_5339_;
goto v_reusejp_5337_;
}
v_reusejp_5337_:
{
return v___x_5338_;
}
}
else
{
lean_object* v_a_5340_; size_t v___x_5341_; size_t v___x_5342_; 
lean_del_object(v___x_5334_);
v_a_5340_ = lean_ctor_get(v_a_5332_, 0);
lean_inc(v_a_5340_);
lean_dec_ref_known(v_a_5332_, 1);
v___x_5341_ = ((size_t)1ULL);
v___x_5342_ = lean_usize_add(v_i_5320_, v___x_5341_);
v_i_5320_ = v___x_5342_;
v_b_5321_ = v_a_5340_;
goto _start;
}
}
}
else
{
lean_object* v_a_5345_; lean_object* v___x_5347_; uint8_t v_isShared_5348_; uint8_t v_isSharedCheck_5352_; 
v_a_5345_ = lean_ctor_get(v___x_5331_, 0);
v_isSharedCheck_5352_ = !lean_is_exclusive(v___x_5331_);
if (v_isSharedCheck_5352_ == 0)
{
v___x_5347_ = v___x_5331_;
v_isShared_5348_ = v_isSharedCheck_5352_;
goto v_resetjp_5346_;
}
else
{
lean_inc(v_a_5345_);
lean_dec(v___x_5331_);
v___x_5347_ = lean_box(0);
v_isShared_5348_ = v_isSharedCheck_5352_;
goto v_resetjp_5346_;
}
v_resetjp_5346_:
{
lean_object* v___x_5350_; 
if (v_isShared_5348_ == 0)
{
v___x_5350_ = v___x_5347_;
goto v_reusejp_5349_;
}
else
{
lean_object* v_reuseFailAlloc_5351_; 
v_reuseFailAlloc_5351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5351_, 0, v_a_5345_);
v___x_5350_ = v_reuseFailAlloc_5351_;
goto v_reusejp_5349_;
}
v_reusejp_5349_:
{
return v___x_5350_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(lean_object* v_next_5353_, lean_object* v_a_5354_, lean_object* v_a_5355_, lean_object* v_a_5356_, lean_object* v_a_5357_, lean_object* v_a_5358_){
_start:
{
lean_object* v___x_5360_; uint8_t v___x_5361_; 
v___x_5360_ = lean_unsigned_to_nat(0u);
v___x_5361_ = lean_nat_dec_eq(v_next_5353_, v___x_5360_);
if (v___x_5361_ == 0)
{
lean_object* v___x_5362_; 
v___x_5362_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_next_5353_, v_a_5354_, v_a_5355_, v_a_5356_, v_a_5357_, v_a_5358_);
if (lean_obj_tag(v___x_5362_) == 0)
{
lean_object* v_a_5363_; lean_object* v_snd_5364_; lean_object* v_fst_5365_; lean_object* v_fst_5366_; lean_object* v_snd_5367_; lean_object* v___x_5368_; 
v_a_5363_ = lean_ctor_get(v___x_5362_, 0);
lean_inc(v_a_5363_);
lean_dec_ref_known(v___x_5362_, 1);
v_snd_5364_ = lean_ctor_get(v_a_5363_, 1);
lean_inc(v_snd_5364_);
v_fst_5365_ = lean_ctor_get(v_a_5363_, 0);
lean_inc(v_fst_5365_);
lean_dec(v_a_5363_);
v_fst_5366_ = lean_ctor_get(v_snd_5364_, 0);
lean_inc(v_fst_5366_);
v_snd_5367_ = lean_ctor_get(v_snd_5364_, 1);
lean_inc(v_snd_5367_);
lean_dec(v_snd_5364_);
v___x_5368_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_fst_5366_, v_a_5354_, v_a_5355_, v_a_5356_, v_a_5357_, v_a_5358_);
if (lean_obj_tag(v___x_5368_) == 0)
{
lean_object* v_a_5369_; lean_object* v_buckets_5370_; lean_object* v___x_5371_; size_t v_sz_5372_; size_t v___x_5373_; lean_object* v___x_5374_; 
v_a_5369_ = lean_ctor_get(v___x_5368_, 0);
lean_inc(v_a_5369_);
lean_dec_ref_known(v___x_5368_, 1);
v_buckets_5370_ = lean_ctor_get(v_snd_5367_, 1);
v___x_5371_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v_sz_5372_ = lean_array_size(v_buckets_5370_);
v___x_5373_ = ((size_t)0ULL);
v___x_5374_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(v_buckets_5370_, v_sz_5372_, v___x_5373_, v___x_5371_, v_a_5354_, v_a_5355_, v_a_5356_, v_a_5357_, v_a_5358_);
if (lean_obj_tag(v___x_5374_) == 0)
{
lean_object* v_a_5375_; lean_object* v___x_5377_; uint8_t v_isShared_5378_; uint8_t v_isSharedCheck_5388_; 
v_a_5375_ = lean_ctor_get(v___x_5374_, 0);
v_isSharedCheck_5388_ = !lean_is_exclusive(v___x_5374_);
if (v_isSharedCheck_5388_ == 0)
{
v___x_5377_ = v___x_5374_;
v_isShared_5378_ = v_isSharedCheck_5388_;
goto v_resetjp_5376_;
}
else
{
lean_inc(v_a_5375_);
lean_dec(v___x_5374_);
v___x_5377_ = lean_box(0);
v_isShared_5378_ = v_isSharedCheck_5388_;
goto v_resetjp_5376_;
}
v_resetjp_5376_:
{
lean_object* v___x_5379_; lean_object* v___x_5380_; lean_object* v___x_5381_; lean_object* v___x_5382_; lean_object* v___x_5383_; lean_object* v___x_5384_; lean_object* v___x_5386_; 
v___x_5379_ = lean_st_ref_take(v_a_5354_);
v___x_5380_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5380_, 0, v___x_5371_);
lean_ctor_set(v___x_5380_, 1, v_fst_5366_);
lean_ctor_set(v___x_5380_, 2, v_snd_5367_);
lean_ctor_set(v___x_5380_, 3, v___x_5371_);
v___x_5381_ = lean_array_set(v___x_5379_, v_next_5353_, v___x_5380_);
v___x_5382_ = lean_st_ref_put(v_a_5354_, v___x_5381_);
v___x_5383_ = l_Array_append___redArg(v_fst_5365_, v_a_5369_);
lean_dec(v_a_5369_);
v___x_5384_ = l_Array_append___redArg(v___x_5383_, v_a_5375_);
lean_dec(v_a_5375_);
if (v_isShared_5378_ == 0)
{
lean_ctor_set(v___x_5377_, 0, v___x_5384_);
v___x_5386_ = v___x_5377_;
goto v_reusejp_5385_;
}
else
{
lean_object* v_reuseFailAlloc_5387_; 
v_reuseFailAlloc_5387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5387_, 0, v___x_5384_);
v___x_5386_ = v_reuseFailAlloc_5387_;
goto v_reusejp_5385_;
}
v_reusejp_5385_:
{
return v___x_5386_;
}
}
}
else
{
lean_dec(v_a_5369_);
lean_dec(v_snd_5367_);
lean_dec(v_fst_5366_);
lean_dec(v_fst_5365_);
return v___x_5374_;
}
}
else
{
lean_dec(v_snd_5367_);
lean_dec(v_fst_5366_);
lean_dec(v_fst_5365_);
return v___x_5368_;
}
}
else
{
lean_object* v_a_5389_; lean_object* v___x_5391_; uint8_t v_isShared_5392_; uint8_t v_isSharedCheck_5396_; 
v_a_5389_ = lean_ctor_get(v___x_5362_, 0);
v_isSharedCheck_5396_ = !lean_is_exclusive(v___x_5362_);
if (v_isSharedCheck_5396_ == 0)
{
v___x_5391_ = v___x_5362_;
v_isShared_5392_ = v_isSharedCheck_5396_;
goto v_resetjp_5390_;
}
else
{
lean_inc(v_a_5389_);
lean_dec(v___x_5362_);
v___x_5391_ = lean_box(0);
v_isShared_5392_ = v_isSharedCheck_5396_;
goto v_resetjp_5390_;
}
v_resetjp_5390_:
{
lean_object* v___x_5394_; 
if (v_isShared_5392_ == 0)
{
v___x_5394_ = v___x_5391_;
goto v_reusejp_5393_;
}
else
{
lean_object* v_reuseFailAlloc_5395_; 
v_reuseFailAlloc_5395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5395_, 0, v_a_5389_);
v___x_5394_ = v_reuseFailAlloc_5395_;
goto v_reusejp_5393_;
}
v_reusejp_5393_:
{
return v___x_5394_;
}
}
}
}
else
{
lean_object* v___x_5397_; lean_object* v___x_5398_; 
v___x_5397_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___x_5398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5398_, 0, v___x_5397_);
return v___x_5398_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(lean_object* v_a_5399_, lean_object* v_a_5400_, lean_object* v___y_5401_, lean_object* v___y_5402_, lean_object* v___y_5403_, lean_object* v___y_5404_, lean_object* v___y_5405_){
_start:
{
if (lean_obj_tag(v_a_5399_) == 0)
{
lean_object* v___x_5407_; lean_object* v___x_5408_; 
v___x_5407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5407_, 0, v_a_5400_);
v___x_5408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5408_, 0, v___x_5407_);
return v___x_5408_;
}
else
{
lean_object* v_value_5409_; lean_object* v_tail_5410_; lean_object* v___x_5411_; 
v_value_5409_ = lean_ctor_get(v_a_5399_, 1);
v_tail_5410_ = lean_ctor_get(v_a_5399_, 2);
v___x_5411_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_value_5409_, v___y_5401_, v___y_5402_, v___y_5403_, v___y_5404_, v___y_5405_);
if (lean_obj_tag(v___x_5411_) == 0)
{
lean_object* v_a_5412_; lean_object* v___x_5413_; 
v_a_5412_ = lean_ctor_get(v___x_5411_, 0);
lean_inc(v_a_5412_);
lean_dec_ref_known(v___x_5411_, 1);
v___x_5413_ = l_Array_append___redArg(v_a_5400_, v_a_5412_);
lean_dec(v_a_5412_);
v_a_5399_ = v_tail_5410_;
v_a_5400_ = v___x_5413_;
goto _start;
}
else
{
lean_object* v_a_5415_; lean_object* v___x_5417_; uint8_t v_isShared_5418_; uint8_t v_isSharedCheck_5422_; 
lean_dec_ref(v_a_5400_);
v_a_5415_ = lean_ctor_get(v___x_5411_, 0);
v_isSharedCheck_5422_ = !lean_is_exclusive(v___x_5411_);
if (v_isSharedCheck_5422_ == 0)
{
v___x_5417_ = v___x_5411_;
v_isShared_5418_ = v_isSharedCheck_5422_;
goto v_resetjp_5416_;
}
else
{
lean_inc(v_a_5415_);
lean_dec(v___x_5411_);
v___x_5417_ = lean_box(0);
v_isShared_5418_ = v_isSharedCheck_5422_;
goto v_resetjp_5416_;
}
v_resetjp_5416_:
{
lean_object* v___x_5420_; 
if (v_isShared_5418_ == 0)
{
v___x_5420_ = v___x_5417_;
goto v_reusejp_5419_;
}
else
{
lean_object* v_reuseFailAlloc_5421_; 
v_reuseFailAlloc_5421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5421_, 0, v_a_5415_);
v___x_5420_ = v_reuseFailAlloc_5421_;
goto v_reusejp_5419_;
}
v_reusejp_5419_:
{
return v___x_5420_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg___boxed(lean_object* v_a_5423_, lean_object* v_a_5424_, lean_object* v___y_5425_, lean_object* v___y_5426_, lean_object* v___y_5427_, lean_object* v___y_5428_, lean_object* v___y_5429_, lean_object* v___y_5430_){
_start:
{
lean_object* v_res_5431_; 
v_res_5431_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(v_a_5423_, v_a_5424_, v___y_5425_, v___y_5426_, v___y_5427_, v___y_5428_, v___y_5429_);
lean_dec(v___y_5429_);
lean_dec_ref(v___y_5428_);
lean_dec(v___y_5427_);
lean_dec_ref(v___y_5426_);
lean_dec(v___y_5425_);
lean_dec(v_a_5423_);
return v_res_5431_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg___boxed(lean_object* v_as_5432_, lean_object* v_sz_5433_, lean_object* v_i_5434_, lean_object* v_b_5435_, lean_object* v___y_5436_, lean_object* v___y_5437_, lean_object* v___y_5438_, lean_object* v___y_5439_, lean_object* v___y_5440_, lean_object* v___y_5441_){
_start:
{
size_t v_sz_boxed_5442_; size_t v_i_boxed_5443_; lean_object* v_res_5444_; 
v_sz_boxed_5442_ = lean_unbox_usize(v_sz_5433_);
lean_dec(v_sz_5433_);
v_i_boxed_5443_ = lean_unbox_usize(v_i_5434_);
lean_dec(v_i_5434_);
v_res_5444_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(v_as_5432_, v_sz_boxed_5442_, v_i_boxed_5443_, v_b_5435_, v___y_5436_, v___y_5437_, v___y_5438_, v___y_5439_, v___y_5440_);
lean_dec(v___y_5440_);
lean_dec_ref(v___y_5439_);
lean_dec(v___y_5438_);
lean_dec_ref(v___y_5437_);
lean_dec(v___y_5436_);
lean_dec_ref(v_as_5432_);
return v_res_5444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg___boxed(lean_object* v_next_5445_, lean_object* v_a_5446_, lean_object* v_a_5447_, lean_object* v_a_5448_, lean_object* v_a_5449_, lean_object* v_a_5450_, lean_object* v_a_5451_){
_start:
{
lean_object* v_res_5452_; 
v_res_5452_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_next_5445_, v_a_5446_, v_a_5447_, v_a_5448_, v_a_5449_, v_a_5450_);
lean_dec(v_a_5450_);
lean_dec_ref(v_a_5449_);
lean_dec(v_a_5448_);
lean_dec_ref(v_a_5447_);
lean_dec(v_a_5446_);
lean_dec(v_next_5445_);
return v_res_5452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux(lean_object* v_00_u03b1_5453_, lean_object* v_next_5454_, lean_object* v_a_5455_, lean_object* v_a_5456_, lean_object* v_a_5457_, lean_object* v_a_5458_, lean_object* v_a_5459_){
_start:
{
lean_object* v___x_5461_; 
v___x_5461_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_next_5454_, v_a_5455_, v_a_5456_, v_a_5457_, v_a_5458_, v_a_5459_);
return v___x_5461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___boxed(lean_object* v_00_u03b1_5462_, lean_object* v_next_5463_, lean_object* v_a_5464_, lean_object* v_a_5465_, lean_object* v_a_5466_, lean_object* v_a_5467_, lean_object* v_a_5468_, lean_object* v_a_5469_){
_start:
{
lean_object* v_res_5470_; 
v_res_5470_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux(v_00_u03b1_5462_, v_next_5463_, v_a_5464_, v_a_5465_, v_a_5466_, v_a_5467_, v_a_5468_);
lean_dec(v_a_5468_);
lean_dec_ref(v_a_5467_);
lean_dec(v_a_5466_);
lean_dec_ref(v_a_5465_);
lean_dec(v_a_5464_);
lean_dec(v_next_5463_);
return v_res_5470_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0(lean_object* v_00_u03b1_5471_, lean_object* v_a_5472_, lean_object* v_a_5473_, lean_object* v___y_5474_, lean_object* v___y_5475_, lean_object* v___y_5476_, lean_object* v___y_5477_, lean_object* v___y_5478_){
_start:
{
lean_object* v___x_5480_; 
v___x_5480_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(v_a_5472_, v_a_5473_, v___y_5474_, v___y_5475_, v___y_5476_, v___y_5477_, v___y_5478_);
return v___x_5480_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___boxed(lean_object* v_00_u03b1_5481_, lean_object* v_a_5482_, lean_object* v_a_5483_, lean_object* v___y_5484_, lean_object* v___y_5485_, lean_object* v___y_5486_, lean_object* v___y_5487_, lean_object* v___y_5488_, lean_object* v___y_5489_){
_start:
{
lean_object* v_res_5490_; 
v_res_5490_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0(v_00_u03b1_5481_, v_a_5482_, v_a_5483_, v___y_5484_, v___y_5485_, v___y_5486_, v___y_5487_, v___y_5488_);
lean_dec(v___y_5488_);
lean_dec_ref(v___y_5487_);
lean_dec(v___y_5486_);
lean_dec_ref(v___y_5485_);
lean_dec(v___y_5484_);
lean_dec(v_a_5482_);
return v_res_5490_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1(lean_object* v_00_u03b1_5491_, lean_object* v_as_5492_, size_t v_sz_5493_, size_t v_i_5494_, lean_object* v_b_5495_, lean_object* v___y_5496_, lean_object* v___y_5497_, lean_object* v___y_5498_, lean_object* v___y_5499_, lean_object* v___y_5500_){
_start:
{
lean_object* v___x_5502_; 
v___x_5502_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(v_as_5492_, v_sz_5493_, v_i_5494_, v_b_5495_, v___y_5496_, v___y_5497_, v___y_5498_, v___y_5499_, v___y_5500_);
return v___x_5502_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___boxed(lean_object* v_00_u03b1_5503_, lean_object* v_as_5504_, lean_object* v_sz_5505_, lean_object* v_i_5506_, lean_object* v_b_5507_, lean_object* v___y_5508_, lean_object* v___y_5509_, lean_object* v___y_5510_, lean_object* v___y_5511_, lean_object* v___y_5512_, lean_object* v___y_5513_){
_start:
{
size_t v_sz_boxed_5514_; size_t v_i_boxed_5515_; lean_object* v_res_5516_; 
v_sz_boxed_5514_ = lean_unbox_usize(v_sz_5505_);
lean_dec(v_sz_5505_);
v_i_boxed_5515_ = lean_unbox_usize(v_i_5506_);
lean_dec(v_i_5506_);
v_res_5516_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1(v_00_u03b1_5503_, v_as_5504_, v_sz_boxed_5514_, v_i_boxed_5515_, v_b_5507_, v___y_5508_, v___y_5509_, v___y_5510_, v___y_5511_, v___y_5512_);
lean_dec(v___y_5512_);
lean_dec_ref(v___y_5511_);
lean_dec(v___y_5510_);
lean_dec_ref(v___y_5509_);
lean_dec(v___y_5508_);
lean_dec_ref(v_as_5504_);
return v_res_5516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg(lean_object* v_next_5517_, lean_object* v_rest_5518_, lean_object* v_a_5519_, lean_object* v_a_5520_, lean_object* v_a_5521_, lean_object* v_a_5522_, lean_object* v_a_5523_){
_start:
{
lean_object* v___x_5525_; uint8_t v___x_5526_; 
v___x_5525_ = lean_unsigned_to_nat(0u);
v___x_5526_ = lean_nat_dec_eq(v_next_5517_, v___x_5525_);
if (v___x_5526_ == 0)
{
lean_object* v___x_5527_; 
v___x_5527_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_next_5517_, v_a_5519_, v_a_5520_, v_a_5521_, v_a_5522_, v_a_5523_);
if (lean_obj_tag(v___x_5527_) == 0)
{
lean_object* v_a_5528_; lean_object* v_snd_5529_; 
v_a_5528_ = lean_ctor_get(v___x_5527_, 0);
lean_inc(v_a_5528_);
lean_dec_ref_known(v___x_5527_, 1);
v_snd_5529_ = lean_ctor_get(v_a_5528_, 1);
lean_inc(v_snd_5529_);
lean_dec(v_a_5528_);
if (lean_obj_tag(v_rest_5518_) == 0)
{
lean_object* v___x_5530_; 
lean_dec(v_snd_5529_);
v___x_5530_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_next_5517_, v_a_5519_, v_a_5520_, v_a_5521_, v_a_5522_, v_a_5523_);
lean_dec(v_next_5517_);
return v___x_5530_;
}
else
{
lean_object* v_fst_5531_; lean_object* v_snd_5532_; lean_object* v_head_5533_; lean_object* v_tail_5534_; lean_object* v___x_5535_; uint8_t v___x_5536_; 
lean_dec(v_next_5517_);
v_fst_5531_ = lean_ctor_get(v_snd_5529_, 0);
lean_inc(v_fst_5531_);
v_snd_5532_ = lean_ctor_get(v_snd_5529_, 1);
lean_inc(v_snd_5532_);
lean_dec(v_snd_5529_);
v_head_5533_ = lean_ctor_get(v_rest_5518_, 0);
v_tail_5534_ = lean_ctor_get(v_rest_5518_, 1);
v___x_5535_ = lean_box(3);
v___x_5536_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_head_5533_, v___x_5535_);
if (v___x_5536_ == 0)
{
lean_object* v___x_5537_; 
lean_dec(v_fst_5531_);
v___x_5537_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_snd_5532_, v_head_5533_, v___x_5525_);
lean_dec(v_snd_5532_);
v_next_5517_ = v___x_5537_;
v_rest_5518_ = v_tail_5534_;
goto _start;
}
else
{
lean_dec(v_snd_5532_);
v_next_5517_ = v_fst_5531_;
v_rest_5518_ = v_tail_5534_;
goto _start;
}
}
}
else
{
lean_object* v_a_5540_; lean_object* v___x_5542_; uint8_t v_isShared_5543_; uint8_t v_isSharedCheck_5547_; 
lean_dec(v_next_5517_);
v_a_5540_ = lean_ctor_get(v___x_5527_, 0);
v_isSharedCheck_5547_ = !lean_is_exclusive(v___x_5527_);
if (v_isSharedCheck_5547_ == 0)
{
v___x_5542_ = v___x_5527_;
v_isShared_5543_ = v_isSharedCheck_5547_;
goto v_resetjp_5541_;
}
else
{
lean_inc(v_a_5540_);
lean_dec(v___x_5527_);
v___x_5542_ = lean_box(0);
v_isShared_5543_ = v_isSharedCheck_5547_;
goto v_resetjp_5541_;
}
v_resetjp_5541_:
{
lean_object* v___x_5545_; 
if (v_isShared_5543_ == 0)
{
v___x_5545_ = v___x_5542_;
goto v_reusejp_5544_;
}
else
{
lean_object* v_reuseFailAlloc_5546_; 
v_reuseFailAlloc_5546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5546_, 0, v_a_5540_);
v___x_5545_ = v_reuseFailAlloc_5546_;
goto v_reusejp_5544_;
}
v_reusejp_5544_:
{
return v___x_5545_;
}
}
}
}
else
{
lean_object* v___x_5548_; lean_object* v___x_5549_; 
lean_dec(v_next_5517_);
v___x_5548_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___x_5549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5549_, 0, v___x_5548_);
return v___x_5549_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg___boxed(lean_object* v_next_5550_, lean_object* v_rest_5551_, lean_object* v_a_5552_, lean_object* v_a_5553_, lean_object* v_a_5554_, lean_object* v_a_5555_, lean_object* v_a_5556_, lean_object* v_a_5557_){
_start:
{
lean_object* v_res_5558_; 
v_res_5558_ = l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg(v_next_5550_, v_rest_5551_, v_a_5552_, v_a_5553_, v_a_5554_, v_a_5555_, v_a_5556_);
lean_dec(v_a_5556_);
lean_dec_ref(v_a_5555_);
lean_dec(v_a_5554_);
lean_dec_ref(v_a_5553_);
lean_dec(v_a_5552_);
lean_dec(v_rest_5551_);
return v_res_5558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux(lean_object* v_00_u03b1_5559_, lean_object* v_next_5560_, lean_object* v_rest_5561_, lean_object* v_a_5562_, lean_object* v_a_5563_, lean_object* v_a_5564_, lean_object* v_a_5565_, lean_object* v_a_5566_){
_start:
{
lean_object* v___x_5568_; 
v___x_5568_ = l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg(v_next_5560_, v_rest_5561_, v_a_5562_, v_a_5563_, v_a_5564_, v_a_5565_, v_a_5566_);
return v___x_5568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux___boxed(lean_object* v_00_u03b1_5569_, lean_object* v_next_5570_, lean_object* v_rest_5571_, lean_object* v_a_5572_, lean_object* v_a_5573_, lean_object* v_a_5574_, lean_object* v_a_5575_, lean_object* v_a_5576_, lean_object* v_a_5577_){
_start:
{
lean_object* v_res_5578_; 
v_res_5578_ = l_Lean_Meta_LazyDiscrTree_extractKeyAux(v_00_u03b1_5569_, v_next_5570_, v_rest_5571_, v_a_5572_, v_a_5573_, v_a_5574_, v_a_5575_, v_a_5576_);
lean_dec(v_a_5576_);
lean_dec_ref(v_a_5575_);
lean_dec(v_a_5574_);
lean_dec_ref(v_a_5573_);
lean_dec(v_a_5572_);
lean_dec(v_rest_5571_);
return v_res_5578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey___redArg(lean_object* v_t_5579_, lean_object* v_path_5580_, lean_object* v_a_5581_, lean_object* v_a_5582_, lean_object* v_a_5583_, lean_object* v_a_5584_){
_start:
{
if (lean_obj_tag(v_path_5580_) == 0)
{
lean_object* v___x_5586_; lean_object* v___x_5587_; lean_object* v___x_5588_; 
v___x_5586_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___x_5587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5587_, 0, v___x_5586_);
lean_ctor_set(v___x_5587_, 1, v_t_5579_);
v___x_5588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5588_, 0, v___x_5587_);
return v___x_5588_;
}
else
{
lean_object* v_head_5589_; lean_object* v_tail_5590_; lean_object* v_roots_5591_; lean_object* v___x_5592_; lean_object* v_idx_5593_; lean_object* v___x_5594_; lean_object* v___x_5595_; 
v_head_5589_ = lean_ctor_get(v_path_5580_, 0);
lean_inc(v_head_5589_);
v_tail_5590_ = lean_ctor_get(v_path_5580_, 1);
lean_inc(v_tail_5590_);
lean_dec_ref_known(v_path_5580_, 2);
v_roots_5591_ = lean_ctor_get(v_t_5579_, 1);
v___x_5592_ = lean_unsigned_to_nat(0u);
v_idx_5593_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_roots_5591_, v_head_5589_, v___x_5592_);
lean_dec(v_head_5589_);
v___x_5594_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_extractKeyAux___boxed), 9, 3);
lean_closure_set(v___x_5594_, 0, lean_box(0));
lean_closure_set(v___x_5594_, 1, v_idx_5593_);
lean_closure_set(v___x_5594_, 2, v_tail_5590_);
v___x_5595_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_t_5579_, v___x_5594_, v_a_5581_, v_a_5582_, v_a_5583_, v_a_5584_);
return v___x_5595_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey___redArg___boxed(lean_object* v_t_5596_, lean_object* v_path_5597_, lean_object* v_a_5598_, lean_object* v_a_5599_, lean_object* v_a_5600_, lean_object* v_a_5601_, lean_object* v_a_5602_){
_start:
{
lean_object* v_res_5603_; 
v_res_5603_ = l_Lean_Meta_LazyDiscrTree_extractKey___redArg(v_t_5596_, v_path_5597_, v_a_5598_, v_a_5599_, v_a_5600_, v_a_5601_);
lean_dec(v_a_5601_);
lean_dec_ref(v_a_5600_);
lean_dec(v_a_5599_);
lean_dec_ref(v_a_5598_);
return v_res_5603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey(lean_object* v_00_u03b1_5604_, lean_object* v_t_5605_, lean_object* v_path_5606_, lean_object* v_a_5607_, lean_object* v_a_5608_, lean_object* v_a_5609_, lean_object* v_a_5610_){
_start:
{
lean_object* v___x_5612_; 
v___x_5612_ = l_Lean_Meta_LazyDiscrTree_extractKey___redArg(v_t_5605_, v_path_5606_, v_a_5607_, v_a_5608_, v_a_5609_, v_a_5610_);
return v___x_5612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey___boxed(lean_object* v_00_u03b1_5613_, lean_object* v_t_5614_, lean_object* v_path_5615_, lean_object* v_a_5616_, lean_object* v_a_5617_, lean_object* v_a_5618_, lean_object* v_a_5619_, lean_object* v_a_5620_){
_start:
{
lean_object* v_res_5621_; 
v_res_5621_ = l_Lean_Meta_LazyDiscrTree_extractKey(v_00_u03b1_5613_, v_t_5614_, v_path_5615_, v_a_5616_, v_a_5617_, v_a_5618_, v_a_5619_);
lean_dec(v_a_5619_);
lean_dec_ref(v_a_5618_);
lean_dec(v_a_5617_);
lean_dec_ref(v_a_5616_);
return v_res_5621_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(lean_object* v_as_x27_5622_, lean_object* v_b_5623_, lean_object* v___y_5624_, lean_object* v___y_5625_, lean_object* v___y_5626_, lean_object* v___y_5627_){
_start:
{
if (lean_obj_tag(v_as_x27_5622_) == 0)
{
lean_object* v___x_5629_; 
v___x_5629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5629_, 0, v_b_5623_);
return v___x_5629_;
}
else
{
lean_object* v_head_5630_; lean_object* v_tail_5631_; lean_object* v_fst_5632_; lean_object* v_snd_5633_; lean_object* v___x_5634_; 
v_head_5630_ = lean_ctor_get(v_as_x27_5622_, 0);
v_tail_5631_ = lean_ctor_get(v_as_x27_5622_, 1);
v_fst_5632_ = lean_ctor_get(v_b_5623_, 0);
lean_inc(v_fst_5632_);
v_snd_5633_ = lean_ctor_get(v_b_5623_, 1);
lean_inc(v_snd_5633_);
lean_dec_ref(v_b_5623_);
lean_inc(v_head_5630_);
v___x_5634_ = l_Lean_Meta_LazyDiscrTree_extractKey___redArg(v_snd_5633_, v_head_5630_, v___y_5624_, v___y_5625_, v___y_5626_, v___y_5627_);
if (lean_obj_tag(v___x_5634_) == 0)
{
lean_object* v_a_5635_; lean_object* v_fst_5636_; lean_object* v_snd_5637_; lean_object* v___x_5639_; uint8_t v_isShared_5640_; uint8_t v_isSharedCheck_5646_; 
v_a_5635_ = lean_ctor_get(v___x_5634_, 0);
lean_inc(v_a_5635_);
lean_dec_ref_known(v___x_5634_, 1);
v_fst_5636_ = lean_ctor_get(v_a_5635_, 0);
v_snd_5637_ = lean_ctor_get(v_a_5635_, 1);
v_isSharedCheck_5646_ = !lean_is_exclusive(v_a_5635_);
if (v_isSharedCheck_5646_ == 0)
{
v___x_5639_ = v_a_5635_;
v_isShared_5640_ = v_isSharedCheck_5646_;
goto v_resetjp_5638_;
}
else
{
lean_inc(v_snd_5637_);
lean_inc(v_fst_5636_);
lean_dec(v_a_5635_);
v___x_5639_ = lean_box(0);
v_isShared_5640_ = v_isSharedCheck_5646_;
goto v_resetjp_5638_;
}
v_resetjp_5638_:
{
lean_object* v___x_5641_; lean_object* v___x_5643_; 
v___x_5641_ = l_Array_append___redArg(v_fst_5632_, v_fst_5636_);
lean_dec(v_fst_5636_);
if (v_isShared_5640_ == 0)
{
lean_ctor_set(v___x_5639_, 0, v___x_5641_);
v___x_5643_ = v___x_5639_;
goto v_reusejp_5642_;
}
else
{
lean_object* v_reuseFailAlloc_5645_; 
v_reuseFailAlloc_5645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5645_, 0, v___x_5641_);
lean_ctor_set(v_reuseFailAlloc_5645_, 1, v_snd_5637_);
v___x_5643_ = v_reuseFailAlloc_5645_;
goto v_reusejp_5642_;
}
v_reusejp_5642_:
{
v_as_x27_5622_ = v_tail_5631_;
v_b_5623_ = v___x_5643_;
goto _start;
}
}
}
else
{
lean_dec(v_fst_5632_);
return v___x_5634_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg___boxed(lean_object* v_as_x27_5647_, lean_object* v_b_5648_, lean_object* v___y_5649_, lean_object* v___y_5650_, lean_object* v___y_5651_, lean_object* v___y_5652_, lean_object* v___y_5653_){
_start:
{
lean_object* v_res_5654_; 
v_res_5654_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(v_as_x27_5647_, v_b_5648_, v___y_5649_, v___y_5650_, v___y_5651_, v___y_5652_);
lean_dec(v___y_5652_);
lean_dec_ref(v___y_5651_);
lean_dec(v___y_5650_);
lean_dec_ref(v___y_5649_);
lean_dec(v_as_x27_5647_);
return v_res_5654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(lean_object* v_t_5655_, lean_object* v_keys_5656_, lean_object* v_a_5657_, lean_object* v_a_5658_, lean_object* v_a_5659_, lean_object* v_a_5660_){
_start:
{
lean_object* v_allExtracted_5662_; lean_object* v___x_5663_; lean_object* v___x_5664_; 
v_allExtracted_5662_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___x_5663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5663_, 0, v_allExtracted_5662_);
lean_ctor_set(v___x_5663_, 1, v_t_5655_);
v___x_5664_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(v_keys_5656_, v___x_5663_, v_a_5657_, v_a_5658_, v_a_5659_, v_a_5660_);
if (lean_obj_tag(v___x_5664_) == 0)
{
lean_object* v_a_5665_; lean_object* v___x_5667_; uint8_t v_isShared_5668_; uint8_t v_isSharedCheck_5681_; 
v_a_5665_ = lean_ctor_get(v___x_5664_, 0);
v_isSharedCheck_5681_ = !lean_is_exclusive(v___x_5664_);
if (v_isSharedCheck_5681_ == 0)
{
v___x_5667_ = v___x_5664_;
v_isShared_5668_ = v_isSharedCheck_5681_;
goto v_resetjp_5666_;
}
else
{
lean_inc(v_a_5665_);
lean_dec(v___x_5664_);
v___x_5667_ = lean_box(0);
v_isShared_5668_ = v_isSharedCheck_5681_;
goto v_resetjp_5666_;
}
v_resetjp_5666_:
{
lean_object* v_fst_5669_; lean_object* v_snd_5670_; lean_object* v___x_5672_; uint8_t v_isShared_5673_; uint8_t v_isSharedCheck_5680_; 
v_fst_5669_ = lean_ctor_get(v_a_5665_, 0);
v_snd_5670_ = lean_ctor_get(v_a_5665_, 1);
v_isSharedCheck_5680_ = !lean_is_exclusive(v_a_5665_);
if (v_isSharedCheck_5680_ == 0)
{
v___x_5672_ = v_a_5665_;
v_isShared_5673_ = v_isSharedCheck_5680_;
goto v_resetjp_5671_;
}
else
{
lean_inc(v_snd_5670_);
lean_inc(v_fst_5669_);
lean_dec(v_a_5665_);
v___x_5672_ = lean_box(0);
v_isShared_5673_ = v_isSharedCheck_5680_;
goto v_resetjp_5671_;
}
v_resetjp_5671_:
{
lean_object* v___x_5675_; 
if (v_isShared_5673_ == 0)
{
v___x_5675_ = v___x_5672_;
goto v_reusejp_5674_;
}
else
{
lean_object* v_reuseFailAlloc_5679_; 
v_reuseFailAlloc_5679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5679_, 0, v_fst_5669_);
lean_ctor_set(v_reuseFailAlloc_5679_, 1, v_snd_5670_);
v___x_5675_ = v_reuseFailAlloc_5679_;
goto v_reusejp_5674_;
}
v_reusejp_5674_:
{
lean_object* v___x_5677_; 
if (v_isShared_5668_ == 0)
{
lean_ctor_set(v___x_5667_, 0, v___x_5675_);
v___x_5677_ = v___x_5667_;
goto v_reusejp_5676_;
}
else
{
lean_object* v_reuseFailAlloc_5678_; 
v_reuseFailAlloc_5678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5678_, 0, v___x_5675_);
v___x_5677_ = v_reuseFailAlloc_5678_;
goto v_reusejp_5676_;
}
v_reusejp_5676_:
{
return v___x_5677_;
}
}
}
}
}
else
{
return v___x_5664_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys___redArg___boxed(lean_object* v_t_5682_, lean_object* v_keys_5683_, lean_object* v_a_5684_, lean_object* v_a_5685_, lean_object* v_a_5686_, lean_object* v_a_5687_, lean_object* v_a_5688_){
_start:
{
lean_object* v_res_5689_; 
v_res_5689_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_t_5682_, v_keys_5683_, v_a_5684_, v_a_5685_, v_a_5686_, v_a_5687_);
lean_dec(v_a_5687_);
lean_dec_ref(v_a_5686_);
lean_dec(v_a_5685_);
lean_dec_ref(v_a_5684_);
lean_dec(v_keys_5683_);
return v_res_5689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys(lean_object* v_00_u03b1_5690_, lean_object* v_t_5691_, lean_object* v_keys_5692_, lean_object* v_a_5693_, lean_object* v_a_5694_, lean_object* v_a_5695_, lean_object* v_a_5696_){
_start:
{
lean_object* v___x_5698_; 
v___x_5698_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_t_5691_, v_keys_5692_, v_a_5693_, v_a_5694_, v_a_5695_, v_a_5696_);
return v___x_5698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys___boxed(lean_object* v_00_u03b1_5699_, lean_object* v_t_5700_, lean_object* v_keys_5701_, lean_object* v_a_5702_, lean_object* v_a_5703_, lean_object* v_a_5704_, lean_object* v_a_5705_, lean_object* v_a_5706_){
_start:
{
lean_object* v_res_5707_; 
v_res_5707_ = l_Lean_Meta_LazyDiscrTree_extractKeys(v_00_u03b1_5699_, v_t_5700_, v_keys_5701_, v_a_5702_, v_a_5703_, v_a_5704_, v_a_5705_);
lean_dec(v_a_5705_);
lean_dec_ref(v_a_5704_);
lean_dec(v_a_5703_);
lean_dec_ref(v_a_5702_);
lean_dec(v_keys_5701_);
return v_res_5707_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0(lean_object* v_00_u03b1_5708_, lean_object* v_as_5709_, lean_object* v_as_x27_5710_, lean_object* v_b_5711_, lean_object* v_a_5712_, lean_object* v___y_5713_, lean_object* v___y_5714_, lean_object* v___y_5715_, lean_object* v___y_5716_){
_start:
{
lean_object* v___x_5718_; 
v___x_5718_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(v_as_x27_5710_, v_b_5711_, v___y_5713_, v___y_5714_, v___y_5715_, v___y_5716_);
return v___x_5718_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___boxed(lean_object* v_00_u03b1_5719_, lean_object* v_as_5720_, lean_object* v_as_x27_5721_, lean_object* v_b_5722_, lean_object* v_a_5723_, lean_object* v___y_5724_, lean_object* v___y_5725_, lean_object* v___y_5726_, lean_object* v___y_5727_, lean_object* v___y_5728_){
_start:
{
lean_object* v_res_5729_; 
v_res_5729_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0(v_00_u03b1_5719_, v_as_5720_, v_as_x27_5721_, v_b_5722_, v_a_5723_, v___y_5724_, v___y_5725_, v___y_5726_, v___y_5727_);
lean_dec(v___y_5727_);
lean_dec_ref(v___y_5726_);
lean_dec(v___y_5725_);
lean_dec_ref(v___y_5724_);
lean_dec(v_as_x27_5721_);
lean_dec(v_as_5720_);
return v_res_5729_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1(void){
_start:
{
lean_object* v___x_5731_; lean_object* v___x_5732_; 
v___x_5731_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__0));
v___x_5732_ = l_Lean_stringToMessageData(v___x_5731_);
return v___x_5732_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3(void){
_start:
{
lean_object* v___x_5734_; lean_object* v___x_5735_; 
v___x_5734_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__2));
v___x_5735_ = l_Lean_stringToMessageData(v___x_5734_);
return v___x_5735_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5(void){
_start:
{
lean_object* v___x_5737_; lean_object* v___x_5738_; 
v___x_5737_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__4));
v___x_5738_ = l_Lean_stringToMessageData(v___x_5737_);
return v___x_5738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg(lean_object* v_inst_5739_, lean_object* v_inst_5740_, lean_object* v_inst_5741_, lean_object* v_inst_5742_, lean_object* v_f_5743_){
_start:
{
lean_object* v_module_5744_; lean_object* v_const_5745_; lean_object* v_exception_5746_; lean_object* v___x_5747_; lean_object* v___x_5748_; lean_object* v___x_5749_; lean_object* v___x_5750_; lean_object* v___x_5751_; lean_object* v___x_5752_; lean_object* v___x_5753_; lean_object* v___x_5754_; lean_object* v___x_5755_; lean_object* v___x_5756_; lean_object* v___x_5757_; lean_object* v___x_5758_; 
v_module_5744_ = lean_ctor_get(v_f_5743_, 0);
lean_inc(v_module_5744_);
v_const_5745_ = lean_ctor_get(v_f_5743_, 1);
lean_inc(v_const_5745_);
v_exception_5746_ = lean_ctor_get(v_f_5743_, 2);
lean_inc_ref(v_exception_5746_);
lean_dec_ref(v_f_5743_);
v___x_5747_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1);
v___x_5748_ = l_Lean_MessageData_ofName(v_const_5745_);
v___x_5749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5749_, 0, v___x_5747_);
lean_ctor_set(v___x_5749_, 1, v___x_5748_);
v___x_5750_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3);
v___x_5751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5751_, 0, v___x_5749_);
lean_ctor_set(v___x_5751_, 1, v___x_5750_);
v___x_5752_ = l_Lean_MessageData_ofName(v_module_5744_);
v___x_5753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5753_, 0, v___x_5751_);
lean_ctor_set(v___x_5753_, 1, v___x_5752_);
v___x_5754_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5);
v___x_5755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5755_, 0, v___x_5753_);
lean_ctor_set(v___x_5755_, 1, v___x_5754_);
v___x_5756_ = l_Lean_Exception_toMessageData(v_exception_5746_);
v___x_5757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5757_, 0, v___x_5755_);
lean_ctor_set(v___x_5757_, 1, v___x_5756_);
v___x_5758_ = l_Lean_logError___redArg(v_inst_5739_, v_inst_5740_, v_inst_5741_, v_inst_5742_, v___x_5757_);
return v___x_5758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure(lean_object* v_m_5759_, lean_object* v_inst_5760_, lean_object* v_inst_5761_, lean_object* v_inst_5762_, lean_object* v_inst_5763_, lean_object* v_f_5764_){
_start:
{
lean_object* v___x_5765_; 
v___x_5765_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg(v_inst_5760_, v_inst_5761_, v_inst_5762_, v_inst_5763_, v_f_5764_);
return v___x_5765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__0(lean_object* v_tasks_5766_, lean_object* v_toPure_5767_, lean_object* v_t_5768_){
_start:
{
lean_object* v___x_5769_; lean_object* v___x_5770_; 
v___x_5769_ = lean_array_push(v_tasks_5766_, v_t_5768_);
v___x_5770_ = lean_apply_2(v_toPure_5767_, lean_box(0), v___x_5769_);
return v___x_5770_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(lean_object* v_inst_5771_, lean_object* v_inst_5772_, lean_object* v_cctx_5773_, lean_object* v_env_5774_, lean_object* v_act_5775_, lean_object* v_constantsPerTask_5776_, lean_object* v_n_5777_, lean_object* v_ngen_5778_, lean_object* v_tasks_5779_, lean_object* v_start_5780_, lean_object* v_cnt_5781_, lean_object* v_idx_5782_){
_start:
{
lean_object* v___x_5783_; lean_object* v_toApplicative_5784_; lean_object* v_moduleData_5785_; lean_object* v_toBind_5786_; lean_object* v_toPure_5787_; lean_object* v___x_5788_; uint8_t v___x_5789_; 
v___x_5783_ = l_Lean_Environment_header(v_env_5774_);
v_toApplicative_5784_ = lean_ctor_get(v_inst_5771_, 0);
v_moduleData_5785_ = lean_ctor_get(v___x_5783_, 6);
lean_inc_ref(v_moduleData_5785_);
lean_dec_ref(v___x_5783_);
v_toBind_5786_ = lean_ctor_get(v_inst_5771_, 1);
v_toPure_5787_ = lean_ctor_get(v_toApplicative_5784_, 1);
v___x_5788_ = lean_array_get_size(v_moduleData_5785_);
v___x_5789_ = lean_nat_dec_lt(v_idx_5782_, v___x_5788_);
if (v___x_5789_ == 0)
{
uint8_t v___x_5790_; 
lean_inc(v_toPure_5787_);
lean_inc(v_toBind_5786_);
lean_dec_ref(v_moduleData_5785_);
lean_dec(v_idx_5782_);
lean_dec(v_cnt_5781_);
lean_dec(v_constantsPerTask_5776_);
lean_dec_ref(v_inst_5771_);
v___x_5790_ = lean_nat_dec_lt(v_start_5780_, v_n_5777_);
if (v___x_5790_ == 0)
{
lean_object* v___x_5791_; 
lean_dec(v_toBind_5786_);
lean_dec(v_start_5780_);
lean_dec_ref(v_ngen_5778_);
lean_dec(v_n_5777_);
lean_dec_ref(v_act_5775_);
lean_dec_ref(v_env_5774_);
lean_dec_ref(v_cctx_5773_);
lean_dec(v_inst_5772_);
v___x_5791_ = lean_apply_2(v_toPure_5787_, lean_box(0), v_tasks_5779_);
return v___x_5791_;
}
else
{
lean_object* v_namePrefix_5792_; lean_object* v_idx_5793_; lean_object* v___x_5795_; uint8_t v_isShared_5796_; uint8_t v_isSharedCheck_5808_; 
v_namePrefix_5792_ = lean_ctor_get(v_ngen_5778_, 0);
v_idx_5793_ = lean_ctor_get(v_ngen_5778_, 1);
v_isSharedCheck_5808_ = !lean_is_exclusive(v_ngen_5778_);
if (v_isSharedCheck_5808_ == 0)
{
v___x_5795_ = v_ngen_5778_;
v_isShared_5796_ = v_isSharedCheck_5808_;
goto v_resetjp_5794_;
}
else
{
lean_inc(v_idx_5793_);
lean_inc(v_namePrefix_5792_);
lean_dec(v_ngen_5778_);
v___x_5795_ = lean_box(0);
v_isShared_5796_ = v_isSharedCheck_5808_;
goto v_resetjp_5794_;
}
v_resetjp_5794_:
{
lean_object* v___f_5797_; lean_object* v___x_5798_; lean_object* v___x_5799_; lean_object* v___x_5801_; 
v___f_5797_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5797_, 0, v_tasks_5779_);
lean_closure_set(v___f_5797_, 1, v_toPure_5787_);
v___x_5798_ = l_Lean_Name_num___override(v_namePrefix_5792_, v_idx_5793_);
v___x_5799_ = lean_unsigned_to_nat(1u);
if (v_isShared_5796_ == 0)
{
lean_ctor_set(v___x_5795_, 1, v___x_5799_);
lean_ctor_set(v___x_5795_, 0, v___x_5798_);
v___x_5801_ = v___x_5795_;
goto v_reusejp_5800_;
}
else
{
lean_object* v_reuseFailAlloc_5807_; 
v_reuseFailAlloc_5807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5807_, 0, v___x_5798_);
lean_ctor_set(v_reuseFailAlloc_5807_, 1, v___x_5799_);
v___x_5801_ = v_reuseFailAlloc_5807_;
goto v_reusejp_5800_;
}
v_reusejp_5800_:
{
lean_object* v___x_5802_; lean_object* v___x_5803_; lean_object* v___x_5804_; lean_object* v___x_5805_; lean_object* v___x_5806_; 
v___x_5802_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_5802_, 0, lean_box(0));
lean_closure_set(v___x_5802_, 1, v_cctx_5773_);
lean_closure_set(v___x_5802_, 2, v___x_5801_);
lean_closure_set(v___x_5802_, 3, v_env_5774_);
lean_closure_set(v___x_5802_, 4, v_act_5775_);
lean_closure_set(v___x_5802_, 5, v_start_5780_);
lean_closure_set(v___x_5802_, 6, v_n_5777_);
v___x_5803_ = lean_unsigned_to_nat(0u);
v___x_5804_ = lean_alloc_closure((void*)(l_BaseIO_asTask___boxed), 4, 3);
lean_closure_set(v___x_5804_, 0, lean_box(0));
lean_closure_set(v___x_5804_, 1, v___x_5802_);
lean_closure_set(v___x_5804_, 2, v___x_5803_);
v___x_5805_ = lean_apply_2(v_inst_5772_, lean_box(0), v___x_5804_);
v___x_5806_ = lean_apply_4(v_toBind_5786_, lean_box(0), lean_box(0), v___x_5805_, v___f_5797_);
return v___x_5806_;
}
}
}
}
else
{
lean_object* v_mdata_5809_; lean_object* v_constants_5810_; lean_object* v___x_5811_; lean_object* v_cnt_5812_; uint8_t v___x_5813_; 
v_mdata_5809_ = lean_array_fget(v_moduleData_5785_, v_idx_5782_);
lean_dec_ref(v_moduleData_5785_);
v_constants_5810_ = lean_ctor_get(v_mdata_5809_, 2);
lean_inc_ref(v_constants_5810_);
lean_dec(v_mdata_5809_);
v___x_5811_ = lean_array_get_size(v_constants_5810_);
lean_dec_ref(v_constants_5810_);
v_cnt_5812_ = lean_nat_add(v_cnt_5781_, v___x_5811_);
lean_dec(v_cnt_5781_);
v___x_5813_ = lean_nat_dec_lt(v_constantsPerTask_5776_, v_cnt_5812_);
if (v___x_5813_ == 0)
{
lean_object* v___x_5814_; lean_object* v___x_5815_; 
v___x_5814_ = lean_unsigned_to_nat(1u);
v___x_5815_ = lean_nat_add(v_idx_5782_, v___x_5814_);
lean_dec(v_idx_5782_);
v_cnt_5781_ = v_cnt_5812_;
v_idx_5782_ = v___x_5815_;
goto _start;
}
else
{
lean_object* v_namePrefix_5817_; lean_object* v_idx_5818_; lean_object* v___x_5820_; uint8_t v_isShared_5821_; uint8_t v_isSharedCheck_5836_; 
lean_inc(v_toBind_5786_);
lean_dec(v_cnt_5812_);
v_namePrefix_5817_ = lean_ctor_get(v_ngen_5778_, 0);
v_idx_5818_ = lean_ctor_get(v_ngen_5778_, 1);
v_isSharedCheck_5836_ = !lean_is_exclusive(v_ngen_5778_);
if (v_isSharedCheck_5836_ == 0)
{
v___x_5820_ = v_ngen_5778_;
v_isShared_5821_ = v_isSharedCheck_5836_;
goto v_resetjp_5819_;
}
else
{
lean_inc(v_idx_5818_);
lean_inc(v_namePrefix_5817_);
lean_dec(v_ngen_5778_);
v___x_5820_ = lean_box(0);
v_isShared_5821_ = v_isSharedCheck_5836_;
goto v_resetjp_5819_;
}
v_resetjp_5819_:
{
lean_object* v___x_5822_; lean_object* v___x_5823_; lean_object* v___x_5825_; 
lean_inc(v_idx_5818_);
lean_inc(v_namePrefix_5817_);
v___x_5822_ = l_Lean_Name_num___override(v_namePrefix_5817_, v_idx_5818_);
v___x_5823_ = lean_unsigned_to_nat(1u);
if (v_isShared_5821_ == 0)
{
lean_ctor_set(v___x_5820_, 1, v___x_5823_);
lean_ctor_set(v___x_5820_, 0, v___x_5822_);
v___x_5825_ = v___x_5820_;
goto v_reusejp_5824_;
}
else
{
lean_object* v_reuseFailAlloc_5835_; 
v_reuseFailAlloc_5835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5835_, 0, v___x_5822_);
lean_ctor_set(v_reuseFailAlloc_5835_, 1, v___x_5823_);
v___x_5825_ = v_reuseFailAlloc_5835_;
goto v_reusejp_5824_;
}
v_reusejp_5824_:
{
lean_object* v___x_5826_; lean_object* v___x_5827_; lean_object* v___x_5828_; lean_object* v___f_5829_; lean_object* v___x_5830_; lean_object* v___x_5831_; lean_object* v___x_5832_; lean_object* v___x_5833_; lean_object* v___x_5834_; 
v___x_5826_ = lean_nat_add(v_idx_5818_, v___x_5823_);
lean_dec(v_idx_5818_);
v___x_5827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5827_, 0, v_namePrefix_5817_);
lean_ctor_set(v___x_5827_, 1, v___x_5826_);
v___x_5828_ = lean_nat_add(v_idx_5782_, v___x_5823_);
lean_dec(v_idx_5782_);
lean_inc(v___x_5828_);
lean_inc_ref(v_act_5775_);
lean_inc_ref(v_env_5774_);
lean_inc_ref(v_cctx_5773_);
lean_inc(v_inst_5772_);
v___f_5829_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__1), 11, 10);
lean_closure_set(v___f_5829_, 0, v_tasks_5779_);
lean_closure_set(v___f_5829_, 1, v_inst_5771_);
lean_closure_set(v___f_5829_, 2, v_inst_5772_);
lean_closure_set(v___f_5829_, 3, v_cctx_5773_);
lean_closure_set(v___f_5829_, 4, v_env_5774_);
lean_closure_set(v___f_5829_, 5, v_act_5775_);
lean_closure_set(v___f_5829_, 6, v_constantsPerTask_5776_);
lean_closure_set(v___f_5829_, 7, v_n_5777_);
lean_closure_set(v___f_5829_, 8, v___x_5827_);
lean_closure_set(v___f_5829_, 9, v___x_5828_);
v___x_5830_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_5830_, 0, lean_box(0));
lean_closure_set(v___x_5830_, 1, v_cctx_5773_);
lean_closure_set(v___x_5830_, 2, v___x_5825_);
lean_closure_set(v___x_5830_, 3, v_env_5774_);
lean_closure_set(v___x_5830_, 4, v_act_5775_);
lean_closure_set(v___x_5830_, 5, v_start_5780_);
lean_closure_set(v___x_5830_, 6, v___x_5828_);
v___x_5831_ = lean_unsigned_to_nat(0u);
v___x_5832_ = lean_alloc_closure((void*)(l_BaseIO_asTask___boxed), 4, 3);
lean_closure_set(v___x_5832_, 0, lean_box(0));
lean_closure_set(v___x_5832_, 1, v___x_5830_);
lean_closure_set(v___x_5832_, 2, v___x_5831_);
v___x_5833_ = lean_apply_2(v_inst_5772_, lean_box(0), v___x_5832_);
v___x_5834_ = lean_apply_4(v_toBind_5786_, lean_box(0), lean_box(0), v___x_5833_, v___f_5829_);
return v___x_5834_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__1(lean_object* v_tasks_5837_, lean_object* v_inst_5838_, lean_object* v_inst_5839_, lean_object* v_cctx_5840_, lean_object* v_env_5841_, lean_object* v_act_5842_, lean_object* v_constantsPerTask_5843_, lean_object* v_n_5844_, lean_object* v___x_5845_, lean_object* v___x_5846_, lean_object* v_t_5847_){
_start:
{
lean_object* v___x_5848_; lean_object* v___x_5849_; lean_object* v___x_5850_; 
v___x_5848_ = lean_array_push(v_tasks_5837_, v_t_5847_);
v___x_5849_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_5846_);
v___x_5850_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(v_inst_5838_, v_inst_5839_, v_cctx_5840_, v_env_5841_, v_act_5842_, v_constantsPerTask_5843_, v_n_5844_, v___x_5845_, v___x_5848_, v___x_5846_, v___x_5849_, v___x_5846_);
return v___x_5850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go(lean_object* v_m_5851_, lean_object* v_00_u03b1_5852_, lean_object* v_inst_5853_, lean_object* v_inst_5854_, lean_object* v_cctx_5855_, lean_object* v_env_5856_, lean_object* v_act_5857_, lean_object* v_constantsPerTask_5858_, lean_object* v_n_5859_, lean_object* v_ngen_5860_, lean_object* v_tasks_5861_, lean_object* v_start_5862_, lean_object* v_cnt_5863_, lean_object* v_idx_5864_){
_start:
{
lean_object* v___x_5865_; 
v___x_5865_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(v_inst_5853_, v_inst_5854_, v_cctx_5855_, v_env_5856_, v_act_5857_, v_constantsPerTask_5858_, v_n_5859_, v_ngen_5860_, v_tasks_5861_, v_start_5862_, v_cnt_5863_, v_idx_5864_);
return v___x_5865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_getChildNgen_match__1_splitter___redArg(lean_object* v_x_5866_, lean_object* v_h__1_5867_){
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_getChildNgen_match__1_splitter(lean_object* v_motive_5871_, lean_object* v_x_5872_, lean_object* v_h__1_5873_){
_start:
{
lean_object* v_fst_5874_; lean_object* v_snd_5875_; lean_object* v___x_5876_; 
v_fst_5874_ = lean_ctor_get(v_x_5872_, 0);
lean_inc(v_fst_5874_);
v_snd_5875_ = lean_ctor_get(v_x_5872_, 1);
lean_inc(v_snd_5875_);
lean_dec_ref(v_x_5872_);
v___x_5876_ = lean_apply_2(v_h__1_5873_, v_fst_5874_, v_snd_5875_);
return v___x_5876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__0(lean_object* v_inst_5877_, lean_object* v_inst_5878_, lean_object* v_inst_5879_, lean_object* v_inst_5880_, lean_object* v_x_5881_, lean_object* v___y_5882_){
_start:
{
lean_object* v___x_5883_; 
v___x_5883_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg(v_inst_5877_, v_inst_5878_, v_inst_5879_, v_inst_5880_, v___y_5882_);
return v___x_5883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__1(lean_object* v_r_5884_, lean_object* v_toPure_5885_, lean_object* v_____r_5886_){
_start:
{
lean_object* v_tree_5887_; lean_object* v___x_5888_; lean_object* v___x_5889_; 
v_tree_5887_ = lean_ctor_get(v_r_5884_, 0);
lean_inc_ref(v_tree_5887_);
lean_dec(v_r_5884_);
v___x_5888_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_tree_5887_);
v___x_5889_ = lean_apply_2(v_toPure_5885_, lean_box(0), v___x_5888_);
return v___x_5889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__2(lean_object* v___x_5890_, lean_object* v___x_5891_, lean_object* v_toPure_5892_, lean_object* v_toBind_5893_, lean_object* v_inst_5894_, lean_object* v___f_5895_, lean_object* v_tasks_5896_){
_start:
{
lean_object* v___x_5897_; lean_object* v___x_5898_; lean_object* v___x_5899_; lean_object* v___x_5900_; lean_object* v___x_5901_; lean_object* v_r_5902_; lean_object* v_errors_5903_; lean_object* v___f_5904_; lean_object* v___x_5905_; lean_object* v___x_5906_; uint8_t v___x_5907_; 
v___x_5897_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__1);
lean_inc(v___x_5890_);
v___x_5898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5898_, 0, v___x_5890_);
lean_ctor_set(v___x_5898_, 1, v___x_5897_);
v___x_5899_ = lean_mk_empty_array_with_capacity(v___x_5890_);
lean_inc_ref(v___x_5899_);
v___x_5900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5900_, 0, v___x_5898_);
lean_ctor_set(v___x_5900_, 1, v___x_5899_);
v___x_5901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5901_, 0, v___x_5900_);
lean_ctor_set(v___x_5901_, 1, v___x_5899_);
v_r_5902_ = l_Lean_Meta_LazyDiscrTree_combineGet___redArg(v___x_5891_, v___x_5901_, v_tasks_5896_);
v_errors_5903_ = lean_ctor_get(v_r_5902_, 1);
lean_inc_ref(v_errors_5903_);
lean_inc(v_toPure_5892_);
v___f_5904_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__1), 3, 2);
lean_closure_set(v___f_5904_, 0, v_r_5902_);
lean_closure_set(v___f_5904_, 1, v_toPure_5892_);
v___x_5905_ = lean_array_get_size(v_errors_5903_);
v___x_5906_ = lean_box(0);
v___x_5907_ = lean_nat_dec_lt(v___x_5890_, v___x_5905_);
lean_dec(v___x_5890_);
if (v___x_5907_ == 0)
{
lean_object* v___x_5908_; lean_object* v___x_5909_; 
lean_dec_ref(v_errors_5903_);
lean_dec(v___f_5895_);
lean_dec_ref(v_inst_5894_);
v___x_5908_ = lean_apply_2(v_toPure_5892_, lean_box(0), v___x_5906_);
v___x_5909_ = lean_apply_4(v_toBind_5893_, lean_box(0), lean_box(0), v___x_5908_, v___f_5904_);
return v___x_5909_;
}
else
{
uint8_t v___x_5910_; 
v___x_5910_ = lean_nat_dec_le(v___x_5905_, v___x_5905_);
if (v___x_5910_ == 0)
{
if (v___x_5907_ == 0)
{
lean_object* v___x_5911_; lean_object* v___x_5912_; 
lean_dec_ref(v_errors_5903_);
lean_dec(v___f_5895_);
lean_dec_ref(v_inst_5894_);
v___x_5911_ = lean_apply_2(v_toPure_5892_, lean_box(0), v___x_5906_);
v___x_5912_ = lean_apply_4(v_toBind_5893_, lean_box(0), lean_box(0), v___x_5911_, v___f_5904_);
return v___x_5912_;
}
else
{
size_t v___x_5913_; size_t v___x_5914_; lean_object* v___x_5915_; lean_object* v___x_5916_; 
lean_dec(v_toPure_5892_);
v___x_5913_ = ((size_t)0ULL);
v___x_5914_ = lean_usize_of_nat(v___x_5905_);
v___x_5915_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_5894_, v___f_5895_, v_errors_5903_, v___x_5913_, v___x_5914_, v___x_5906_);
v___x_5916_ = lean_apply_4(v_toBind_5893_, lean_box(0), lean_box(0), v___x_5915_, v___f_5904_);
return v___x_5916_;
}
}
else
{
size_t v___x_5917_; size_t v___x_5918_; lean_object* v___x_5919_; lean_object* v___x_5920_; 
lean_dec(v_toPure_5892_);
v___x_5917_ = ((size_t)0ULL);
v___x_5918_ = lean_usize_of_nat(v___x_5905_);
v___x_5919_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_5894_, v___f_5895_, v_errors_5903_, v___x_5917_, v___x_5918_, v___x_5906_);
v___x_5920_ = lean_apply_4(v_toBind_5893_, lean_box(0), lean_box(0), v___x_5919_, v___f_5904_);
return v___x_5920_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg(lean_object* v_inst_5923_, lean_object* v_inst_5924_, lean_object* v_inst_5925_, lean_object* v_inst_5926_, lean_object* v_inst_5927_, lean_object* v_cctx_5928_, lean_object* v_ngen_5929_, lean_object* v_env_5930_, lean_object* v_act_5931_, lean_object* v_constantsPerTask_5932_){
_start:
{
lean_object* v___x_5933_; lean_object* v_moduleData_5934_; lean_object* v_toApplicative_5935_; lean_object* v_toBind_5936_; lean_object* v_n_5937_; lean_object* v___x_5938_; lean_object* v___x_5939_; lean_object* v___x_5940_; lean_object* v_toPure_5941_; lean_object* v___f_5942_; lean_object* v___x_5943_; lean_object* v___f_5944_; lean_object* v___x_5945_; 
v___x_5933_ = l_Lean_Environment_header(v_env_5930_);
v_moduleData_5934_ = lean_ctor_get(v___x_5933_, 6);
lean_inc_ref(v_moduleData_5934_);
lean_dec_ref(v___x_5933_);
v_toApplicative_5935_ = lean_ctor_get(v_inst_5923_, 0);
v_toBind_5936_ = lean_ctor_get(v_inst_5923_, 1);
lean_inc_n(v_toBind_5936_, 2);
v_n_5937_ = lean_array_get_size(v_moduleData_5934_);
lean_dec_ref(v_moduleData_5934_);
v___x_5938_ = lean_unsigned_to_nat(0u);
v___x_5939_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
lean_inc_ref_n(v_inst_5923_, 2);
v___x_5940_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(v_inst_5923_, v_inst_5927_, v_cctx_5928_, v_env_5930_, v_act_5931_, v_constantsPerTask_5932_, v_n_5937_, v_ngen_5929_, v___x_5939_, v___x_5938_, v___x_5938_, v___x_5938_);
v_toPure_5941_ = lean_ctor_get(v_toApplicative_5935_, 1);
lean_inc(v_toPure_5941_);
v___f_5942_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__0), 6, 4);
lean_closure_set(v___f_5942_, 0, v_inst_5923_);
lean_closure_set(v___f_5942_, 1, v_inst_5924_);
lean_closure_set(v___f_5942_, 2, v_inst_5925_);
lean_closure_set(v___f_5942_, 3, v_inst_5926_);
v___x_5943_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___redArg___closed__0));
v___f_5944_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__2), 7, 6);
lean_closure_set(v___f_5944_, 0, v___x_5938_);
lean_closure_set(v___f_5944_, 1, v___x_5943_);
lean_closure_set(v___f_5944_, 2, v_toPure_5941_);
lean_closure_set(v___f_5944_, 3, v_toBind_5936_);
lean_closure_set(v___f_5944_, 4, v_inst_5923_);
lean_closure_set(v___f_5944_, 5, v___f_5942_);
v___x_5945_ = lean_apply_4(v_toBind_5936_, lean_box(0), lean_box(0), v___x_5940_, v___f_5944_);
return v___x_5945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree(lean_object* v_m_5946_, lean_object* v_00_u03b1_5947_, lean_object* v_inst_5948_, lean_object* v_inst_5949_, lean_object* v_inst_5950_, lean_object* v_inst_5951_, lean_object* v_inst_5952_, lean_object* v_cctx_5953_, lean_object* v_ngen_5954_, lean_object* v_env_5955_, lean_object* v_act_5956_, lean_object* v_constantsPerTask_5957_){
_start:
{
lean_object* v___x_5958_; 
v___x_5958_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg(v_inst_5948_, v_inst_5949_, v_inst_5950_, v_inst_5951_, v_inst_5952_, v_cctx_5953_, v_ngen_5954_, v_env_5955_, v_act_5956_, v_constantsPerTask_5957_);
return v___x_5958_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0(void){
_start:
{
lean_object* v___x_5959_; lean_object* v___x_5960_; lean_object* v___x_5961_; 
v___x_5959_ = lean_box(0);
v___x_5960_ = lean_unsigned_to_nat(16u);
v___x_5961_ = lean_mk_array(v___x_5960_, v___x_5959_);
return v___x_5961_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1(void){
_start:
{
lean_object* v___x_5962_; lean_object* v___x_5963_; lean_object* v___x_5964_; 
v___x_5962_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0, &l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0);
v___x_5963_ = lean_unsigned_to_nat(0u);
v___x_5964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5964_, 0, v___x_5963_);
lean_ctor_set(v___x_5964_, 1, v___x_5962_);
return v___x_5964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createTreeCtx(lean_object* v_ctx_5965_){
_start:
{
lean_object* v_toCold_5966_; lean_object* v_ref_5967_; lean_object* v___x_5969_; uint8_t v_isShared_5970_; uint8_t v_isSharedCheck_6001_; 
v_toCold_5966_ = lean_ctor_get(v_ctx_5965_, 0);
v_ref_5967_ = lean_ctor_get(v_ctx_5965_, 2);
v_isSharedCheck_6001_ = !lean_is_exclusive(v_ctx_5965_);
if (v_isSharedCheck_6001_ == 0)
{
lean_object* v_unused_6002_; 
v_unused_6002_ = lean_ctor_get(v_ctx_5965_, 1);
lean_dec(v_unused_6002_);
v___x_5969_ = v_ctx_5965_;
v_isShared_5970_ = v_isSharedCheck_6001_;
goto v_resetjp_5968_;
}
else
{
lean_inc(v_ref_5967_);
lean_inc(v_toCold_5966_);
lean_dec(v_ctx_5965_);
v___x_5969_ = lean_box(0);
v_isShared_5970_ = v_isSharedCheck_6001_;
goto v_resetjp_5968_;
}
v_resetjp_5968_:
{
lean_object* v_fileName_5971_; lean_object* v_fileMap_5972_; lean_object* v_options_5973_; lean_object* v_maxRecDepth_5974_; lean_object* v___x_5976_; uint8_t v_isShared_5977_; uint8_t v_isSharedCheck_5992_; 
v_fileName_5971_ = lean_ctor_get(v_toCold_5966_, 0);
v_fileMap_5972_ = lean_ctor_get(v_toCold_5966_, 1);
v_options_5973_ = lean_ctor_get(v_toCold_5966_, 2);
v_maxRecDepth_5974_ = lean_ctor_get(v_toCold_5966_, 3);
v_isSharedCheck_5992_ = !lean_is_exclusive(v_toCold_5966_);
if (v_isSharedCheck_5992_ == 0)
{
lean_object* v_unused_5993_; lean_object* v_unused_5994_; lean_object* v_unused_5995_; lean_object* v_unused_5996_; lean_object* v_unused_5997_; lean_object* v_unused_5998_; lean_object* v_unused_5999_; lean_object* v_unused_6000_; 
v_unused_5993_ = lean_ctor_get(v_toCold_5966_, 11);
lean_dec(v_unused_5993_);
v_unused_5994_ = lean_ctor_get(v_toCold_5966_, 10);
lean_dec(v_unused_5994_);
v_unused_5995_ = lean_ctor_get(v_toCold_5966_, 9);
lean_dec(v_unused_5995_);
v_unused_5996_ = lean_ctor_get(v_toCold_5966_, 8);
lean_dec(v_unused_5996_);
v_unused_5997_ = lean_ctor_get(v_toCold_5966_, 7);
lean_dec(v_unused_5997_);
v_unused_5998_ = lean_ctor_get(v_toCold_5966_, 6);
lean_dec(v_unused_5998_);
v_unused_5999_ = lean_ctor_get(v_toCold_5966_, 5);
lean_dec(v_unused_5999_);
v_unused_6000_ = lean_ctor_get(v_toCold_5966_, 4);
lean_dec(v_unused_6000_);
v___x_5976_ = v_toCold_5966_;
v_isShared_5977_ = v_isSharedCheck_5992_;
goto v_resetjp_5975_;
}
else
{
lean_inc(v_maxRecDepth_5974_);
lean_inc(v_options_5973_);
lean_inc(v_fileMap_5972_);
lean_inc(v_fileName_5971_);
lean_dec(v_toCold_5966_);
v___x_5976_ = lean_box(0);
v_isShared_5977_ = v_isSharedCheck_5992_;
goto v_resetjp_5975_;
}
v_resetjp_5975_:
{
lean_object* v___x_5978_; lean_object* v___x_5979_; lean_object* v___x_5980_; lean_object* v___x_5981_; lean_object* v___x_5982_; lean_object* v___x_5983_; lean_object* v___x_5985_; 
v___x_5978_ = lean_box(0);
v___x_5979_ = lean_box(0);
v___x_5980_ = lean_unsigned_to_nat(0u);
v___x_5981_ = l_Lean_firstFrontendMacroScope;
v___x_5982_ = lean_box(0);
v___x_5983_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1, &l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1);
lean_inc_ref(v_options_5973_);
if (v_isShared_5977_ == 0)
{
lean_ctor_set(v___x_5976_, 11, v___x_5983_);
lean_ctor_set(v___x_5976_, 10, v___x_5982_);
lean_ctor_set(v___x_5976_, 9, v___x_5981_);
lean_ctor_set(v___x_5976_, 8, v___x_5978_);
lean_ctor_set(v___x_5976_, 7, v___x_5980_);
lean_ctor_set(v___x_5976_, 6, v___x_5980_);
lean_ctor_set(v___x_5976_, 5, v___x_5979_);
lean_ctor_set(v___x_5976_, 4, v___x_5978_);
v___x_5985_ = v___x_5976_;
goto v_reusejp_5984_;
}
else
{
lean_object* v_reuseFailAlloc_5991_; 
v_reuseFailAlloc_5991_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_5991_, 0, v_fileName_5971_);
lean_ctor_set(v_reuseFailAlloc_5991_, 1, v_fileMap_5972_);
lean_ctor_set(v_reuseFailAlloc_5991_, 2, v_options_5973_);
lean_ctor_set(v_reuseFailAlloc_5991_, 3, v_maxRecDepth_5974_);
lean_ctor_set(v_reuseFailAlloc_5991_, 4, v___x_5978_);
lean_ctor_set(v_reuseFailAlloc_5991_, 5, v___x_5979_);
lean_ctor_set(v_reuseFailAlloc_5991_, 6, v___x_5980_);
lean_ctor_set(v_reuseFailAlloc_5991_, 7, v___x_5980_);
lean_ctor_set(v_reuseFailAlloc_5991_, 8, v___x_5978_);
lean_ctor_set(v_reuseFailAlloc_5991_, 9, v___x_5981_);
lean_ctor_set(v_reuseFailAlloc_5991_, 10, v___x_5982_);
lean_ctor_set(v_reuseFailAlloc_5991_, 11, v___x_5983_);
v___x_5985_ = v_reuseFailAlloc_5991_;
goto v_reusejp_5984_;
}
v_reusejp_5984_:
{
uint16_t v___x_5986_; uint8_t v___x_5987_; lean_object* v___x_5989_; 
v___x_5986_ = l_Lean_OptionFlags_ofOptions(v_options_5973_);
lean_dec_ref(v_options_5973_);
v___x_5987_ = 0;
if (v_isShared_5970_ == 0)
{
lean_ctor_set(v___x_5969_, 1, v___x_5980_);
lean_ctor_set(v___x_5969_, 0, v___x_5985_);
v___x_5989_ = v___x_5969_;
goto v_reusejp_5988_;
}
else
{
lean_object* v_reuseFailAlloc_5990_; 
v_reuseFailAlloc_5990_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v_reuseFailAlloc_5990_, 0, v___x_5985_);
lean_ctor_set(v_reuseFailAlloc_5990_, 1, v___x_5980_);
lean_ctor_set(v_reuseFailAlloc_5990_, 2, v_ref_5967_);
v___x_5989_ = v_reuseFailAlloc_5990_;
goto v_reusejp_5988_;
}
v_reusejp_5988_:
{
lean_ctor_set_uint16(v___x_5989_, sizeof(void*)*3, v___x_5986_);
lean_ctor_set_uint8(v___x_5989_, sizeof(void*)*3 + 2, v___x_5987_);
lean_ctor_set_uint8(v___x_5989_, sizeof(void*)*3 + 3, v___x_5987_);
return v___x_5989_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(lean_object* v_category_6003_, lean_object* v_opts_6004_, lean_object* v_act_6005_, lean_object* v_decl_6006_, lean_object* v___y_6007_, lean_object* v___y_6008_, lean_object* v___y_6009_, lean_object* v___y_6010_){
_start:
{
lean_object* v___x_6012_; lean_object* v___x_6013_; 
lean_inc(v___y_6010_);
lean_inc_ref(v___y_6009_);
lean_inc(v___y_6008_);
lean_inc_ref(v___y_6007_);
v___x_6012_ = lean_apply_4(v_act_6005_, v___y_6007_, v___y_6008_, v___y_6009_, v___y_6010_);
v___x_6013_ = l_Lean_profileitIOUnsafe___redArg(v_category_6003_, v_opts_6004_, v___x_6012_, v_decl_6006_);
return v___x_6013_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg___boxed(lean_object* v_category_6014_, lean_object* v_opts_6015_, lean_object* v_act_6016_, lean_object* v_decl_6017_, lean_object* v___y_6018_, lean_object* v___y_6019_, lean_object* v___y_6020_, lean_object* v___y_6021_, lean_object* v___y_6022_){
_start:
{
lean_object* v_res_6023_; 
v_res_6023_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v_category_6014_, v_opts_6015_, v_act_6016_, v_decl_6017_, v___y_6018_, v___y_6019_, v___y_6020_, v___y_6021_);
lean_dec(v___y_6021_);
lean_dec_ref(v___y_6020_);
lean_dec(v___y_6019_);
lean_dec_ref(v___y_6018_);
lean_dec_ref(v_opts_6015_);
lean_dec_ref(v_category_6014_);
return v_res_6023_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1(lean_object* v_00_u03b1_6024_, lean_object* v_category_6025_, lean_object* v_opts_6026_, lean_object* v_act_6027_, lean_object* v_decl_6028_, lean_object* v___y_6029_, lean_object* v___y_6030_, lean_object* v___y_6031_, lean_object* v___y_6032_){
_start:
{
lean_object* v___x_6034_; 
v___x_6034_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v_category_6025_, v_opts_6026_, v_act_6027_, v_decl_6028_, v___y_6029_, v___y_6030_, v___y_6031_, v___y_6032_);
return v___x_6034_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___boxed(lean_object* v_00_u03b1_6035_, lean_object* v_category_6036_, lean_object* v_opts_6037_, lean_object* v_act_6038_, lean_object* v_decl_6039_, lean_object* v___y_6040_, lean_object* v___y_6041_, lean_object* v___y_6042_, lean_object* v___y_6043_, lean_object* v___y_6044_){
_start:
{
lean_object* v_res_6045_; 
v_res_6045_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1(v_00_u03b1_6035_, v_category_6036_, v_opts_6037_, v_act_6038_, v_decl_6039_, v___y_6040_, v___y_6041_, v___y_6042_, v___y_6043_);
lean_dec(v___y_6043_);
lean_dec_ref(v___y_6042_);
lean_dec(v___y_6041_);
lean_dec_ref(v___y_6040_);
lean_dec_ref(v_opts_6037_);
lean_dec_ref(v_category_6036_);
return v_res_6045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(lean_object* v_cctx_6046_, lean_object* v_env_6047_, lean_object* v_act_6048_, lean_object* v_constantsPerTask_6049_, lean_object* v_n_6050_, lean_object* v_ngen_6051_, lean_object* v_tasks_6052_, lean_object* v_start_6053_, lean_object* v_cnt_6054_, lean_object* v_idx_6055_){
_start:
{
lean_object* v___x_6057_; lean_object* v_moduleData_6058_; lean_object* v___x_6059_; uint8_t v___x_6060_; 
v___x_6057_ = l_Lean_Environment_header(v_env_6047_);
v_moduleData_6058_ = lean_ctor_get(v___x_6057_, 6);
lean_inc_ref(v_moduleData_6058_);
lean_dec_ref(v___x_6057_);
v___x_6059_ = lean_array_get_size(v_moduleData_6058_);
v___x_6060_ = lean_nat_dec_lt(v_idx_6055_, v___x_6059_);
if (v___x_6060_ == 0)
{
uint8_t v___x_6061_; 
lean_dec_ref(v_moduleData_6058_);
lean_dec(v_idx_6055_);
lean_dec(v_cnt_6054_);
v___x_6061_ = lean_nat_dec_lt(v_start_6053_, v_n_6050_);
if (v___x_6061_ == 0)
{
lean_object* v___x_6062_; 
lean_dec(v_start_6053_);
lean_dec_ref(v_ngen_6051_);
lean_dec(v_n_6050_);
lean_dec_ref(v_act_6048_);
lean_dec_ref(v_env_6047_);
lean_dec_ref(v_cctx_6046_);
v___x_6062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6062_, 0, v_tasks_6052_);
return v___x_6062_;
}
else
{
lean_object* v_namePrefix_6063_; lean_object* v_idx_6064_; lean_object* v___x_6066_; uint8_t v_isShared_6067_; uint8_t v_isSharedCheck_6078_; 
v_namePrefix_6063_ = lean_ctor_get(v_ngen_6051_, 0);
v_idx_6064_ = lean_ctor_get(v_ngen_6051_, 1);
v_isSharedCheck_6078_ = !lean_is_exclusive(v_ngen_6051_);
if (v_isSharedCheck_6078_ == 0)
{
v___x_6066_ = v_ngen_6051_;
v_isShared_6067_ = v_isSharedCheck_6078_;
goto v_resetjp_6065_;
}
else
{
lean_inc(v_idx_6064_);
lean_inc(v_namePrefix_6063_);
lean_dec(v_ngen_6051_);
v___x_6066_ = lean_box(0);
v_isShared_6067_ = v_isSharedCheck_6078_;
goto v_resetjp_6065_;
}
v_resetjp_6065_:
{
lean_object* v___x_6068_; lean_object* v___x_6069_; lean_object* v___x_6071_; 
v___x_6068_ = l_Lean_Name_num___override(v_namePrefix_6063_, v_idx_6064_);
v___x_6069_ = lean_unsigned_to_nat(1u);
if (v_isShared_6067_ == 0)
{
lean_ctor_set(v___x_6066_, 1, v___x_6069_);
lean_ctor_set(v___x_6066_, 0, v___x_6068_);
v___x_6071_ = v___x_6066_;
goto v_reusejp_6070_;
}
else
{
lean_object* v_reuseFailAlloc_6077_; 
v_reuseFailAlloc_6077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6077_, 0, v___x_6068_);
lean_ctor_set(v_reuseFailAlloc_6077_, 1, v___x_6069_);
v___x_6071_ = v_reuseFailAlloc_6077_;
goto v_reusejp_6070_;
}
v_reusejp_6070_:
{
lean_object* v___x_6072_; lean_object* v___x_6073_; lean_object* v___x_6074_; lean_object* v___x_6075_; lean_object* v___x_6076_; 
v___x_6072_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_6072_, 0, lean_box(0));
lean_closure_set(v___x_6072_, 1, v_cctx_6046_);
lean_closure_set(v___x_6072_, 2, v___x_6071_);
lean_closure_set(v___x_6072_, 3, v_env_6047_);
lean_closure_set(v___x_6072_, 4, v_act_6048_);
lean_closure_set(v___x_6072_, 5, v_start_6053_);
lean_closure_set(v___x_6072_, 6, v_n_6050_);
v___x_6073_ = lean_unsigned_to_nat(0u);
v___x_6074_ = lean_io_as_task(v___x_6072_, v___x_6073_);
v___x_6075_ = lean_array_push(v_tasks_6052_, v___x_6074_);
v___x_6076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6076_, 0, v___x_6075_);
return v___x_6076_;
}
}
}
}
else
{
lean_object* v_mdata_6079_; lean_object* v_constants_6080_; lean_object* v___x_6081_; lean_object* v_cnt_6082_; uint8_t v___x_6083_; 
v_mdata_6079_ = lean_array_fget(v_moduleData_6058_, v_idx_6055_);
lean_dec_ref(v_moduleData_6058_);
v_constants_6080_ = lean_ctor_get(v_mdata_6079_, 2);
lean_inc_ref(v_constants_6080_);
lean_dec(v_mdata_6079_);
v___x_6081_ = lean_array_get_size(v_constants_6080_);
lean_dec_ref(v_constants_6080_);
v_cnt_6082_ = lean_nat_add(v_cnt_6054_, v___x_6081_);
lean_dec(v_cnt_6054_);
v___x_6083_ = lean_nat_dec_lt(v_constantsPerTask_6049_, v_cnt_6082_);
if (v___x_6083_ == 0)
{
lean_object* v___x_6084_; lean_object* v___x_6085_; 
v___x_6084_ = lean_unsigned_to_nat(1u);
v___x_6085_ = lean_nat_add(v_idx_6055_, v___x_6084_);
lean_dec(v_idx_6055_);
v_cnt_6054_ = v_cnt_6082_;
v_idx_6055_ = v___x_6085_;
goto _start;
}
else
{
lean_object* v_namePrefix_6087_; lean_object* v_idx_6088_; lean_object* v___x_6090_; uint8_t v_isShared_6091_; uint8_t v_isSharedCheck_6105_; 
lean_dec(v_cnt_6082_);
v_namePrefix_6087_ = lean_ctor_get(v_ngen_6051_, 0);
v_idx_6088_ = lean_ctor_get(v_ngen_6051_, 1);
v_isSharedCheck_6105_ = !lean_is_exclusive(v_ngen_6051_);
if (v_isSharedCheck_6105_ == 0)
{
v___x_6090_ = v_ngen_6051_;
v_isShared_6091_ = v_isSharedCheck_6105_;
goto v_resetjp_6089_;
}
else
{
lean_inc(v_idx_6088_);
lean_inc(v_namePrefix_6087_);
lean_dec(v_ngen_6051_);
v___x_6090_ = lean_box(0);
v_isShared_6091_ = v_isSharedCheck_6105_;
goto v_resetjp_6089_;
}
v_resetjp_6089_:
{
lean_object* v___x_6092_; lean_object* v___x_6093_; lean_object* v___x_6095_; 
lean_inc(v_idx_6088_);
lean_inc(v_namePrefix_6087_);
v___x_6092_ = l_Lean_Name_num___override(v_namePrefix_6087_, v_idx_6088_);
v___x_6093_ = lean_unsigned_to_nat(1u);
if (v_isShared_6091_ == 0)
{
lean_ctor_set(v___x_6090_, 1, v___x_6093_);
lean_ctor_set(v___x_6090_, 0, v___x_6092_);
v___x_6095_ = v___x_6090_;
goto v_reusejp_6094_;
}
else
{
lean_object* v_reuseFailAlloc_6104_; 
v_reuseFailAlloc_6104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6104_, 0, v___x_6092_);
lean_ctor_set(v_reuseFailAlloc_6104_, 1, v___x_6093_);
v___x_6095_ = v_reuseFailAlloc_6104_;
goto v_reusejp_6094_;
}
v_reusejp_6094_:
{
lean_object* v___x_6096_; lean_object* v___x_6097_; lean_object* v___x_6098_; lean_object* v___x_6099_; lean_object* v___x_6100_; lean_object* v___x_6101_; lean_object* v___x_6102_; 
v___x_6096_ = lean_nat_add(v_idx_6088_, v___x_6093_);
lean_dec(v_idx_6088_);
v___x_6097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6097_, 0, v_namePrefix_6087_);
lean_ctor_set(v___x_6097_, 1, v___x_6096_);
v___x_6098_ = lean_nat_add(v_idx_6055_, v___x_6093_);
lean_dec(v_idx_6055_);
lean_inc_n(v___x_6098_, 2);
lean_inc_ref(v_act_6048_);
lean_inc_ref(v_env_6047_);
lean_inc_ref(v_cctx_6046_);
v___x_6099_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_6099_, 0, lean_box(0));
lean_closure_set(v___x_6099_, 1, v_cctx_6046_);
lean_closure_set(v___x_6099_, 2, v___x_6095_);
lean_closure_set(v___x_6099_, 3, v_env_6047_);
lean_closure_set(v___x_6099_, 4, v_act_6048_);
lean_closure_set(v___x_6099_, 5, v_start_6053_);
lean_closure_set(v___x_6099_, 6, v___x_6098_);
v___x_6100_ = lean_unsigned_to_nat(0u);
v___x_6101_ = lean_io_as_task(v___x_6099_, v___x_6100_);
v___x_6102_ = lean_array_push(v_tasks_6052_, v___x_6101_);
v_ngen_6051_ = v___x_6097_;
v_tasks_6052_ = v___x_6102_;
v_start_6053_ = v___x_6098_;
v_cnt_6054_ = v___x_6100_;
v_idx_6055_ = v___x_6098_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg___boxed(lean_object* v_cctx_6106_, lean_object* v_env_6107_, lean_object* v_act_6108_, lean_object* v_constantsPerTask_6109_, lean_object* v_n_6110_, lean_object* v_ngen_6111_, lean_object* v_tasks_6112_, lean_object* v_start_6113_, lean_object* v_cnt_6114_, lean_object* v_idx_6115_, lean_object* v___y_6116_){
_start:
{
lean_object* v_res_6117_; 
v_res_6117_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(v_cctx_6106_, v_env_6107_, v_act_6108_, v_constantsPerTask_6109_, v_n_6110_, v_ngen_6111_, v_tasks_6112_, v_start_6113_, v_cnt_6114_, v_idx_6115_);
lean_dec(v_constantsPerTask_6109_);
return v_res_6117_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0(uint8_t v_suppressElabErrors_6126_, uint8_t v___y_6127_, lean_object* v_x_6128_){
_start:
{
if (lean_obj_tag(v_x_6128_) == 1)
{
lean_object* v_pre_6129_; 
v_pre_6129_ = lean_ctor_get(v_x_6128_, 0);
switch(lean_obj_tag(v_pre_6129_))
{
case 1:
{
lean_object* v_pre_6130_; 
v_pre_6130_ = lean_ctor_get(v_pre_6129_, 0);
switch(lean_obj_tag(v_pre_6130_))
{
case 0:
{
lean_object* v_str_6131_; lean_object* v_str_6132_; lean_object* v___x_6133_; uint8_t v___x_6134_; 
v_str_6131_ = lean_ctor_get(v_x_6128_, 1);
v_str_6132_ = lean_ctor_get(v_pre_6129_, 1);
v___x_6133_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__0));
v___x_6134_ = lean_string_dec_eq(v_str_6132_, v___x_6133_);
if (v___x_6134_ == 0)
{
lean_object* v___x_6135_; uint8_t v___x_6136_; 
v___x_6135_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__1));
v___x_6136_ = lean_string_dec_eq(v_str_6132_, v___x_6135_);
if (v___x_6136_ == 0)
{
return v___x_6136_;
}
else
{
lean_object* v___x_6137_; uint8_t v___x_6138_; 
v___x_6137_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__2));
v___x_6138_ = lean_string_dec_eq(v_str_6131_, v___x_6137_);
if (v___x_6138_ == 0)
{
return v___x_6138_;
}
else
{
return v_suppressElabErrors_6126_;
}
}
}
else
{
lean_object* v___x_6139_; uint8_t v___x_6140_; 
v___x_6139_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__3));
v___x_6140_ = lean_string_dec_eq(v_str_6131_, v___x_6139_);
if (v___x_6140_ == 0)
{
return v___x_6140_;
}
else
{
return v_suppressElabErrors_6126_;
}
}
}
case 1:
{
lean_object* v_pre_6141_; 
v_pre_6141_ = lean_ctor_get(v_pre_6130_, 0);
if (lean_obj_tag(v_pre_6141_) == 0)
{
lean_object* v_str_6142_; lean_object* v_str_6143_; lean_object* v_str_6144_; lean_object* v___x_6145_; uint8_t v___x_6146_; 
v_str_6142_ = lean_ctor_get(v_x_6128_, 1);
v_str_6143_ = lean_ctor_get(v_pre_6129_, 1);
v_str_6144_ = lean_ctor_get(v_pre_6130_, 1);
v___x_6145_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__4));
v___x_6146_ = lean_string_dec_eq(v_str_6144_, v___x_6145_);
if (v___x_6146_ == 0)
{
return v___x_6146_;
}
else
{
lean_object* v___x_6147_; uint8_t v___x_6148_; 
v___x_6147_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__5));
v___x_6148_ = lean_string_dec_eq(v_str_6143_, v___x_6147_);
if (v___x_6148_ == 0)
{
return v___x_6148_;
}
else
{
lean_object* v___x_6149_; uint8_t v___x_6150_; 
v___x_6149_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__6));
v___x_6150_ = lean_string_dec_eq(v_str_6142_, v___x_6149_);
if (v___x_6150_ == 0)
{
return v___x_6150_;
}
else
{
return v_suppressElabErrors_6126_;
}
}
}
}
else
{
return v___y_6127_;
}
}
default: 
{
return v___y_6127_;
}
}
}
case 0:
{
lean_object* v_str_6151_; lean_object* v___x_6152_; uint8_t v___x_6153_; 
v_str_6151_ = lean_ctor_get(v_x_6128_, 1);
v___x_6152_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__7));
v___x_6153_ = lean_string_dec_eq(v_str_6151_, v___x_6152_);
if (v___x_6153_ == 0)
{
return v___x_6153_;
}
else
{
return v_suppressElabErrors_6126_;
}
}
default: 
{
return v___y_6127_;
}
}
}
else
{
return v___y_6127_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___boxed(lean_object* v_suppressElabErrors_6154_, lean_object* v___y_6155_, lean_object* v_x_6156_){
_start:
{
uint8_t v_suppressElabErrors_boxed_6157_; uint8_t v___y_8181__boxed_6158_; uint8_t v_res_6159_; lean_object* v_r_6160_; 
v_suppressElabErrors_boxed_6157_ = lean_unbox(v_suppressElabErrors_6154_);
v___y_8181__boxed_6158_ = lean_unbox(v___y_6155_);
v_res_6159_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0(v_suppressElabErrors_boxed_6157_, v___y_8181__boxed_6158_, v_x_6156_);
lean_dec(v_x_6156_);
v_r_6160_ = lean_box(v_res_6159_);
return v_r_6160_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7_spec__9(lean_object* v_opts_6161_, lean_object* v_opt_6162_){
_start:
{
lean_object* v_name_6163_; lean_object* v_defValue_6164_; lean_object* v_map_6165_; lean_object* v___x_6166_; 
v_name_6163_ = lean_ctor_get(v_opt_6162_, 0);
v_defValue_6164_ = lean_ctor_get(v_opt_6162_, 1);
v_map_6165_ = lean_ctor_get(v_opts_6161_, 0);
v___x_6166_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_6165_, v_name_6163_);
if (lean_obj_tag(v___x_6166_) == 0)
{
uint8_t v___x_6167_; 
v___x_6167_ = lean_unbox(v_defValue_6164_);
return v___x_6167_;
}
else
{
lean_object* v_val_6168_; 
v_val_6168_ = lean_ctor_get(v___x_6166_, 0);
lean_inc(v_val_6168_);
lean_dec_ref_known(v___x_6166_, 1);
if (lean_obj_tag(v_val_6168_) == 1)
{
uint8_t v_v_6169_; 
v_v_6169_ = lean_ctor_get_uint8(v_val_6168_, 0);
lean_dec_ref_known(v_val_6168_, 0);
return v_v_6169_;
}
else
{
uint8_t v___x_6170_; 
lean_dec(v_val_6168_);
v___x_6170_ = lean_unbox(v_defValue_6164_);
return v___x_6170_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7_spec__9___boxed(lean_object* v_opts_6171_, lean_object* v_opt_6172_){
_start:
{
uint8_t v_res_6173_; lean_object* v_r_6174_; 
v_res_6173_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7_spec__9(v_opts_6171_, v_opt_6172_);
lean_dec_ref(v_opt_6172_);
lean_dec_ref(v_opts_6171_);
v_r_6174_ = lean_box(v_res_6173_);
return v_r_6174_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7(lean_object* v_ref_6176_, lean_object* v_msgData_6177_, uint8_t v_severity_6178_, uint8_t v_isSilent_6179_, lean_object* v___y_6180_, lean_object* v___y_6181_, lean_object* v___y_6182_, lean_object* v___y_6183_){
_start:
{
lean_object* v___y_6186_; lean_object* v___y_6187_; lean_object* v___y_6188_; uint8_t v___y_6189_; uint8_t v___y_6190_; lean_object* v___y_6191_; lean_object* v___y_6192_; lean_object* v_toCold_6193_; lean_object* v___y_6194_; lean_object* v___y_6223_; lean_object* v___y_6224_; uint8_t v___y_6225_; lean_object* v___y_6226_; uint8_t v___y_6227_; uint8_t v___y_6228_; lean_object* v___y_6229_; lean_object* v___y_6230_; uint8_t v___y_6250_; lean_object* v___y_6251_; lean_object* v___y_6252_; uint8_t v___y_6253_; lean_object* v___y_6254_; uint8_t v___y_6255_; lean_object* v___y_6256_; uint8_t v___y_6260_; uint8_t v___y_6261_; uint8_t v___y_6262_; uint8_t v___x_6273_; uint8_t v___y_6275_; uint8_t v___y_6276_; uint8_t v___y_6277_; uint8_t v___y_6279_; uint8_t v___x_6287_; 
v___x_6273_ = 2;
v___x_6287_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6178_, v___x_6273_);
if (v___x_6287_ == 0)
{
v___y_6279_ = v___x_6287_;
goto v___jp_6278_;
}
else
{
uint8_t v___x_6288_; 
lean_inc_ref(v_msgData_6177_);
v___x_6288_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_6177_);
v___y_6279_ = v___x_6288_;
goto v___jp_6278_;
}
v___jp_6185_:
{
lean_object* v_currNamespace_6195_; lean_object* v_openDecls_6196_; lean_object* v___x_6197_; lean_object* v___x_6198_; lean_object* v___x_6199_; lean_object* v___x_6200_; lean_object* v_env_6201_; lean_object* v_nextMacroScope_6202_; lean_object* v_ngen_6203_; lean_object* v_auxDeclNGen_6204_; lean_object* v_traceState_6205_; lean_object* v_cache_6206_; lean_object* v_recordedDeps_6207_; lean_object* v_messages_6208_; lean_object* v_infoState_6209_; lean_object* v_snapshotTasks_6210_; lean_object* v___x_6212_; uint8_t v_isShared_6213_; uint8_t v_isSharedCheck_6221_; 
v_currNamespace_6195_ = lean_ctor_get(v_toCold_6193_, 4);
v_openDecls_6196_ = lean_ctor_get(v_toCold_6193_, 5);
lean_inc(v_openDecls_6196_);
lean_inc(v_currNamespace_6195_);
v___x_6197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6197_, 0, v_currNamespace_6195_);
lean_ctor_set(v___x_6197_, 1, v_openDecls_6196_);
v___x_6198_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6198_, 0, v___x_6197_);
lean_ctor_set(v___x_6198_, 1, v___y_6188_);
lean_inc_ref(v___y_6187_);
lean_inc_ref(v___y_6192_);
v___x_6199_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_6199_, 0, v___y_6192_);
lean_ctor_set(v___x_6199_, 1, v___y_6191_);
lean_ctor_set(v___x_6199_, 2, v___y_6186_);
lean_ctor_set(v___x_6199_, 3, v___y_6187_);
lean_ctor_set(v___x_6199_, 4, v___x_6198_);
lean_ctor_set_uint8(v___x_6199_, sizeof(void*)*5, v___y_6189_);
lean_ctor_set_uint8(v___x_6199_, sizeof(void*)*5 + 1, v___y_6190_);
lean_ctor_set_uint8(v___x_6199_, sizeof(void*)*5 + 2, v_isSilent_6179_);
v___x_6200_ = lean_st_ref_take(v___y_6194_);
v_env_6201_ = lean_ctor_get(v___x_6200_, 0);
v_nextMacroScope_6202_ = lean_ctor_get(v___x_6200_, 1);
v_ngen_6203_ = lean_ctor_get(v___x_6200_, 2);
v_auxDeclNGen_6204_ = lean_ctor_get(v___x_6200_, 3);
v_traceState_6205_ = lean_ctor_get(v___x_6200_, 4);
v_cache_6206_ = lean_ctor_get(v___x_6200_, 5);
v_recordedDeps_6207_ = lean_ctor_get(v___x_6200_, 6);
v_messages_6208_ = lean_ctor_get(v___x_6200_, 7);
v_infoState_6209_ = lean_ctor_get(v___x_6200_, 8);
v_snapshotTasks_6210_ = lean_ctor_get(v___x_6200_, 9);
v_isSharedCheck_6221_ = !lean_is_exclusive(v___x_6200_);
if (v_isSharedCheck_6221_ == 0)
{
v___x_6212_ = v___x_6200_;
v_isShared_6213_ = v_isSharedCheck_6221_;
goto v_resetjp_6211_;
}
else
{
lean_inc(v_snapshotTasks_6210_);
lean_inc(v_infoState_6209_);
lean_inc(v_messages_6208_);
lean_inc(v_recordedDeps_6207_);
lean_inc(v_cache_6206_);
lean_inc(v_traceState_6205_);
lean_inc(v_auxDeclNGen_6204_);
lean_inc(v_ngen_6203_);
lean_inc(v_nextMacroScope_6202_);
lean_inc(v_env_6201_);
lean_dec(v___x_6200_);
v___x_6212_ = lean_box(0);
v_isShared_6213_ = v_isSharedCheck_6221_;
goto v_resetjp_6211_;
}
v_resetjp_6211_:
{
lean_object* v___x_6214_; lean_object* v___x_6215_; lean_object* v___x_6217_; 
v___x_6214_ = lean_box(0);
v___x_6215_ = l_Lean_MessageLog_add(v___x_6199_, v_messages_6208_);
if (v_isShared_6213_ == 0)
{
lean_ctor_set(v___x_6212_, 7, v___x_6215_);
v___x_6217_ = v___x_6212_;
goto v_reusejp_6216_;
}
else
{
lean_object* v_reuseFailAlloc_6220_; 
v_reuseFailAlloc_6220_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6220_, 0, v_env_6201_);
lean_ctor_set(v_reuseFailAlloc_6220_, 1, v_nextMacroScope_6202_);
lean_ctor_set(v_reuseFailAlloc_6220_, 2, v_ngen_6203_);
lean_ctor_set(v_reuseFailAlloc_6220_, 3, v_auxDeclNGen_6204_);
lean_ctor_set(v_reuseFailAlloc_6220_, 4, v_traceState_6205_);
lean_ctor_set(v_reuseFailAlloc_6220_, 5, v_cache_6206_);
lean_ctor_set(v_reuseFailAlloc_6220_, 6, v_recordedDeps_6207_);
lean_ctor_set(v_reuseFailAlloc_6220_, 7, v___x_6215_);
lean_ctor_set(v_reuseFailAlloc_6220_, 8, v_infoState_6209_);
lean_ctor_set(v_reuseFailAlloc_6220_, 9, v_snapshotTasks_6210_);
v___x_6217_ = v_reuseFailAlloc_6220_;
goto v_reusejp_6216_;
}
v_reusejp_6216_:
{
lean_object* v___x_6218_; lean_object* v___x_6219_; 
v___x_6218_ = lean_st_ref_put(v___y_6194_, v___x_6217_);
v___x_6219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6219_, 0, v___x_6214_);
return v___x_6219_;
}
}
}
v___jp_6222_:
{
lean_object* v_fileName_6231_; lean_object* v_fileMap_6232_; lean_object* v___x_6233_; lean_object* v___x_6234_; lean_object* v_a_6235_; lean_object* v___x_6237_; uint8_t v_isShared_6238_; uint8_t v_isSharedCheck_6248_; 
v_fileName_6231_ = lean_ctor_get(v___y_6229_, 0);
v_fileMap_6232_ = lean_ctor_get(v___y_6229_, 1);
v___x_6233_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_6177_);
v___x_6234_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(v___x_6233_, v___y_6180_, v___y_6181_, v___y_6182_, v___y_6183_);
v_a_6235_ = lean_ctor_get(v___x_6234_, 0);
v_isSharedCheck_6248_ = !lean_is_exclusive(v___x_6234_);
if (v_isSharedCheck_6248_ == 0)
{
v___x_6237_ = v___x_6234_;
v_isShared_6238_ = v_isSharedCheck_6248_;
goto v_resetjp_6236_;
}
else
{
lean_inc(v_a_6235_);
lean_dec(v___x_6234_);
v___x_6237_ = lean_box(0);
v_isShared_6238_ = v_isSharedCheck_6248_;
goto v_resetjp_6236_;
}
v_resetjp_6236_:
{
lean_object* v___x_6239_; lean_object* v___x_6240_; lean_object* v___x_6241_; lean_object* v___x_6242_; 
lean_inc_ref_n(v_fileMap_6232_, 2);
v___x_6239_ = l_Lean_FileMap_toPosition(v_fileMap_6232_, v___y_6226_);
lean_dec(v___y_6226_);
v___x_6240_ = l_Lean_FileMap_toPosition(v_fileMap_6232_, v___y_6230_);
lean_dec(v___y_6230_);
v___x_6241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6241_, 0, v___x_6240_);
v___x_6242_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___closed__0));
if (v___y_6225_ == 0)
{
lean_del_object(v___x_6237_);
lean_dec_ref(v___y_6223_);
v___y_6186_ = v___x_6241_;
v___y_6187_ = v___x_6242_;
v___y_6188_ = v_a_6235_;
v___y_6189_ = v___y_6227_;
v___y_6190_ = v___y_6228_;
v___y_6191_ = v___x_6239_;
v___y_6192_ = v_fileName_6231_;
v_toCold_6193_ = v___y_6224_;
v___y_6194_ = v___y_6183_;
goto v___jp_6185_;
}
else
{
uint8_t v___x_6243_; 
lean_inc(v_a_6235_);
v___x_6243_ = l_Lean_MessageData_hasTag(v___y_6223_, v_a_6235_);
if (v___x_6243_ == 0)
{
lean_object* v___x_6244_; lean_object* v___x_6246_; 
lean_dec_ref_known(v___x_6241_, 1);
lean_dec_ref(v___x_6239_);
lean_dec(v_a_6235_);
v___x_6244_ = lean_box(0);
if (v_isShared_6238_ == 0)
{
lean_ctor_set(v___x_6237_, 0, v___x_6244_);
v___x_6246_ = v___x_6237_;
goto v_reusejp_6245_;
}
else
{
lean_object* v_reuseFailAlloc_6247_; 
v_reuseFailAlloc_6247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6247_, 0, v___x_6244_);
v___x_6246_ = v_reuseFailAlloc_6247_;
goto v_reusejp_6245_;
}
v_reusejp_6245_:
{
return v___x_6246_;
}
}
else
{
lean_del_object(v___x_6237_);
v___y_6186_ = v___x_6241_;
v___y_6187_ = v___x_6242_;
v___y_6188_ = v_a_6235_;
v___y_6189_ = v___y_6227_;
v___y_6190_ = v___y_6228_;
v___y_6191_ = v___x_6239_;
v___y_6192_ = v_fileName_6231_;
v_toCold_6193_ = v___y_6224_;
v___y_6194_ = v___y_6183_;
goto v___jp_6185_;
}
}
}
}
v___jp_6249_:
{
lean_object* v___x_6257_; 
v___x_6257_ = l_Lean_Syntax_getTailPos_x3f(v___y_6254_, v___y_6253_);
lean_dec(v___y_6254_);
if (lean_obj_tag(v___x_6257_) == 0)
{
lean_inc(v___y_6256_);
v___y_6223_ = v___y_6251_;
v___y_6224_ = v___y_6252_;
v___y_6225_ = v___y_6250_;
v___y_6226_ = v___y_6256_;
v___y_6227_ = v___y_6253_;
v___y_6228_ = v___y_6255_;
v___y_6229_ = v___y_6252_;
v___y_6230_ = v___y_6256_;
goto v___jp_6222_;
}
else
{
lean_object* v_val_6258_; 
v_val_6258_ = lean_ctor_get(v___x_6257_, 0);
lean_inc(v_val_6258_);
lean_dec_ref_known(v___x_6257_, 1);
v___y_6223_ = v___y_6251_;
v___y_6224_ = v___y_6252_;
v___y_6225_ = v___y_6250_;
v___y_6226_ = v___y_6256_;
v___y_6227_ = v___y_6253_;
v___y_6228_ = v___y_6255_;
v___y_6229_ = v___y_6252_;
v___y_6230_ = v_val_6258_;
goto v___jp_6222_;
}
}
v___jp_6259_:
{
lean_object* v_toCold_6263_; lean_object* v_ref_6264_; uint8_t v_suppressElabErrors_6265_; lean_object* v___x_6266_; lean_object* v___x_6267_; lean_object* v___f_6268_; lean_object* v_ref_6269_; lean_object* v___x_6270_; 
v_toCold_6263_ = lean_ctor_get(v___y_6182_, 0);
v_ref_6264_ = lean_ctor_get(v___y_6182_, 2);
v_suppressElabErrors_6265_ = lean_ctor_get_uint8(v___y_6182_, sizeof(void*)*3 + 2);
v___x_6266_ = lean_box(v_suppressElabErrors_6265_);
v___x_6267_ = lean_box(v___y_6260_);
v___f_6268_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_6268_, 0, v___x_6266_);
lean_closure_set(v___f_6268_, 1, v___x_6267_);
v_ref_6269_ = l_Lean_replaceRef(v_ref_6176_, v_ref_6264_);
v___x_6270_ = l_Lean_Syntax_getPos_x3f(v_ref_6269_, v___y_6261_);
if (lean_obj_tag(v___x_6270_) == 0)
{
lean_object* v___x_6271_; 
v___x_6271_ = lean_unsigned_to_nat(0u);
v___y_6250_ = v_suppressElabErrors_6265_;
v___y_6251_ = v___f_6268_;
v___y_6252_ = v_toCold_6263_;
v___y_6253_ = v___y_6261_;
v___y_6254_ = v_ref_6269_;
v___y_6255_ = v___y_6262_;
v___y_6256_ = v___x_6271_;
goto v___jp_6249_;
}
else
{
lean_object* v_val_6272_; 
v_val_6272_ = lean_ctor_get(v___x_6270_, 0);
lean_inc(v_val_6272_);
lean_dec_ref_known(v___x_6270_, 1);
v___y_6250_ = v_suppressElabErrors_6265_;
v___y_6251_ = v___f_6268_;
v___y_6252_ = v_toCold_6263_;
v___y_6253_ = v___y_6261_;
v___y_6254_ = v_ref_6269_;
v___y_6255_ = v___y_6262_;
v___y_6256_ = v_val_6272_;
goto v___jp_6249_;
}
}
v___jp_6274_:
{
if (v___y_6277_ == 0)
{
v___y_6260_ = v___y_6275_;
v___y_6261_ = v___y_6276_;
v___y_6262_ = v_severity_6178_;
goto v___jp_6259_;
}
else
{
v___y_6260_ = v___y_6275_;
v___y_6261_ = v___y_6276_;
v___y_6262_ = v___x_6273_;
goto v___jp_6259_;
}
}
v___jp_6278_:
{
if (v___y_6279_ == 0)
{
uint8_t v___x_6280_; uint8_t v___x_6281_; 
v___x_6280_ = 1;
v___x_6281_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6178_, v___x_6280_);
if (v___x_6281_ == 0)
{
v___y_6275_ = v___y_6279_;
v___y_6276_ = v___y_6279_;
v___y_6277_ = v___x_6281_;
goto v___jp_6274_;
}
else
{
lean_object* v___x_6282_; lean_object* v___x_6283_; uint8_t v___x_6284_; 
v___x_6282_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_6182_);
v___x_6283_ = l_Lean_warningAsError;
v___x_6284_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7_spec__9(v___x_6282_, v___x_6283_);
lean_dec_ref(v___x_6282_);
v___y_6275_ = v___y_6279_;
v___y_6276_ = v___y_6279_;
v___y_6277_ = v___x_6284_;
goto v___jp_6274_;
}
}
else
{
lean_object* v___x_6285_; lean_object* v___x_6286_; 
lean_dec_ref(v_msgData_6177_);
v___x_6285_ = lean_box(0);
v___x_6286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6286_, 0, v___x_6285_);
return v___x_6286_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___boxed(lean_object* v_ref_6289_, lean_object* v_msgData_6290_, lean_object* v_severity_6291_, lean_object* v_isSilent_6292_, lean_object* v___y_6293_, lean_object* v___y_6294_, lean_object* v___y_6295_, lean_object* v___y_6296_, lean_object* v___y_6297_){
_start:
{
uint8_t v_severity_boxed_6298_; uint8_t v_isSilent_boxed_6299_; lean_object* v_res_6300_; 
v_severity_boxed_6298_ = lean_unbox(v_severity_6291_);
v_isSilent_boxed_6299_ = lean_unbox(v_isSilent_6292_);
v_res_6300_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7(v_ref_6289_, v_msgData_6290_, v_severity_boxed_6298_, v_isSilent_boxed_6299_, v___y_6293_, v___y_6294_, v___y_6295_, v___y_6296_);
lean_dec(v___y_6296_);
lean_dec_ref(v___y_6295_);
lean_dec(v___y_6294_);
lean_dec_ref(v___y_6293_);
lean_dec(v_ref_6289_);
return v_res_6300_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3(lean_object* v_msgData_6301_, uint8_t v_severity_6302_, uint8_t v_isSilent_6303_, lean_object* v___y_6304_, lean_object* v___y_6305_, lean_object* v___y_6306_, lean_object* v___y_6307_){
_start:
{
lean_object* v_ref_6309_; lean_object* v___x_6310_; 
v_ref_6309_ = lean_ctor_get(v___y_6306_, 2);
v___x_6310_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7(v_ref_6309_, v_msgData_6301_, v_severity_6302_, v_isSilent_6303_, v___y_6304_, v___y_6305_, v___y_6306_, v___y_6307_);
return v___x_6310_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_msgData_6311_, lean_object* v_severity_6312_, lean_object* v_isSilent_6313_, lean_object* v___y_6314_, lean_object* v___y_6315_, lean_object* v___y_6316_, lean_object* v___y_6317_, lean_object* v___y_6318_){
_start:
{
uint8_t v_severity_boxed_6319_; uint8_t v_isSilent_boxed_6320_; lean_object* v_res_6321_; 
v_severity_boxed_6319_ = lean_unbox(v_severity_6312_);
v_isSilent_boxed_6320_ = lean_unbox(v_isSilent_6313_);
v_res_6321_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3(v_msgData_6311_, v_severity_boxed_6319_, v_isSilent_boxed_6320_, v___y_6314_, v___y_6315_, v___y_6316_, v___y_6317_);
lean_dec(v___y_6317_);
lean_dec_ref(v___y_6316_);
lean_dec(v___y_6315_);
lean_dec_ref(v___y_6314_);
return v_res_6321_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2(lean_object* v_msgData_6322_, lean_object* v___y_6323_, lean_object* v___y_6324_, lean_object* v___y_6325_, lean_object* v___y_6326_){
_start:
{
uint8_t v___x_6328_; uint8_t v___x_6329_; lean_object* v___x_6330_; 
v___x_6328_ = 2;
v___x_6329_ = 0;
v___x_6330_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3(v_msgData_6322_, v___x_6328_, v___x_6329_, v___y_6323_, v___y_6324_, v___y_6325_, v___y_6326_);
return v___x_6330_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_6331_, lean_object* v___y_6332_, lean_object* v___y_6333_, lean_object* v___y_6334_, lean_object* v___y_6335_, lean_object* v___y_6336_){
_start:
{
lean_object* v_res_6337_; 
v_res_6337_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2(v_msgData_6331_, v___y_6332_, v___y_6333_, v___y_6334_, v___y_6335_);
lean_dec(v___y_6335_);
lean_dec_ref(v___y_6334_);
lean_dec(v___y_6333_);
lean_dec_ref(v___y_6332_);
return v_res_6337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0(lean_object* v_f_6338_, lean_object* v___y_6339_, lean_object* v___y_6340_, lean_object* v___y_6341_, lean_object* v___y_6342_){
_start:
{
lean_object* v_module_6344_; lean_object* v_const_6345_; lean_object* v_exception_6346_; lean_object* v___x_6347_; lean_object* v___x_6348_; lean_object* v___x_6349_; lean_object* v___x_6350_; lean_object* v___x_6351_; lean_object* v___x_6352_; lean_object* v___x_6353_; lean_object* v___x_6354_; lean_object* v___x_6355_; lean_object* v___x_6356_; lean_object* v___x_6357_; lean_object* v___x_6358_; 
v_module_6344_ = lean_ctor_get(v_f_6338_, 0);
lean_inc(v_module_6344_);
v_const_6345_ = lean_ctor_get(v_f_6338_, 1);
lean_inc(v_const_6345_);
v_exception_6346_ = lean_ctor_get(v_f_6338_, 2);
lean_inc_ref(v_exception_6346_);
lean_dec_ref(v_f_6338_);
v___x_6347_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1);
v___x_6348_ = l_Lean_MessageData_ofName(v_const_6345_);
v___x_6349_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6349_, 0, v___x_6347_);
lean_ctor_set(v___x_6349_, 1, v___x_6348_);
v___x_6350_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3);
v___x_6351_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6351_, 0, v___x_6349_);
lean_ctor_set(v___x_6351_, 1, v___x_6350_);
v___x_6352_ = l_Lean_MessageData_ofName(v_module_6344_);
v___x_6353_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6353_, 0, v___x_6351_);
lean_ctor_set(v___x_6353_, 1, v___x_6352_);
v___x_6354_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5);
v___x_6355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6355_, 0, v___x_6353_);
lean_ctor_set(v___x_6355_, 1, v___x_6354_);
v___x_6356_ = l_Lean_Exception_toMessageData(v_exception_6346_);
v___x_6357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6357_, 0, v___x_6355_);
lean_ctor_set(v___x_6357_, 1, v___x_6356_);
v___x_6358_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2(v___x_6357_, v___y_6339_, v___y_6340_, v___y_6341_, v___y_6342_);
return v___x_6358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0___boxed(lean_object* v_f_6359_, lean_object* v___y_6360_, lean_object* v___y_6361_, lean_object* v___y_6362_, lean_object* v___y_6363_, lean_object* v___y_6364_){
_start:
{
lean_object* v_res_6365_; 
v_res_6365_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0(v_f_6359_, v___y_6360_, v___y_6361_, v___y_6362_, v___y_6363_);
lean_dec(v___y_6363_);
lean_dec_ref(v___y_6362_);
lean_dec(v___y_6361_);
lean_dec_ref(v___y_6360_);
return v_res_6365_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3(lean_object* v_as_6366_, size_t v_i_6367_, size_t v_stop_6368_, lean_object* v_b_6369_, lean_object* v___y_6370_, lean_object* v___y_6371_, lean_object* v___y_6372_, lean_object* v___y_6373_){
_start:
{
uint8_t v___x_6375_; 
v___x_6375_ = lean_usize_dec_eq(v_i_6367_, v_stop_6368_);
if (v___x_6375_ == 0)
{
lean_object* v___x_6376_; lean_object* v___x_6377_; 
v___x_6376_ = lean_array_uget_borrowed(v_as_6366_, v_i_6367_);
lean_inc(v___x_6376_);
v___x_6377_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0(v___x_6376_, v___y_6370_, v___y_6371_, v___y_6372_, v___y_6373_);
if (lean_obj_tag(v___x_6377_) == 0)
{
lean_object* v_a_6378_; size_t v___x_6379_; size_t v___x_6380_; 
v_a_6378_ = lean_ctor_get(v___x_6377_, 0);
lean_inc(v_a_6378_);
lean_dec_ref_known(v___x_6377_, 1);
v___x_6379_ = ((size_t)1ULL);
v___x_6380_ = lean_usize_add(v_i_6367_, v___x_6379_);
v_i_6367_ = v___x_6380_;
v_b_6369_ = v_a_6378_;
goto _start;
}
else
{
return v___x_6377_;
}
}
else
{
lean_object* v___x_6382_; 
v___x_6382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6382_, 0, v_b_6369_);
return v___x_6382_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3___boxed(lean_object* v_as_6383_, lean_object* v_i_6384_, lean_object* v_stop_6385_, lean_object* v_b_6386_, lean_object* v___y_6387_, lean_object* v___y_6388_, lean_object* v___y_6389_, lean_object* v___y_6390_, lean_object* v___y_6391_){
_start:
{
size_t v_i_boxed_6392_; size_t v_stop_boxed_6393_; lean_object* v_res_6394_; 
v_i_boxed_6392_ = lean_unbox_usize(v_i_6384_);
lean_dec(v_i_6384_);
v_stop_boxed_6393_ = lean_unbox_usize(v_stop_6385_);
lean_dec(v_stop_6385_);
v_res_6394_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3(v_as_6383_, v_i_boxed_6392_, v_stop_boxed_6393_, v_b_6386_, v___y_6387_, v___y_6388_, v___y_6389_, v___y_6390_);
lean_dec(v___y_6390_);
lean_dec_ref(v___y_6389_);
lean_dec(v___y_6388_);
lean_dec_ref(v___y_6387_);
lean_dec_ref(v_as_6383_);
return v_res_6394_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(lean_object* v_as_6395_, size_t v_i_6396_, size_t v_stop_6397_, lean_object* v_b_6398_){
_start:
{
uint8_t v___x_6399_; 
v___x_6399_ = lean_usize_dec_eq(v_i_6396_, v_stop_6397_);
if (v___x_6399_ == 0)
{
lean_object* v___x_6400_; lean_object* v___x_6401_; lean_object* v___x_6402_; size_t v___x_6403_; size_t v___x_6404_; 
v___x_6400_ = lean_array_uget_borrowed(v_as_6395_, v_i_6396_);
lean_inc(v___x_6400_);
v___x_6401_ = lean_task_get_own(v___x_6400_);
v___x_6402_ = l_Lean_Meta_LazyDiscrTree_InitResults_append___redArg(v_b_6398_, v___x_6401_);
v___x_6403_ = ((size_t)1ULL);
v___x_6404_ = lean_usize_add(v_i_6396_, v___x_6403_);
v_i_6396_ = v___x_6404_;
v_b_6398_ = v___x_6402_;
goto _start;
}
else
{
return v_b_6398_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_as_6406_, lean_object* v_i_6407_, lean_object* v_stop_6408_, lean_object* v_b_6409_){
_start:
{
size_t v_i_boxed_6410_; size_t v_stop_boxed_6411_; lean_object* v_res_6412_; 
v_i_boxed_6410_ = lean_unbox_usize(v_i_6407_);
lean_dec(v_i_6407_);
v_stop_boxed_6411_ = lean_unbox_usize(v_stop_6408_);
lean_dec(v_stop_6408_);
v_res_6412_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(v_as_6406_, v_i_boxed_6410_, v_stop_boxed_6411_, v_b_6409_);
lean_dec_ref(v_as_6406_);
return v_res_6412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(lean_object* v_z_6413_, lean_object* v_tasks_6414_){
_start:
{
lean_object* v___x_6415_; lean_object* v___x_6416_; uint8_t v___x_6417_; 
v___x_6415_ = lean_unsigned_to_nat(0u);
v___x_6416_ = lean_array_get_size(v_tasks_6414_);
v___x_6417_ = lean_nat_dec_lt(v___x_6415_, v___x_6416_);
if (v___x_6417_ == 0)
{
return v_z_6413_;
}
else
{
size_t v___x_6418_; size_t v___x_6419_; lean_object* v___x_6420_; 
v___x_6418_ = ((size_t)0ULL);
v___x_6419_ = lean_usize_of_nat(v___x_6416_);
v___x_6420_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(v_tasks_6414_, v___x_6418_, v___x_6419_, v_z_6413_);
return v___x_6420_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg___boxed(lean_object* v_z_6421_, lean_object* v_tasks_6422_){
_start:
{
lean_object* v_res_6423_; 
v_res_6423_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(v_z_6421_, v_tasks_6422_);
lean_dec_ref(v_tasks_6422_);
return v_res_6423_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_6424_; lean_object* v___x_6425_; lean_object* v___x_6426_; 
v___x_6424_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
v___x_6425_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2);
v___x_6426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6426_, 0, v___x_6425_);
lean_ctor_set(v___x_6426_, 1, v___x_6424_);
return v___x_6426_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_6427_; lean_object* v___x_6428_; lean_object* v___x_6429_; 
v___x_6427_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
v___x_6428_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0);
v___x_6429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6429_, 0, v___x_6428_);
lean_ctor_set(v___x_6429_, 1, v___x_6427_);
return v___x_6429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(lean_object* v_cctx_6430_, lean_object* v_ngen_6431_, lean_object* v_env_6432_, lean_object* v_act_6433_, lean_object* v_constantsPerTask_6434_, lean_object* v___y_6435_, lean_object* v___y_6436_, lean_object* v___y_6437_, lean_object* v___y_6438_){
_start:
{
lean_object* v___x_6440_; lean_object* v_moduleData_6441_; lean_object* v_n_6442_; lean_object* v___x_6443_; lean_object* v___x_6444_; lean_object* v___x_6445_; lean_object* v_a_6446_; lean_object* v___x_6448_; uint8_t v_isShared_6449_; uint8_t v_isSharedCheck_6481_; 
v___x_6440_ = l_Lean_Environment_header(v_env_6432_);
v_moduleData_6441_ = lean_ctor_get(v___x_6440_, 6);
lean_inc_ref(v_moduleData_6441_);
lean_dec_ref(v___x_6440_);
v_n_6442_ = lean_array_get_size(v_moduleData_6441_);
lean_dec_ref(v_moduleData_6441_);
v___x_6443_ = lean_unsigned_to_nat(0u);
v___x_6444_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
v___x_6445_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(v_cctx_6430_, v_env_6432_, v_act_6433_, v_constantsPerTask_6434_, v_n_6442_, v_ngen_6431_, v___x_6444_, v___x_6443_, v___x_6443_, v___x_6443_);
v_a_6446_ = lean_ctor_get(v___x_6445_, 0);
v_isSharedCheck_6481_ = !lean_is_exclusive(v___x_6445_);
if (v_isSharedCheck_6481_ == 0)
{
v___x_6448_ = v___x_6445_;
v_isShared_6449_ = v_isSharedCheck_6481_;
goto v_resetjp_6447_;
}
else
{
lean_inc(v_a_6446_);
lean_dec(v___x_6445_);
v___x_6448_ = lean_box(0);
v_isShared_6449_ = v_isSharedCheck_6481_;
goto v_resetjp_6447_;
}
v_resetjp_6447_:
{
lean_object* v___x_6450_; lean_object* v_r_6451_; lean_object* v_tree_6452_; lean_object* v_errors_6453_; lean_object* v___x_6454_; uint8_t v___x_6455_; 
v___x_6450_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1);
v_r_6451_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(v___x_6450_, v_a_6446_);
lean_dec(v_a_6446_);
v_tree_6452_ = lean_ctor_get(v_r_6451_, 0);
lean_inc_ref(v_tree_6452_);
v_errors_6453_ = lean_ctor_get(v_r_6451_, 1);
lean_inc_ref(v_errors_6453_);
lean_dec_ref(v_r_6451_);
v___x_6454_ = lean_array_get_size(v_errors_6453_);
v___x_6455_ = lean_nat_dec_lt(v___x_6443_, v___x_6454_);
if (v___x_6455_ == 0)
{
lean_object* v___x_6456_; lean_object* v___x_6458_; 
lean_dec_ref(v_errors_6453_);
v___x_6456_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_tree_6452_);
if (v_isShared_6449_ == 0)
{
lean_ctor_set(v___x_6448_, 0, v___x_6456_);
v___x_6458_ = v___x_6448_;
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
else
{
lean_object* v___x_6460_; size_t v___x_6461_; size_t v___x_6462_; lean_object* v___x_6463_; 
lean_del_object(v___x_6448_);
v___x_6460_ = lean_box(0);
v___x_6461_ = ((size_t)0ULL);
v___x_6462_ = lean_usize_of_nat(v___x_6454_);
v___x_6463_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3(v_errors_6453_, v___x_6461_, v___x_6462_, v___x_6460_, v___y_6435_, v___y_6436_, v___y_6437_, v___y_6438_);
lean_dec_ref(v_errors_6453_);
if (lean_obj_tag(v___x_6463_) == 0)
{
lean_object* v___x_6465_; uint8_t v_isShared_6466_; uint8_t v_isSharedCheck_6471_; 
v_isSharedCheck_6471_ = !lean_is_exclusive(v___x_6463_);
if (v_isSharedCheck_6471_ == 0)
{
lean_object* v_unused_6472_; 
v_unused_6472_ = lean_ctor_get(v___x_6463_, 0);
lean_dec(v_unused_6472_);
v___x_6465_ = v___x_6463_;
v_isShared_6466_ = v_isSharedCheck_6471_;
goto v_resetjp_6464_;
}
else
{
lean_dec(v___x_6463_);
v___x_6465_ = lean_box(0);
v_isShared_6466_ = v_isSharedCheck_6471_;
goto v_resetjp_6464_;
}
v_resetjp_6464_:
{
lean_object* v___x_6467_; lean_object* v___x_6469_; 
v___x_6467_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_tree_6452_);
if (v_isShared_6466_ == 0)
{
lean_ctor_set(v___x_6465_, 0, v___x_6467_);
v___x_6469_ = v___x_6465_;
goto v_reusejp_6468_;
}
else
{
lean_object* v_reuseFailAlloc_6470_; 
v_reuseFailAlloc_6470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6470_, 0, v___x_6467_);
v___x_6469_ = v_reuseFailAlloc_6470_;
goto v_reusejp_6468_;
}
v_reusejp_6468_:
{
return v___x_6469_;
}
}
}
else
{
lean_object* v_a_6473_; lean_object* v___x_6475_; uint8_t v_isShared_6476_; uint8_t v_isSharedCheck_6480_; 
lean_dec_ref(v_tree_6452_);
v_a_6473_ = lean_ctor_get(v___x_6463_, 0);
v_isSharedCheck_6480_ = !lean_is_exclusive(v___x_6463_);
if (v_isSharedCheck_6480_ == 0)
{
v___x_6475_ = v___x_6463_;
v_isShared_6476_ = v_isSharedCheck_6480_;
goto v_resetjp_6474_;
}
else
{
lean_inc(v_a_6473_);
lean_dec(v___x_6463_);
v___x_6475_ = lean_box(0);
v_isShared_6476_ = v_isSharedCheck_6480_;
goto v_resetjp_6474_;
}
v_resetjp_6474_:
{
lean_object* v___x_6478_; 
if (v_isShared_6476_ == 0)
{
v___x_6478_ = v___x_6475_;
goto v_reusejp_6477_;
}
else
{
lean_object* v_reuseFailAlloc_6479_; 
v_reuseFailAlloc_6479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6479_, 0, v_a_6473_);
v___x_6478_ = v_reuseFailAlloc_6479_;
goto v_reusejp_6477_;
}
v_reusejp_6477_:
{
return v___x_6478_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___boxed(lean_object* v_cctx_6482_, lean_object* v_ngen_6483_, lean_object* v_env_6484_, lean_object* v_act_6485_, lean_object* v_constantsPerTask_6486_, lean_object* v___y_6487_, lean_object* v___y_6488_, lean_object* v___y_6489_, lean_object* v___y_6490_, lean_object* v___y_6491_){
_start:
{
lean_object* v_res_6492_; 
v_res_6492_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(v_cctx_6482_, v_ngen_6483_, v_env_6484_, v_act_6485_, v_constantsPerTask_6486_, v___y_6487_, v___y_6488_, v___y_6489_, v___y_6490_);
lean_dec(v___y_6490_);
lean_dec_ref(v___y_6489_);
lean_dec(v___y_6488_);
lean_dec_ref(v___y_6487_);
lean_dec(v_constantsPerTask_6486_);
return v_res_6492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0(lean_object* v_a_6493_, lean_object* v___x_6494_, lean_object* v_addEntry_6495_, lean_object* v_constantsPerTask_6496_, lean_object* v_droppedEntriesRef_6497_, lean_object* v_droppedKeys_6498_, lean_object* v___y_6499_, lean_object* v___y_6500_, lean_object* v___y_6501_, lean_object* v___y_6502_){
_start:
{
lean_object* v___x_6504_; lean_object* v_env_6505_; lean_object* v___x_6506_; lean_object* v___x_6507_; 
v___x_6504_ = lean_st_ref_get(v___y_6502_);
v_env_6505_ = lean_ctor_get(v___x_6504_, 0);
lean_inc_ref(v_env_6505_);
lean_dec(v___x_6504_);
lean_inc_ref(v_a_6493_);
v___x_6506_ = l_Lean_Meta_LazyDiscrTree_createTreeCtx(v_a_6493_);
v___x_6507_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(v___x_6506_, v___x_6494_, v_env_6505_, v_addEntry_6495_, v_constantsPerTask_6496_, v___y_6499_, v___y_6500_, v___y_6501_, v___y_6502_);
if (lean_obj_tag(v___x_6507_) == 0)
{
if (lean_obj_tag(v_droppedEntriesRef_6497_) == 1)
{
lean_object* v_a_6508_; lean_object* v_val_6509_; lean_object* v___x_6511_; uint8_t v_isShared_6512_; uint8_t v_isSharedCheck_6542_; 
v_a_6508_ = lean_ctor_get(v___x_6507_, 0);
lean_inc(v_a_6508_);
lean_dec_ref_known(v___x_6507_, 1);
v_val_6509_ = lean_ctor_get(v_droppedEntriesRef_6497_, 0);
v_isSharedCheck_6542_ = !lean_is_exclusive(v_droppedEntriesRef_6497_);
if (v_isSharedCheck_6542_ == 0)
{
v___x_6511_ = v_droppedEntriesRef_6497_;
v_isShared_6512_ = v_isSharedCheck_6542_;
goto v_resetjp_6510_;
}
else
{
lean_inc(v_val_6509_);
lean_dec(v_droppedEntriesRef_6497_);
v___x_6511_ = lean_box(0);
v_isShared_6512_ = v_isSharedCheck_6542_;
goto v_resetjp_6510_;
}
v_resetjp_6510_:
{
lean_object* v___x_6513_; 
v___x_6513_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_a_6508_, v_droppedKeys_6498_, v___y_6499_, v___y_6500_, v___y_6501_, v___y_6502_);
lean_dec(v_droppedKeys_6498_);
if (lean_obj_tag(v___x_6513_) == 0)
{
lean_object* v_a_6514_; lean_object* v___x_6516_; uint8_t v_isShared_6517_; uint8_t v_isSharedCheck_6533_; 
v_a_6514_ = lean_ctor_get(v___x_6513_, 0);
v_isSharedCheck_6533_ = !lean_is_exclusive(v___x_6513_);
if (v_isSharedCheck_6533_ == 0)
{
v___x_6516_ = v___x_6513_;
v_isShared_6517_ = v_isSharedCheck_6533_;
goto v_resetjp_6515_;
}
else
{
lean_inc(v_a_6514_);
lean_dec(v___x_6513_);
v___x_6516_ = lean_box(0);
v_isShared_6517_ = v_isSharedCheck_6533_;
goto v_resetjp_6515_;
}
v_resetjp_6515_:
{
lean_object* v_fst_6518_; lean_object* v_snd_6519_; lean_object* v___x_6520_; lean_object* v___y_6522_; 
v_fst_6518_ = lean_ctor_get(v_a_6514_, 0);
lean_inc(v_fst_6518_);
v_snd_6519_ = lean_ctor_get(v_a_6514_, 1);
lean_inc(v_snd_6519_);
lean_dec(v_a_6514_);
v___x_6520_ = lean_st_ref_get(v_val_6509_);
if (lean_obj_tag(v___x_6520_) == 0)
{
lean_object* v___x_6531_; 
v___x_6531_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___y_6522_ = v___x_6531_;
goto v___jp_6521_;
}
else
{
lean_object* v_val_6532_; 
v_val_6532_ = lean_ctor_get(v___x_6520_, 0);
lean_inc(v_val_6532_);
lean_dec_ref_known(v___x_6520_, 1);
v___y_6522_ = v_val_6532_;
goto v___jp_6521_;
}
v___jp_6521_:
{
lean_object* v___x_6523_; lean_object* v___x_6525_; 
v___x_6523_ = l_Array_append___redArg(v___y_6522_, v_fst_6518_);
lean_dec(v_fst_6518_);
if (v_isShared_6512_ == 0)
{
lean_ctor_set(v___x_6511_, 0, v___x_6523_);
v___x_6525_ = v___x_6511_;
goto v_reusejp_6524_;
}
else
{
lean_object* v_reuseFailAlloc_6530_; 
v_reuseFailAlloc_6530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6530_, 0, v___x_6523_);
v___x_6525_ = v_reuseFailAlloc_6530_;
goto v_reusejp_6524_;
}
v_reusejp_6524_:
{
lean_object* v___x_6526_; lean_object* v___x_6528_; 
v___x_6526_ = lean_st_ref_swap(v_val_6509_, v___x_6525_);
lean_dec(v_val_6509_);
lean_dec(v___x_6526_);
if (v_isShared_6517_ == 0)
{
lean_ctor_set(v___x_6516_, 0, v_snd_6519_);
v___x_6528_ = v___x_6516_;
goto v_reusejp_6527_;
}
else
{
lean_object* v_reuseFailAlloc_6529_; 
v_reuseFailAlloc_6529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6529_, 0, v_snd_6519_);
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
lean_object* v_a_6534_; lean_object* v___x_6536_; uint8_t v_isShared_6537_; uint8_t v_isSharedCheck_6541_; 
lean_del_object(v___x_6511_);
lean_dec(v_val_6509_);
v_a_6534_ = lean_ctor_get(v___x_6513_, 0);
v_isSharedCheck_6541_ = !lean_is_exclusive(v___x_6513_);
if (v_isSharedCheck_6541_ == 0)
{
v___x_6536_ = v___x_6513_;
v_isShared_6537_ = v_isSharedCheck_6541_;
goto v_resetjp_6535_;
}
else
{
lean_inc(v_a_6534_);
lean_dec(v___x_6513_);
v___x_6536_ = lean_box(0);
v_isShared_6537_ = v_isSharedCheck_6541_;
goto v_resetjp_6535_;
}
v_resetjp_6535_:
{
lean_object* v___x_6539_; 
if (v_isShared_6537_ == 0)
{
v___x_6539_ = v___x_6536_;
goto v_reusejp_6538_;
}
else
{
lean_object* v_reuseFailAlloc_6540_; 
v_reuseFailAlloc_6540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6540_, 0, v_a_6534_);
v___x_6539_ = v_reuseFailAlloc_6540_;
goto v_reusejp_6538_;
}
v_reusejp_6538_:
{
return v___x_6539_;
}
}
}
}
}
else
{
lean_object* v_a_6543_; lean_object* v___x_6544_; 
lean_dec(v_droppedEntriesRef_6497_);
v_a_6543_ = lean_ctor_get(v___x_6507_, 0);
lean_inc(v_a_6543_);
lean_dec_ref_known(v___x_6507_, 1);
v___x_6544_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_a_6543_, v_droppedKeys_6498_, v___y_6499_, v___y_6500_, v___y_6501_, v___y_6502_);
return v___x_6544_;
}
}
else
{
lean_dec(v_droppedKeys_6498_);
lean_dec(v_droppedEntriesRef_6497_);
return v___x_6507_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0___boxed(lean_object* v_a_6545_, lean_object* v___x_6546_, lean_object* v_addEntry_6547_, lean_object* v_constantsPerTask_6548_, lean_object* v_droppedEntriesRef_6549_, lean_object* v_droppedKeys_6550_, lean_object* v___y_6551_, lean_object* v___y_6552_, lean_object* v___y_6553_, lean_object* v___y_6554_, lean_object* v___y_6555_){
_start:
{
lean_object* v_res_6556_; 
v_res_6556_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0(v_a_6545_, v___x_6546_, v_addEntry_6547_, v_constantsPerTask_6548_, v_droppedEntriesRef_6549_, v_droppedKeys_6550_, v___y_6551_, v___y_6552_, v___y_6553_, v___y_6554_);
lean_dec(v___y_6554_);
lean_dec_ref(v___y_6553_);
lean_dec(v___y_6552_);
lean_dec_ref(v___y_6551_);
lean_dec(v_constantsPerTask_6548_);
lean_dec_ref(v_a_6545_);
return v_res_6556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(lean_object* v_ref_6558_, lean_object* v_addEntry_6559_, lean_object* v_droppedKeys_6560_, lean_object* v_constantsPerTask_6561_, lean_object* v_droppedEntriesRef_6562_, lean_object* v_ty_6563_, lean_object* v_a_6564_, lean_object* v_a_6565_, lean_object* v_a_6566_, lean_object* v_a_6567_){
_start:
{
lean_object* v_a_6570_; lean_object* v___x_6592_; lean_object* v_ngen_6593_; lean_object* v_namePrefix_6594_; lean_object* v_idx_6595_; lean_object* v___x_6597_; uint8_t v_isShared_6598_; uint8_t v_isSharedCheck_6641_; 
v___x_6592_ = lean_st_ref_get(v_a_6567_);
v_ngen_6593_ = lean_ctor_get(v___x_6592_, 2);
lean_inc_ref(v_ngen_6593_);
lean_dec(v___x_6592_);
v_namePrefix_6594_ = lean_ctor_get(v_ngen_6593_, 0);
v_idx_6595_ = lean_ctor_get(v_ngen_6593_, 1);
v_isSharedCheck_6641_ = !lean_is_exclusive(v_ngen_6593_);
if (v_isSharedCheck_6641_ == 0)
{
v___x_6597_ = v_ngen_6593_;
v_isShared_6598_ = v_isSharedCheck_6641_;
goto v_resetjp_6596_;
}
else
{
lean_inc(v_idx_6595_);
lean_inc(v_namePrefix_6594_);
lean_dec(v_ngen_6593_);
v___x_6597_ = lean_box(0);
v_isShared_6598_ = v_isSharedCheck_6641_;
goto v_resetjp_6596_;
}
v___jp_6569_:
{
lean_object* v___x_6571_; 
v___x_6571_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v_a_6570_, v_ty_6563_, v_a_6564_, v_a_6565_, v_a_6566_, v_a_6567_);
if (lean_obj_tag(v___x_6571_) == 0)
{
lean_object* v_a_6572_; lean_object* v___x_6574_; uint8_t v_isShared_6575_; uint8_t v_isSharedCheck_6583_; 
v_a_6572_ = lean_ctor_get(v___x_6571_, 0);
v_isSharedCheck_6583_ = !lean_is_exclusive(v___x_6571_);
if (v_isSharedCheck_6583_ == 0)
{
v___x_6574_ = v___x_6571_;
v_isShared_6575_ = v_isSharedCheck_6583_;
goto v_resetjp_6573_;
}
else
{
lean_inc(v_a_6572_);
lean_dec(v___x_6571_);
v___x_6574_ = lean_box(0);
v_isShared_6575_ = v_isSharedCheck_6583_;
goto v_resetjp_6573_;
}
v_resetjp_6573_:
{
lean_object* v_fst_6576_; lean_object* v_snd_6577_; lean_object* v___x_6578_; lean_object* v___x_6579_; lean_object* v___x_6581_; 
v_fst_6576_ = lean_ctor_get(v_a_6572_, 0);
lean_inc(v_fst_6576_);
v_snd_6577_ = lean_ctor_get(v_a_6572_, 1);
lean_inc(v_snd_6577_);
lean_dec(v_a_6572_);
v___x_6578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6578_, 0, v_snd_6577_);
v___x_6579_ = lean_st_ref_swap(v_ref_6558_, v___x_6578_);
lean_dec(v___x_6579_);
if (v_isShared_6575_ == 0)
{
lean_ctor_set(v___x_6574_, 0, v_fst_6576_);
v___x_6581_ = v___x_6574_;
goto v_reusejp_6580_;
}
else
{
lean_object* v_reuseFailAlloc_6582_; 
v_reuseFailAlloc_6582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6582_, 0, v_fst_6576_);
v___x_6581_ = v_reuseFailAlloc_6582_;
goto v_reusejp_6580_;
}
v_reusejp_6580_:
{
return v___x_6581_;
}
}
}
else
{
lean_object* v_a_6584_; lean_object* v___x_6586_; uint8_t v_isShared_6587_; uint8_t v_isSharedCheck_6591_; 
v_a_6584_ = lean_ctor_get(v___x_6571_, 0);
v_isSharedCheck_6591_ = !lean_is_exclusive(v___x_6571_);
if (v_isSharedCheck_6591_ == 0)
{
v___x_6586_ = v___x_6571_;
v_isShared_6587_ = v_isSharedCheck_6591_;
goto v_resetjp_6585_;
}
else
{
lean_inc(v_a_6584_);
lean_dec(v___x_6571_);
v___x_6586_ = lean_box(0);
v_isShared_6587_ = v_isSharedCheck_6591_;
goto v_resetjp_6585_;
}
v_resetjp_6585_:
{
lean_object* v___x_6589_; 
if (v_isShared_6587_ == 0)
{
v___x_6589_ = v___x_6586_;
goto v_reusejp_6588_;
}
else
{
lean_object* v_reuseFailAlloc_6590_; 
v_reuseFailAlloc_6590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6590_, 0, v_a_6584_);
v___x_6589_ = v_reuseFailAlloc_6590_;
goto v_reusejp_6588_;
}
v_reusejp_6588_:
{
return v___x_6589_;
}
}
}
}
v_resetjp_6596_:
{
lean_object* v___x_6599_; lean_object* v___x_6600_; lean_object* v___x_6602_; 
lean_inc(v_idx_6595_);
lean_inc(v_namePrefix_6594_);
v___x_6599_ = l_Lean_Name_num___override(v_namePrefix_6594_, v_idx_6595_);
v___x_6600_ = lean_unsigned_to_nat(1u);
if (v_isShared_6598_ == 0)
{
lean_ctor_set(v___x_6597_, 1, v___x_6600_);
lean_ctor_set(v___x_6597_, 0, v___x_6599_);
v___x_6602_ = v___x_6597_;
goto v_reusejp_6601_;
}
else
{
lean_object* v_reuseFailAlloc_6640_; 
v_reuseFailAlloc_6640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6640_, 0, v___x_6599_);
lean_ctor_set(v_reuseFailAlloc_6640_, 1, v___x_6600_);
v___x_6602_ = v_reuseFailAlloc_6640_;
goto v_reusejp_6601_;
}
v_reusejp_6601_:
{
lean_object* v___f_6603_; lean_object* v___x_6604_; lean_object* v___x_6605_; lean_object* v___x_6606_; lean_object* v_env_6607_; lean_object* v_nextMacroScope_6608_; lean_object* v_auxDeclNGen_6609_; lean_object* v_traceState_6610_; lean_object* v_cache_6611_; lean_object* v_recordedDeps_6612_; lean_object* v_messages_6613_; lean_object* v_infoState_6614_; lean_object* v_snapshotTasks_6615_; lean_object* v___x_6617_; uint8_t v_isShared_6618_; uint8_t v_isSharedCheck_6638_; 
lean_inc_ref(v_a_6566_);
v___f_6603_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_6603_, 0, v_a_6566_);
lean_closure_set(v___f_6603_, 1, v___x_6602_);
lean_closure_set(v___f_6603_, 2, v_addEntry_6559_);
lean_closure_set(v___f_6603_, 3, v_constantsPerTask_6561_);
lean_closure_set(v___f_6603_, 4, v_droppedEntriesRef_6562_);
lean_closure_set(v___f_6603_, 5, v_droppedKeys_6560_);
v___x_6604_ = lean_nat_add(v_idx_6595_, v___x_6600_);
lean_dec(v_idx_6595_);
v___x_6605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6605_, 0, v_namePrefix_6594_);
lean_ctor_set(v___x_6605_, 1, v___x_6604_);
v___x_6606_ = lean_st_ref_take(v_a_6567_);
v_env_6607_ = lean_ctor_get(v___x_6606_, 0);
v_nextMacroScope_6608_ = lean_ctor_get(v___x_6606_, 1);
v_auxDeclNGen_6609_ = lean_ctor_get(v___x_6606_, 3);
v_traceState_6610_ = lean_ctor_get(v___x_6606_, 4);
v_cache_6611_ = lean_ctor_get(v___x_6606_, 5);
v_recordedDeps_6612_ = lean_ctor_get(v___x_6606_, 6);
v_messages_6613_ = lean_ctor_get(v___x_6606_, 7);
v_infoState_6614_ = lean_ctor_get(v___x_6606_, 8);
v_snapshotTasks_6615_ = lean_ctor_get(v___x_6606_, 9);
v_isSharedCheck_6638_ = !lean_is_exclusive(v___x_6606_);
if (v_isSharedCheck_6638_ == 0)
{
lean_object* v_unused_6639_; 
v_unused_6639_ = lean_ctor_get(v___x_6606_, 2);
lean_dec(v_unused_6639_);
v___x_6617_ = v___x_6606_;
v_isShared_6618_ = v_isSharedCheck_6638_;
goto v_resetjp_6616_;
}
else
{
lean_inc(v_snapshotTasks_6615_);
lean_inc(v_infoState_6614_);
lean_inc(v_messages_6613_);
lean_inc(v_recordedDeps_6612_);
lean_inc(v_cache_6611_);
lean_inc(v_traceState_6610_);
lean_inc(v_auxDeclNGen_6609_);
lean_inc(v_nextMacroScope_6608_);
lean_inc(v_env_6607_);
lean_dec(v___x_6606_);
v___x_6617_ = lean_box(0);
v_isShared_6618_ = v_isSharedCheck_6638_;
goto v_resetjp_6616_;
}
v_resetjp_6616_:
{
lean_object* v___x_6620_; 
if (v_isShared_6618_ == 0)
{
lean_ctor_set(v___x_6617_, 2, v___x_6605_);
v___x_6620_ = v___x_6617_;
goto v_reusejp_6619_;
}
else
{
lean_object* v_reuseFailAlloc_6637_; 
v_reuseFailAlloc_6637_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6637_, 0, v_env_6607_);
lean_ctor_set(v_reuseFailAlloc_6637_, 1, v_nextMacroScope_6608_);
lean_ctor_set(v_reuseFailAlloc_6637_, 2, v___x_6605_);
lean_ctor_set(v_reuseFailAlloc_6637_, 3, v_auxDeclNGen_6609_);
lean_ctor_set(v_reuseFailAlloc_6637_, 4, v_traceState_6610_);
lean_ctor_set(v_reuseFailAlloc_6637_, 5, v_cache_6611_);
lean_ctor_set(v_reuseFailAlloc_6637_, 6, v_recordedDeps_6612_);
lean_ctor_set(v_reuseFailAlloc_6637_, 7, v_messages_6613_);
lean_ctor_set(v_reuseFailAlloc_6637_, 8, v_infoState_6614_);
lean_ctor_set(v_reuseFailAlloc_6637_, 9, v_snapshotTasks_6615_);
v___x_6620_ = v_reuseFailAlloc_6637_;
goto v_reusejp_6619_;
}
v_reusejp_6619_:
{
lean_object* v___x_6621_; lean_object* v___x_6622_; 
v___x_6621_ = lean_st_ref_put(v_a_6567_, v___x_6620_);
v___x_6622_ = lean_st_ref_get(v_ref_6558_);
if (lean_obj_tag(v___x_6622_) == 0)
{
lean_object* v___x_6623_; lean_object* v___x_6624_; lean_object* v___x_6625_; lean_object* v___x_6626_; 
v___x_6623_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_6566_);
v___x_6624_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___closed__0));
v___x_6625_ = lean_box(0);
v___x_6626_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v___x_6624_, v___x_6623_, v___f_6603_, v___x_6625_, v_a_6564_, v_a_6565_, v_a_6566_, v_a_6567_);
lean_dec_ref(v___x_6623_);
if (lean_obj_tag(v___x_6626_) == 0)
{
lean_object* v_a_6627_; 
v_a_6627_ = lean_ctor_get(v___x_6626_, 0);
lean_inc(v_a_6627_);
lean_dec_ref_known(v___x_6626_, 1);
v_a_6570_ = v_a_6627_;
goto v___jp_6569_;
}
else
{
lean_object* v_a_6628_; lean_object* v___x_6630_; uint8_t v_isShared_6631_; uint8_t v_isSharedCheck_6635_; 
lean_dec_ref(v_ty_6563_);
v_a_6628_ = lean_ctor_get(v___x_6626_, 0);
v_isSharedCheck_6635_ = !lean_is_exclusive(v___x_6626_);
if (v_isSharedCheck_6635_ == 0)
{
v___x_6630_ = v___x_6626_;
v_isShared_6631_ = v_isSharedCheck_6635_;
goto v_resetjp_6629_;
}
else
{
lean_inc(v_a_6628_);
lean_dec(v___x_6626_);
v___x_6630_ = lean_box(0);
v_isShared_6631_ = v_isSharedCheck_6635_;
goto v_resetjp_6629_;
}
v_resetjp_6629_:
{
lean_object* v___x_6633_; 
if (v_isShared_6631_ == 0)
{
v___x_6633_ = v___x_6630_;
goto v_reusejp_6632_;
}
else
{
lean_object* v_reuseFailAlloc_6634_; 
v_reuseFailAlloc_6634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6634_, 0, v_a_6628_);
v___x_6633_ = v_reuseFailAlloc_6634_;
goto v_reusejp_6632_;
}
v_reusejp_6632_:
{
return v___x_6633_;
}
}
}
}
else
{
lean_object* v_val_6636_; 
lean_dec_ref(v___f_6603_);
v_val_6636_ = lean_ctor_get(v___x_6622_, 0);
lean_inc(v_val_6636_);
lean_dec_ref_known(v___x_6622_, 1);
v_a_6570_ = v_val_6636_;
goto v___jp_6569_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___boxed(lean_object* v_ref_6642_, lean_object* v_addEntry_6643_, lean_object* v_droppedKeys_6644_, lean_object* v_constantsPerTask_6645_, lean_object* v_droppedEntriesRef_6646_, lean_object* v_ty_6647_, lean_object* v_a_6648_, lean_object* v_a_6649_, lean_object* v_a_6650_, lean_object* v_a_6651_, lean_object* v_a_6652_){
_start:
{
lean_object* v_res_6653_; 
v_res_6653_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(v_ref_6642_, v_addEntry_6643_, v_droppedKeys_6644_, v_constantsPerTask_6645_, v_droppedEntriesRef_6646_, v_ty_6647_, v_a_6648_, v_a_6649_, v_a_6650_, v_a_6651_);
lean_dec(v_a_6651_);
lean_dec_ref(v_a_6650_);
lean_dec(v_a_6649_);
lean_dec_ref(v_a_6648_);
lean_dec(v_ref_6642_);
return v_res_6653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches(lean_object* v_00_u03b1_6654_, lean_object* v_ref_6655_, lean_object* v_addEntry_6656_, lean_object* v_droppedKeys_6657_, lean_object* v_constantsPerTask_6658_, lean_object* v_droppedEntriesRef_6659_, lean_object* v_ty_6660_, lean_object* v_a_6661_, lean_object* v_a_6662_, lean_object* v_a_6663_, lean_object* v_a_6664_){
_start:
{
lean_object* v___x_6666_; 
v___x_6666_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(v_ref_6655_, v_addEntry_6656_, v_droppedKeys_6657_, v_constantsPerTask_6658_, v_droppedEntriesRef_6659_, v_ty_6660_, v_a_6661_, v_a_6662_, v_a_6663_, v_a_6664_);
return v___x_6666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___boxed(lean_object* v_00_u03b1_6667_, lean_object* v_ref_6668_, lean_object* v_addEntry_6669_, lean_object* v_droppedKeys_6670_, lean_object* v_constantsPerTask_6671_, lean_object* v_droppedEntriesRef_6672_, lean_object* v_ty_6673_, lean_object* v_a_6674_, lean_object* v_a_6675_, lean_object* v_a_6676_, lean_object* v_a_6677_, lean_object* v_a_6678_){
_start:
{
lean_object* v_res_6679_; 
v_res_6679_ = l_Lean_Meta_LazyDiscrTree_findImportMatches(v_00_u03b1_6667_, v_ref_6668_, v_addEntry_6669_, v_droppedKeys_6670_, v_constantsPerTask_6671_, v_droppedEntriesRef_6672_, v_ty_6673_, v_a_6674_, v_a_6675_, v_a_6676_, v_a_6677_);
lean_dec(v_a_6677_);
lean_dec_ref(v_a_6676_);
lean_dec(v_a_6675_);
lean_dec_ref(v_a_6674_);
lean_dec(v_ref_6668_);
return v_res_6679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0(lean_object* v_00_u03b1_6680_, lean_object* v_cctx_6681_, lean_object* v_ngen_6682_, lean_object* v_env_6683_, lean_object* v_act_6684_, lean_object* v_constantsPerTask_6685_, lean_object* v___y_6686_, lean_object* v___y_6687_, lean_object* v___y_6688_, lean_object* v___y_6689_){
_start:
{
lean_object* v___x_6691_; 
v___x_6691_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(v_cctx_6681_, v_ngen_6682_, v_env_6683_, v_act_6684_, v_constantsPerTask_6685_, v___y_6686_, v___y_6687_, v___y_6688_, v___y_6689_);
return v___x_6691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___boxed(lean_object* v_00_u03b1_6692_, lean_object* v_cctx_6693_, lean_object* v_ngen_6694_, lean_object* v_env_6695_, lean_object* v_act_6696_, lean_object* v_constantsPerTask_6697_, lean_object* v___y_6698_, lean_object* v___y_6699_, lean_object* v___y_6700_, lean_object* v___y_6701_, lean_object* v___y_6702_){
_start:
{
lean_object* v_res_6703_; 
v_res_6703_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0(v_00_u03b1_6692_, v_cctx_6693_, v_ngen_6694_, v_env_6695_, v_act_6696_, v_constantsPerTask_6697_, v___y_6698_, v___y_6699_, v___y_6700_, v___y_6701_);
lean_dec(v___y_6701_);
lean_dec_ref(v___y_6700_);
lean_dec(v___y_6699_);
lean_dec_ref(v___y_6698_);
lean_dec(v_constantsPerTask_6697_);
return v_res_6703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1(lean_object* v_00_u03b1_6704_, lean_object* v_cctx_6705_, lean_object* v_env_6706_, lean_object* v_act_6707_, lean_object* v_constantsPerTask_6708_, lean_object* v_n_6709_, lean_object* v_ngen_6710_, lean_object* v_tasks_6711_, lean_object* v_start_6712_, lean_object* v_cnt_6713_, lean_object* v_idx_6714_, lean_object* v___y_6715_, lean_object* v___y_6716_, lean_object* v___y_6717_, lean_object* v___y_6718_){
_start:
{
lean_object* v___x_6720_; 
v___x_6720_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(v_cctx_6705_, v_env_6706_, v_act_6707_, v_constantsPerTask_6708_, v_n_6709_, v_ngen_6710_, v_tasks_6711_, v_start_6712_, v_cnt_6713_, v_idx_6714_);
return v___x_6720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___boxed(lean_object* v_00_u03b1_6721_, lean_object* v_cctx_6722_, lean_object* v_env_6723_, lean_object* v_act_6724_, lean_object* v_constantsPerTask_6725_, lean_object* v_n_6726_, lean_object* v_ngen_6727_, lean_object* v_tasks_6728_, lean_object* v_start_6729_, lean_object* v_cnt_6730_, lean_object* v_idx_6731_, lean_object* v___y_6732_, lean_object* v___y_6733_, lean_object* v___y_6734_, lean_object* v___y_6735_, lean_object* v___y_6736_){
_start:
{
lean_object* v_res_6737_; 
v_res_6737_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1(v_00_u03b1_6721_, v_cctx_6722_, v_env_6723_, v_act_6724_, v_constantsPerTask_6725_, v_n_6726_, v_ngen_6727_, v_tasks_6728_, v_start_6729_, v_cnt_6730_, v_idx_6731_, v___y_6732_, v___y_6733_, v___y_6734_, v___y_6735_);
lean_dec(v___y_6735_);
lean_dec_ref(v___y_6734_);
lean_dec(v___y_6733_);
lean_dec_ref(v___y_6732_);
lean_dec(v_constantsPerTask_6725_);
return v_res_6737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2(lean_object* v_00_u03b1_6738_, lean_object* v_z_6739_, lean_object* v_tasks_6740_){
_start:
{
lean_object* v___x_6741_; 
v___x_6741_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(v_z_6739_, v_tasks_6740_);
return v___x_6741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___boxed(lean_object* v_00_u03b1_6742_, lean_object* v_z_6743_, lean_object* v_tasks_6744_){
_start:
{
lean_object* v_res_6745_; 
v_res_6745_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2(v_00_u03b1_6742_, v_z_6743_, v_tasks_6744_);
lean_dec_ref(v_tasks_6744_);
return v_res_6745_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5(lean_object* v_00_u03b1_6746_, lean_object* v_as_6747_, size_t v_i_6748_, size_t v_stop_6749_, lean_object* v_b_6750_){
_start:
{
lean_object* v___x_6751_; 
v___x_6751_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(v_as_6747_, v_i_6748_, v_stop_6749_, v_b_6750_);
return v___x_6751_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b1_6752_, lean_object* v_as_6753_, lean_object* v_i_6754_, lean_object* v_stop_6755_, lean_object* v_b_6756_){
_start:
{
size_t v_i_boxed_6757_; size_t v_stop_boxed_6758_; lean_object* v_res_6759_; 
v_i_boxed_6757_ = lean_unbox_usize(v_i_6754_);
lean_dec(v_i_6754_);
v_stop_boxed_6758_ = lean_unbox_usize(v_stop_6755_);
lean_dec(v_stop_6755_);
v_res_6759_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5(v_00_u03b1_6752_, v_as_6753_, v_i_boxed_6757_, v_stop_boxed_6758_, v_b_6756_);
lean_dec_ref(v_as_6753_);
return v_res_6759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(lean_object* v___y_6760_){
_start:
{
lean_object* v___x_6762_; lean_object* v_ngen_6763_; lean_object* v_namePrefix_6764_; lean_object* v_idx_6765_; lean_object* v___x_6767_; uint8_t v_isShared_6768_; uint8_t v_isSharedCheck_6796_; 
v___x_6762_ = lean_st_ref_get(v___y_6760_);
v_ngen_6763_ = lean_ctor_get(v___x_6762_, 2);
lean_inc_ref(v_ngen_6763_);
lean_dec(v___x_6762_);
v_namePrefix_6764_ = lean_ctor_get(v_ngen_6763_, 0);
v_idx_6765_ = lean_ctor_get(v_ngen_6763_, 1);
v_isSharedCheck_6796_ = !lean_is_exclusive(v_ngen_6763_);
if (v_isSharedCheck_6796_ == 0)
{
v___x_6767_ = v_ngen_6763_;
v_isShared_6768_ = v_isSharedCheck_6796_;
goto v_resetjp_6766_;
}
else
{
lean_inc(v_idx_6765_);
lean_inc(v_namePrefix_6764_);
lean_dec(v_ngen_6763_);
v___x_6767_ = lean_box(0);
v_isShared_6768_ = v_isSharedCheck_6796_;
goto v_resetjp_6766_;
}
v_resetjp_6766_:
{
lean_object* v___x_6769_; lean_object* v___x_6770_; lean_object* v___x_6772_; 
lean_inc(v_idx_6765_);
lean_inc(v_namePrefix_6764_);
v___x_6769_ = l_Lean_Name_num___override(v_namePrefix_6764_, v_idx_6765_);
v___x_6770_ = lean_unsigned_to_nat(1u);
if (v_isShared_6768_ == 0)
{
lean_ctor_set(v___x_6767_, 1, v___x_6770_);
lean_ctor_set(v___x_6767_, 0, v___x_6769_);
v___x_6772_ = v___x_6767_;
goto v_reusejp_6771_;
}
else
{
lean_object* v_reuseFailAlloc_6795_; 
v_reuseFailAlloc_6795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6795_, 0, v___x_6769_);
lean_ctor_set(v_reuseFailAlloc_6795_, 1, v___x_6770_);
v___x_6772_ = v_reuseFailAlloc_6795_;
goto v_reusejp_6771_;
}
v_reusejp_6771_:
{
lean_object* v___x_6773_; lean_object* v___x_6774_; lean_object* v___x_6775_; lean_object* v_env_6776_; lean_object* v_nextMacroScope_6777_; lean_object* v_auxDeclNGen_6778_; lean_object* v_traceState_6779_; lean_object* v_cache_6780_; lean_object* v_recordedDeps_6781_; lean_object* v_messages_6782_; lean_object* v_infoState_6783_; lean_object* v_snapshotTasks_6784_; lean_object* v___x_6786_; uint8_t v_isShared_6787_; uint8_t v_isSharedCheck_6793_; 
v___x_6773_ = lean_nat_add(v_idx_6765_, v___x_6770_);
lean_dec(v_idx_6765_);
v___x_6774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6774_, 0, v_namePrefix_6764_);
lean_ctor_set(v___x_6774_, 1, v___x_6773_);
v___x_6775_ = lean_st_ref_take(v___y_6760_);
v_env_6776_ = lean_ctor_get(v___x_6775_, 0);
v_nextMacroScope_6777_ = lean_ctor_get(v___x_6775_, 1);
v_auxDeclNGen_6778_ = lean_ctor_get(v___x_6775_, 3);
v_traceState_6779_ = lean_ctor_get(v___x_6775_, 4);
v_cache_6780_ = lean_ctor_get(v___x_6775_, 5);
v_recordedDeps_6781_ = lean_ctor_get(v___x_6775_, 6);
v_messages_6782_ = lean_ctor_get(v___x_6775_, 7);
v_infoState_6783_ = lean_ctor_get(v___x_6775_, 8);
v_snapshotTasks_6784_ = lean_ctor_get(v___x_6775_, 9);
v_isSharedCheck_6793_ = !lean_is_exclusive(v___x_6775_);
if (v_isSharedCheck_6793_ == 0)
{
lean_object* v_unused_6794_; 
v_unused_6794_ = lean_ctor_get(v___x_6775_, 2);
lean_dec(v_unused_6794_);
v___x_6786_ = v___x_6775_;
v_isShared_6787_ = v_isSharedCheck_6793_;
goto v_resetjp_6785_;
}
else
{
lean_inc(v_snapshotTasks_6784_);
lean_inc(v_infoState_6783_);
lean_inc(v_messages_6782_);
lean_inc(v_recordedDeps_6781_);
lean_inc(v_cache_6780_);
lean_inc(v_traceState_6779_);
lean_inc(v_auxDeclNGen_6778_);
lean_inc(v_nextMacroScope_6777_);
lean_inc(v_env_6776_);
lean_dec(v___x_6775_);
v___x_6786_ = lean_box(0);
v_isShared_6787_ = v_isSharedCheck_6793_;
goto v_resetjp_6785_;
}
v_resetjp_6785_:
{
lean_object* v___x_6789_; 
if (v_isShared_6787_ == 0)
{
lean_ctor_set(v___x_6786_, 2, v___x_6774_);
v___x_6789_ = v___x_6786_;
goto v_reusejp_6788_;
}
else
{
lean_object* v_reuseFailAlloc_6792_; 
v_reuseFailAlloc_6792_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6792_, 0, v_env_6776_);
lean_ctor_set(v_reuseFailAlloc_6792_, 1, v_nextMacroScope_6777_);
lean_ctor_set(v_reuseFailAlloc_6792_, 2, v___x_6774_);
lean_ctor_set(v_reuseFailAlloc_6792_, 3, v_auxDeclNGen_6778_);
lean_ctor_set(v_reuseFailAlloc_6792_, 4, v_traceState_6779_);
lean_ctor_set(v_reuseFailAlloc_6792_, 5, v_cache_6780_);
lean_ctor_set(v_reuseFailAlloc_6792_, 6, v_recordedDeps_6781_);
lean_ctor_set(v_reuseFailAlloc_6792_, 7, v_messages_6782_);
lean_ctor_set(v_reuseFailAlloc_6792_, 8, v_infoState_6783_);
lean_ctor_set(v_reuseFailAlloc_6792_, 9, v_snapshotTasks_6784_);
v___x_6789_ = v_reuseFailAlloc_6792_;
goto v_reusejp_6788_;
}
v_reusejp_6788_:
{
lean_object* v___x_6790_; lean_object* v___x_6791_; 
v___x_6790_ = lean_st_ref_put(v___y_6760_, v___x_6789_);
v___x_6791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6791_, 0, v___x_6772_);
return v___x_6791_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg___boxed(lean_object* v___y_6797_, lean_object* v___y_6798_){
_start:
{
lean_object* v_res_6799_; 
v_res_6799_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(v___y_6797_);
lean_dec(v___y_6797_);
return v_res_6799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1(lean_object* v___y_6800_, lean_object* v___y_6801_){
_start:
{
lean_object* v___x_6803_; 
v___x_6803_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(v___y_6801_);
return v___x_6803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___boxed(lean_object* v___y_6804_, lean_object* v___y_6805_, lean_object* v___y_6806_){
_start:
{
lean_object* v_res_6807_; 
v_res_6807_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1(v___y_6804_, v___y_6805_);
lean_dec(v___y_6805_);
lean_dec_ref(v___y_6804_);
return v_res_6807_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0(void){
_start:
{
lean_object* v___x_6808_; lean_object* v___x_6809_; lean_object* v___x_6810_; 
v___x_6808_ = lean_unsigned_to_nat(32u);
v___x_6809_ = lean_mk_empty_array_with_capacity(v___x_6808_);
v___x_6810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6810_, 0, v___x_6809_);
return v___x_6810_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1(void){
_start:
{
size_t v___x_6811_; lean_object* v___x_6812_; lean_object* v___x_6813_; lean_object* v___x_6814_; lean_object* v___x_6815_; lean_object* v___x_6816_; 
v___x_6811_ = ((size_t)5ULL);
v___x_6812_ = lean_unsigned_to_nat(0u);
v___x_6813_ = lean_unsigned_to_nat(32u);
v___x_6814_ = lean_mk_empty_array_with_capacity(v___x_6813_);
v___x_6815_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0);
v___x_6816_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_6816_, 0, v___x_6815_);
lean_ctor_set(v___x_6816_, 1, v___x_6814_);
lean_ctor_set(v___x_6816_, 2, v___x_6812_);
lean_ctor_set(v___x_6816_, 3, v___x_6812_);
lean_ctor_set_usize(v___x_6816_, 4, v___x_6811_);
return v___x_6816_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2(void){
_start:
{
lean_object* v___x_6817_; lean_object* v___x_6818_; lean_object* v___x_6819_; lean_object* v___x_6820_; 
v___x_6817_ = lean_box(1);
v___x_6818_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1);
v___x_6819_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0);
v___x_6820_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6820_, 0, v___x_6819_);
lean_ctor_set(v___x_6820_, 1, v___x_6818_);
lean_ctor_set(v___x_6820_, 2, v___x_6817_);
return v___x_6820_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_msgData_6821_, lean_object* v___y_6822_, lean_object* v___y_6823_){
_start:
{
lean_object* v___x_6825_; lean_object* v_toCold_6826_; lean_object* v_env_6827_; lean_object* v_options_6828_; uint8_t v___x_6829_; lean_object* v_env_6830_; lean_object* v___x_6831_; lean_object* v___x_6832_; lean_object* v___x_6833_; lean_object* v___x_6834_; lean_object* v___x_6835_; 
v___x_6825_ = lean_st_ref_get(v___y_6823_);
v_toCold_6826_ = lean_ctor_get(v___y_6822_, 0);
v_env_6827_ = lean_ctor_get(v___x_6825_, 0);
lean_inc_ref(v_env_6827_);
lean_dec(v___x_6825_);
v_options_6828_ = lean_ctor_get(v_toCold_6826_, 2);
v___x_6829_ = 0;
v_env_6830_ = l_Lean_Environment_setRecordingDeps(v_env_6827_, v___x_6829_);
v___x_6831_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_6832_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2);
lean_inc_ref(v_options_6828_);
v___x_6833_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6833_, 0, v_env_6830_);
lean_ctor_set(v___x_6833_, 1, v___x_6831_);
lean_ctor_set(v___x_6833_, 2, v___x_6832_);
lean_ctor_set(v___x_6833_, 3, v_options_6828_);
v___x_6834_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_6834_, 0, v___x_6833_);
lean_ctor_set(v___x_6834_, 1, v_msgData_6821_);
v___x_6835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6835_, 0, v___x_6834_);
return v___x_6835_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(lean_object* v_msgData_6836_, lean_object* v___y_6837_, lean_object* v___y_6838_, lean_object* v___y_6839_){
_start:
{
lean_object* v_res_6840_; 
v_res_6840_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5(v_msgData_6836_, v___y_6837_, v___y_6838_);
lean_dec(v___y_6838_);
lean_dec_ref(v___y_6837_);
return v_res_6840_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4(lean_object* v_ref_6841_, lean_object* v_msgData_6842_, uint8_t v_severity_6843_, uint8_t v_isSilent_6844_, lean_object* v___y_6845_, lean_object* v___y_6846_){
_start:
{
lean_object* v___y_6849_; lean_object* v___y_6850_; lean_object* v___y_6851_; uint8_t v___y_6852_; lean_object* v___y_6853_; lean_object* v___y_6854_; uint8_t v___y_6855_; lean_object* v_toCold_6856_; lean_object* v___y_6857_; lean_object* v___y_6886_; lean_object* v___y_6887_; lean_object* v___y_6888_; uint8_t v___y_6889_; lean_object* v___y_6890_; uint8_t v___y_6891_; uint8_t v___y_6892_; lean_object* v___y_6893_; lean_object* v___y_6913_; lean_object* v___y_6914_; uint8_t v___y_6915_; lean_object* v___y_6916_; uint8_t v___y_6917_; uint8_t v___y_6918_; lean_object* v___y_6919_; uint8_t v___y_6923_; uint8_t v___y_6924_; uint8_t v___y_6925_; uint8_t v___x_6936_; uint8_t v___y_6938_; uint8_t v___y_6939_; uint8_t v___y_6940_; uint8_t v___y_6942_; uint8_t v___x_6950_; 
v___x_6936_ = 2;
v___x_6950_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6843_, v___x_6936_);
if (v___x_6950_ == 0)
{
v___y_6942_ = v___x_6950_;
goto v___jp_6941_;
}
else
{
uint8_t v___x_6951_; 
lean_inc_ref(v_msgData_6842_);
v___x_6951_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_6842_);
v___y_6942_ = v___x_6951_;
goto v___jp_6941_;
}
v___jp_6848_:
{
lean_object* v_currNamespace_6858_; lean_object* v_openDecls_6859_; lean_object* v___x_6860_; lean_object* v___x_6861_; lean_object* v___x_6862_; lean_object* v___x_6863_; lean_object* v_env_6864_; lean_object* v_nextMacroScope_6865_; lean_object* v_ngen_6866_; lean_object* v_auxDeclNGen_6867_; lean_object* v_traceState_6868_; lean_object* v_cache_6869_; lean_object* v_recordedDeps_6870_; lean_object* v_messages_6871_; lean_object* v_infoState_6872_; lean_object* v_snapshotTasks_6873_; lean_object* v___x_6875_; uint8_t v_isShared_6876_; uint8_t v_isSharedCheck_6884_; 
v_currNamespace_6858_ = lean_ctor_get(v_toCold_6856_, 4);
v_openDecls_6859_ = lean_ctor_get(v_toCold_6856_, 5);
lean_inc(v_openDecls_6859_);
lean_inc(v_currNamespace_6858_);
v___x_6860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6860_, 0, v_currNamespace_6858_);
lean_ctor_set(v___x_6860_, 1, v_openDecls_6859_);
v___x_6861_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6861_, 0, v___x_6860_);
lean_ctor_set(v___x_6861_, 1, v___y_6850_);
lean_inc_ref(v___y_6854_);
lean_inc_ref(v___y_6851_);
v___x_6862_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_6862_, 0, v___y_6851_);
lean_ctor_set(v___x_6862_, 1, v___y_6853_);
lean_ctor_set(v___x_6862_, 2, v___y_6849_);
lean_ctor_set(v___x_6862_, 3, v___y_6854_);
lean_ctor_set(v___x_6862_, 4, v___x_6861_);
lean_ctor_set_uint8(v___x_6862_, sizeof(void*)*5, v___y_6855_);
lean_ctor_set_uint8(v___x_6862_, sizeof(void*)*5 + 1, v___y_6852_);
lean_ctor_set_uint8(v___x_6862_, sizeof(void*)*5 + 2, v_isSilent_6844_);
v___x_6863_ = lean_st_ref_take(v___y_6857_);
v_env_6864_ = lean_ctor_get(v___x_6863_, 0);
v_nextMacroScope_6865_ = lean_ctor_get(v___x_6863_, 1);
v_ngen_6866_ = lean_ctor_get(v___x_6863_, 2);
v_auxDeclNGen_6867_ = lean_ctor_get(v___x_6863_, 3);
v_traceState_6868_ = lean_ctor_get(v___x_6863_, 4);
v_cache_6869_ = lean_ctor_get(v___x_6863_, 5);
v_recordedDeps_6870_ = lean_ctor_get(v___x_6863_, 6);
v_messages_6871_ = lean_ctor_get(v___x_6863_, 7);
v_infoState_6872_ = lean_ctor_get(v___x_6863_, 8);
v_snapshotTasks_6873_ = lean_ctor_get(v___x_6863_, 9);
v_isSharedCheck_6884_ = !lean_is_exclusive(v___x_6863_);
if (v_isSharedCheck_6884_ == 0)
{
v___x_6875_ = v___x_6863_;
v_isShared_6876_ = v_isSharedCheck_6884_;
goto v_resetjp_6874_;
}
else
{
lean_inc(v_snapshotTasks_6873_);
lean_inc(v_infoState_6872_);
lean_inc(v_messages_6871_);
lean_inc(v_recordedDeps_6870_);
lean_inc(v_cache_6869_);
lean_inc(v_traceState_6868_);
lean_inc(v_auxDeclNGen_6867_);
lean_inc(v_ngen_6866_);
lean_inc(v_nextMacroScope_6865_);
lean_inc(v_env_6864_);
lean_dec(v___x_6863_);
v___x_6875_ = lean_box(0);
v_isShared_6876_ = v_isSharedCheck_6884_;
goto v_resetjp_6874_;
}
v_resetjp_6874_:
{
lean_object* v___x_6877_; lean_object* v___x_6878_; lean_object* v___x_6880_; 
v___x_6877_ = lean_box(0);
v___x_6878_ = l_Lean_MessageLog_add(v___x_6862_, v_messages_6871_);
if (v_isShared_6876_ == 0)
{
lean_ctor_set(v___x_6875_, 7, v___x_6878_);
v___x_6880_ = v___x_6875_;
goto v_reusejp_6879_;
}
else
{
lean_object* v_reuseFailAlloc_6883_; 
v_reuseFailAlloc_6883_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6883_, 0, v_env_6864_);
lean_ctor_set(v_reuseFailAlloc_6883_, 1, v_nextMacroScope_6865_);
lean_ctor_set(v_reuseFailAlloc_6883_, 2, v_ngen_6866_);
lean_ctor_set(v_reuseFailAlloc_6883_, 3, v_auxDeclNGen_6867_);
lean_ctor_set(v_reuseFailAlloc_6883_, 4, v_traceState_6868_);
lean_ctor_set(v_reuseFailAlloc_6883_, 5, v_cache_6869_);
lean_ctor_set(v_reuseFailAlloc_6883_, 6, v_recordedDeps_6870_);
lean_ctor_set(v_reuseFailAlloc_6883_, 7, v___x_6878_);
lean_ctor_set(v_reuseFailAlloc_6883_, 8, v_infoState_6872_);
lean_ctor_set(v_reuseFailAlloc_6883_, 9, v_snapshotTasks_6873_);
v___x_6880_ = v_reuseFailAlloc_6883_;
goto v_reusejp_6879_;
}
v_reusejp_6879_:
{
lean_object* v___x_6881_; lean_object* v___x_6882_; 
v___x_6881_ = lean_st_ref_put(v___y_6857_, v___x_6880_);
v___x_6882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6882_, 0, v___x_6877_);
return v___x_6882_;
}
}
}
v___jp_6885_:
{
lean_object* v_fileName_6894_; lean_object* v_fileMap_6895_; lean_object* v___x_6896_; lean_object* v___x_6897_; lean_object* v_a_6898_; lean_object* v___x_6900_; uint8_t v_isShared_6901_; uint8_t v_isSharedCheck_6911_; 
v_fileName_6894_ = lean_ctor_get(v___y_6888_, 0);
v_fileMap_6895_ = lean_ctor_get(v___y_6888_, 1);
v___x_6896_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_6842_);
v___x_6897_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5(v___x_6896_, v___y_6845_, v___y_6846_);
v_a_6898_ = lean_ctor_get(v___x_6897_, 0);
v_isSharedCheck_6911_ = !lean_is_exclusive(v___x_6897_);
if (v_isSharedCheck_6911_ == 0)
{
v___x_6900_ = v___x_6897_;
v_isShared_6901_ = v_isSharedCheck_6911_;
goto v_resetjp_6899_;
}
else
{
lean_inc(v_a_6898_);
lean_dec(v___x_6897_);
v___x_6900_ = lean_box(0);
v_isShared_6901_ = v_isSharedCheck_6911_;
goto v_resetjp_6899_;
}
v_resetjp_6899_:
{
lean_object* v___x_6902_; lean_object* v___x_6903_; lean_object* v___x_6904_; lean_object* v___x_6905_; 
lean_inc_ref_n(v_fileMap_6895_, 2);
v___x_6902_ = l_Lean_FileMap_toPosition(v_fileMap_6895_, v___y_6890_);
lean_dec(v___y_6890_);
v___x_6903_ = l_Lean_FileMap_toPosition(v_fileMap_6895_, v___y_6893_);
lean_dec(v___y_6893_);
v___x_6904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6904_, 0, v___x_6903_);
v___x_6905_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___closed__0));
if (v___y_6891_ == 0)
{
lean_del_object(v___x_6900_);
lean_dec_ref(v___y_6886_);
v___y_6849_ = v___x_6904_;
v___y_6850_ = v_a_6898_;
v___y_6851_ = v_fileName_6894_;
v___y_6852_ = v___y_6889_;
v___y_6853_ = v___x_6902_;
v___y_6854_ = v___x_6905_;
v___y_6855_ = v___y_6892_;
v_toCold_6856_ = v___y_6887_;
v___y_6857_ = v___y_6846_;
goto v___jp_6848_;
}
else
{
uint8_t v___x_6906_; 
lean_inc(v_a_6898_);
v___x_6906_ = l_Lean_MessageData_hasTag(v___y_6886_, v_a_6898_);
if (v___x_6906_ == 0)
{
lean_object* v___x_6907_; lean_object* v___x_6909_; 
lean_dec_ref_known(v___x_6904_, 1);
lean_dec_ref(v___x_6902_);
lean_dec(v_a_6898_);
v___x_6907_ = lean_box(0);
if (v_isShared_6901_ == 0)
{
lean_ctor_set(v___x_6900_, 0, v___x_6907_);
v___x_6909_ = v___x_6900_;
goto v_reusejp_6908_;
}
else
{
lean_object* v_reuseFailAlloc_6910_; 
v_reuseFailAlloc_6910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6910_, 0, v___x_6907_);
v___x_6909_ = v_reuseFailAlloc_6910_;
goto v_reusejp_6908_;
}
v_reusejp_6908_:
{
return v___x_6909_;
}
}
else
{
lean_del_object(v___x_6900_);
v___y_6849_ = v___x_6904_;
v___y_6850_ = v_a_6898_;
v___y_6851_ = v_fileName_6894_;
v___y_6852_ = v___y_6889_;
v___y_6853_ = v___x_6902_;
v___y_6854_ = v___x_6905_;
v___y_6855_ = v___y_6892_;
v_toCold_6856_ = v___y_6887_;
v___y_6857_ = v___y_6846_;
goto v___jp_6848_;
}
}
}
}
v___jp_6912_:
{
lean_object* v___x_6920_; 
v___x_6920_ = l_Lean_Syntax_getTailPos_x3f(v___y_6916_, v___y_6918_);
lean_dec(v___y_6916_);
if (lean_obj_tag(v___x_6920_) == 0)
{
lean_inc(v___y_6919_);
v___y_6886_ = v___y_6913_;
v___y_6887_ = v___y_6914_;
v___y_6888_ = v___y_6914_;
v___y_6889_ = v___y_6917_;
v___y_6890_ = v___y_6919_;
v___y_6891_ = v___y_6915_;
v___y_6892_ = v___y_6918_;
v___y_6893_ = v___y_6919_;
goto v___jp_6885_;
}
else
{
lean_object* v_val_6921_; 
v_val_6921_ = lean_ctor_get(v___x_6920_, 0);
lean_inc(v_val_6921_);
lean_dec_ref_known(v___x_6920_, 1);
v___y_6886_ = v___y_6913_;
v___y_6887_ = v___y_6914_;
v___y_6888_ = v___y_6914_;
v___y_6889_ = v___y_6917_;
v___y_6890_ = v___y_6919_;
v___y_6891_ = v___y_6915_;
v___y_6892_ = v___y_6918_;
v___y_6893_ = v_val_6921_;
goto v___jp_6885_;
}
}
v___jp_6922_:
{
lean_object* v_toCold_6926_; lean_object* v_ref_6927_; uint8_t v_suppressElabErrors_6928_; lean_object* v___x_6929_; lean_object* v___x_6930_; lean_object* v___f_6931_; lean_object* v_ref_6932_; lean_object* v___x_6933_; 
v_toCold_6926_ = lean_ctor_get(v___y_6845_, 0);
v_ref_6927_ = lean_ctor_get(v___y_6845_, 2);
v_suppressElabErrors_6928_ = lean_ctor_get_uint8(v___y_6845_, sizeof(void*)*3 + 2);
v___x_6929_ = lean_box(v_suppressElabErrors_6928_);
v___x_6930_ = lean_box(v___y_6923_);
v___f_6931_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_6931_, 0, v___x_6929_);
lean_closure_set(v___f_6931_, 1, v___x_6930_);
v_ref_6932_ = l_Lean_replaceRef(v_ref_6841_, v_ref_6927_);
v___x_6933_ = l_Lean_Syntax_getPos_x3f(v_ref_6932_, v___y_6924_);
if (lean_obj_tag(v___x_6933_) == 0)
{
lean_object* v___x_6934_; 
v___x_6934_ = lean_unsigned_to_nat(0u);
v___y_6913_ = v___f_6931_;
v___y_6914_ = v_toCold_6926_;
v___y_6915_ = v_suppressElabErrors_6928_;
v___y_6916_ = v_ref_6932_;
v___y_6917_ = v___y_6925_;
v___y_6918_ = v___y_6924_;
v___y_6919_ = v___x_6934_;
goto v___jp_6912_;
}
else
{
lean_object* v_val_6935_; 
v_val_6935_ = lean_ctor_get(v___x_6933_, 0);
lean_inc(v_val_6935_);
lean_dec_ref_known(v___x_6933_, 1);
v___y_6913_ = v___f_6931_;
v___y_6914_ = v_toCold_6926_;
v___y_6915_ = v_suppressElabErrors_6928_;
v___y_6916_ = v_ref_6932_;
v___y_6917_ = v___y_6925_;
v___y_6918_ = v___y_6924_;
v___y_6919_ = v_val_6935_;
goto v___jp_6912_;
}
}
v___jp_6937_:
{
if (v___y_6940_ == 0)
{
v___y_6923_ = v___y_6938_;
v___y_6924_ = v___y_6939_;
v___y_6925_ = v_severity_6843_;
goto v___jp_6922_;
}
else
{
v___y_6923_ = v___y_6938_;
v___y_6924_ = v___y_6939_;
v___y_6925_ = v___x_6936_;
goto v___jp_6922_;
}
}
v___jp_6941_:
{
if (v___y_6942_ == 0)
{
uint8_t v___x_6943_; uint8_t v___x_6944_; 
v___x_6943_ = 1;
v___x_6944_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6843_, v___x_6943_);
if (v___x_6944_ == 0)
{
v___y_6938_ = v___y_6942_;
v___y_6939_ = v___y_6942_;
v___y_6940_ = v___x_6944_;
goto v___jp_6937_;
}
else
{
lean_object* v___x_6945_; lean_object* v___x_6946_; uint8_t v___x_6947_; 
v___x_6945_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_6845_);
v___x_6946_ = l_Lean_warningAsError;
v___x_6947_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7_spec__9(v___x_6945_, v___x_6946_);
lean_dec_ref(v___x_6945_);
v___y_6938_ = v___y_6942_;
v___y_6939_ = v___y_6942_;
v___y_6940_ = v___x_6947_;
goto v___jp_6937_;
}
}
else
{
lean_object* v___x_6948_; lean_object* v___x_6949_; 
lean_dec_ref(v_msgData_6842_);
v___x_6948_ = lean_box(0);
v___x_6949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6949_, 0, v___x_6948_);
return v___x_6949_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_ref_6952_, lean_object* v_msgData_6953_, lean_object* v_severity_6954_, lean_object* v_isSilent_6955_, lean_object* v___y_6956_, lean_object* v___y_6957_, lean_object* v___y_6958_){
_start:
{
uint8_t v_severity_boxed_6959_; uint8_t v_isSilent_boxed_6960_; lean_object* v_res_6961_; 
v_severity_boxed_6959_ = lean_unbox(v_severity_6954_);
v_isSilent_boxed_6960_ = lean_unbox(v_isSilent_6955_);
v_res_6961_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4(v_ref_6952_, v_msgData_6953_, v_severity_boxed_6959_, v_isSilent_boxed_6960_, v___y_6956_, v___y_6957_);
lean_dec(v___y_6957_);
lean_dec_ref(v___y_6956_);
lean_dec(v_ref_6952_);
return v_res_6961_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2(lean_object* v_msgData_6962_, uint8_t v_severity_6963_, uint8_t v_isSilent_6964_, lean_object* v___y_6965_, lean_object* v___y_6966_){
_start:
{
lean_object* v_ref_6968_; lean_object* v___x_6969_; 
v_ref_6968_ = lean_ctor_get(v___y_6965_, 2);
v___x_6969_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4(v_ref_6968_, v_msgData_6962_, v_severity_6963_, v_isSilent_6964_, v___y_6965_, v___y_6966_);
return v___x_6969_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_6970_, lean_object* v_severity_6971_, lean_object* v_isSilent_6972_, lean_object* v___y_6973_, lean_object* v___y_6974_, lean_object* v___y_6975_){
_start:
{
uint8_t v_severity_boxed_6976_; uint8_t v_isSilent_boxed_6977_; lean_object* v_res_6978_; 
v_severity_boxed_6976_ = lean_unbox(v_severity_6971_);
v_isSilent_boxed_6977_ = lean_unbox(v_isSilent_6972_);
v_res_6978_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2(v_msgData_6970_, v_severity_boxed_6976_, v_isSilent_boxed_6977_, v___y_6973_, v___y_6974_);
lean_dec(v___y_6974_);
lean_dec_ref(v___y_6973_);
return v_res_6978_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0(lean_object* v_msgData_6979_, lean_object* v___y_6980_, lean_object* v___y_6981_){
_start:
{
uint8_t v___x_6983_; uint8_t v___x_6984_; lean_object* v___x_6985_; 
v___x_6983_ = 2;
v___x_6984_ = 0;
v___x_6985_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2(v_msgData_6979_, v___x_6983_, v___x_6984_, v___y_6980_, v___y_6981_);
return v___x_6985_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0___boxed(lean_object* v_msgData_6986_, lean_object* v___y_6987_, lean_object* v___y_6988_, lean_object* v___y_6989_){
_start:
{
lean_object* v_res_6990_; 
v_res_6990_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0(v_msgData_6986_, v___y_6987_, v___y_6988_);
lean_dec(v___y_6988_);
lean_dec_ref(v___y_6987_);
return v_res_6990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0(lean_object* v_f_6991_, lean_object* v___y_6992_, lean_object* v___y_6993_){
_start:
{
lean_object* v_module_6995_; lean_object* v_const_6996_; lean_object* v_exception_6997_; lean_object* v___x_6998_; lean_object* v___x_6999_; lean_object* v___x_7000_; lean_object* v___x_7001_; lean_object* v___x_7002_; lean_object* v___x_7003_; lean_object* v___x_7004_; lean_object* v___x_7005_; lean_object* v___x_7006_; lean_object* v___x_7007_; lean_object* v___x_7008_; lean_object* v___x_7009_; 
v_module_6995_ = lean_ctor_get(v_f_6991_, 0);
lean_inc(v_module_6995_);
v_const_6996_ = lean_ctor_get(v_f_6991_, 1);
lean_inc(v_const_6996_);
v_exception_6997_ = lean_ctor_get(v_f_6991_, 2);
lean_inc_ref(v_exception_6997_);
lean_dec_ref(v_f_6991_);
v___x_6998_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1);
v___x_6999_ = l_Lean_MessageData_ofName(v_const_6996_);
v___x_7000_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_7000_, 0, v___x_6998_);
lean_ctor_set(v___x_7000_, 1, v___x_6999_);
v___x_7001_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3);
v___x_7002_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_7002_, 0, v___x_7000_);
lean_ctor_set(v___x_7002_, 1, v___x_7001_);
v___x_7003_ = l_Lean_MessageData_ofName(v_module_6995_);
v___x_7004_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_7004_, 0, v___x_7002_);
lean_ctor_set(v___x_7004_, 1, v___x_7003_);
v___x_7005_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5);
v___x_7006_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_7006_, 0, v___x_7004_);
lean_ctor_set(v___x_7006_, 1, v___x_7005_);
v___x_7007_ = l_Lean_Exception_toMessageData(v_exception_6997_);
v___x_7008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_7008_, 0, v___x_7006_);
lean_ctor_set(v___x_7008_, 1, v___x_7007_);
v___x_7009_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0(v___x_7008_, v___y_6992_, v___y_6993_);
return v___x_7009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0___boxed(lean_object* v_f_7010_, lean_object* v___y_7011_, lean_object* v___y_7012_, lean_object* v___y_7013_){
_start:
{
lean_object* v_res_7014_; 
v_res_7014_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0(v_f_7010_, v___y_7011_, v___y_7012_);
lean_dec(v___y_7012_);
lean_dec_ref(v___y_7011_);
return v_res_7014_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2(lean_object* v_as_7015_, size_t v_i_7016_, size_t v_stop_7017_, lean_object* v_b_7018_, lean_object* v___y_7019_, lean_object* v___y_7020_){
_start:
{
uint8_t v___x_7022_; 
v___x_7022_ = lean_usize_dec_eq(v_i_7016_, v_stop_7017_);
if (v___x_7022_ == 0)
{
lean_object* v___x_7023_; lean_object* v___x_7024_; 
v___x_7023_ = lean_array_uget_borrowed(v_as_7015_, v_i_7016_);
lean_inc(v___x_7023_);
v___x_7024_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0(v___x_7023_, v___y_7019_, v___y_7020_);
if (lean_obj_tag(v___x_7024_) == 0)
{
lean_object* v_a_7025_; size_t v___x_7026_; size_t v___x_7027_; 
v_a_7025_ = lean_ctor_get(v___x_7024_, 0);
lean_inc(v_a_7025_);
lean_dec_ref_known(v___x_7024_, 1);
v___x_7026_ = ((size_t)1ULL);
v___x_7027_ = lean_usize_add(v_i_7016_, v___x_7026_);
v_i_7016_ = v___x_7027_;
v_b_7018_ = v_a_7025_;
goto _start;
}
else
{
return v___x_7024_;
}
}
else
{
lean_object* v___x_7029_; 
v___x_7029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7029_, 0, v_b_7018_);
return v___x_7029_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2___boxed(lean_object* v_as_7030_, lean_object* v_i_7031_, lean_object* v_stop_7032_, lean_object* v_b_7033_, lean_object* v___y_7034_, lean_object* v___y_7035_, lean_object* v___y_7036_){
_start:
{
size_t v_i_boxed_7037_; size_t v_stop_boxed_7038_; lean_object* v_res_7039_; 
v_i_boxed_7037_ = lean_unbox_usize(v_i_7031_);
lean_dec(v_i_7031_);
v_stop_boxed_7038_ = lean_unbox_usize(v_stop_7032_);
lean_dec(v_stop_7032_);
v_res_7039_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2(v_as_7030_, v_i_boxed_7037_, v_stop_boxed_7038_, v_b_7033_, v___y_7034_, v___y_7035_);
lean_dec(v___y_7035_);
lean_dec_ref(v___y_7034_);
lean_dec_ref(v_as_7030_);
return v_res_7039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(lean_object* v_entriesForConst_7040_, lean_object* v_a_7041_, lean_object* v_a_7042_){
_start:
{
lean_object* v___x_7044_; lean_object* v_env_7045_; lean_object* v___x_7046_; lean_object* v_a_7047_; lean_object* v___x_7049_; uint8_t v_isShared_7050_; uint8_t v_isSharedCheck_7080_; 
v___x_7044_ = lean_st_ref_get(v_a_7042_);
v_env_7045_ = lean_ctor_get(v___x_7044_, 0);
lean_inc_ref(v_env_7045_);
lean_dec(v___x_7044_);
v___x_7046_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(v_a_7042_);
v_a_7047_ = lean_ctor_get(v___x_7046_, 0);
v_isSharedCheck_7080_ = !lean_is_exclusive(v___x_7046_);
if (v_isSharedCheck_7080_ == 0)
{
v___x_7049_ = v___x_7046_;
v_isShared_7050_ = v_isSharedCheck_7080_;
goto v_resetjp_7048_;
}
else
{
lean_inc(v_a_7047_);
lean_dec(v___x_7046_);
v___x_7049_ = lean_box(0);
v_isShared_7050_ = v_isSharedCheck_7080_;
goto v_resetjp_7048_;
}
v_resetjp_7048_:
{
lean_object* v___x_7051_; lean_object* v___x_7052_; lean_object* v___y_7059_; lean_object* v___x_7068_; lean_object* v___x_7069_; lean_object* v___x_7070_; uint8_t v___x_7071_; 
v___x_7051_ = l_Lean_Meta_LazyDiscrTree_ImportData_new();
lean_inc_ref(v_a_7041_);
v___x_7052_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(v_a_7041_, v_a_7047_, v_env_7045_, v___x_7051_, v_entriesForConst_7040_);
v___x_7068_ = lean_st_ref_get(v___x_7051_);
lean_dec(v___x_7051_);
v___x_7069_ = lean_unsigned_to_nat(0u);
v___x_7070_ = lean_array_get_size(v___x_7068_);
v___x_7071_ = lean_nat_dec_lt(v___x_7069_, v___x_7070_);
if (v___x_7071_ == 0)
{
lean_dec(v___x_7068_);
goto v___jp_7053_;
}
else
{
lean_object* v___x_7072_; uint8_t v___x_7073_; 
v___x_7072_ = lean_box(0);
v___x_7073_ = lean_nat_dec_le(v___x_7070_, v___x_7070_);
if (v___x_7073_ == 0)
{
if (v___x_7071_ == 0)
{
lean_dec(v___x_7068_);
goto v___jp_7053_;
}
else
{
size_t v___x_7074_; size_t v___x_7075_; lean_object* v___x_7076_; 
v___x_7074_ = ((size_t)0ULL);
v___x_7075_ = lean_usize_of_nat(v___x_7070_);
v___x_7076_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2(v___x_7068_, v___x_7074_, v___x_7075_, v___x_7072_, v_a_7041_, v_a_7042_);
lean_dec(v___x_7068_);
v___y_7059_ = v___x_7076_;
goto v___jp_7058_;
}
}
else
{
size_t v___x_7077_; size_t v___x_7078_; lean_object* v___x_7079_; 
v___x_7077_ = ((size_t)0ULL);
v___x_7078_ = lean_usize_of_nat(v___x_7070_);
v___x_7079_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2(v___x_7068_, v___x_7077_, v___x_7078_, v___x_7072_, v_a_7041_, v_a_7042_);
lean_dec(v___x_7068_);
v___y_7059_ = v___x_7079_;
goto v___jp_7058_;
}
}
v___jp_7053_:
{
lean_object* v___x_7054_; lean_object* v___x_7056_; 
v___x_7054_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v___x_7052_);
if (v_isShared_7050_ == 0)
{
lean_ctor_set(v___x_7049_, 0, v___x_7054_);
v___x_7056_ = v___x_7049_;
goto v_reusejp_7055_;
}
else
{
lean_object* v_reuseFailAlloc_7057_; 
v_reuseFailAlloc_7057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7057_, 0, v___x_7054_);
v___x_7056_ = v_reuseFailAlloc_7057_;
goto v_reusejp_7055_;
}
v_reusejp_7055_:
{
return v___x_7056_;
}
}
v___jp_7058_:
{
if (lean_obj_tag(v___y_7059_) == 0)
{
lean_dec_ref_known(v___y_7059_, 1);
goto v___jp_7053_;
}
else
{
lean_object* v_a_7060_; lean_object* v___x_7062_; uint8_t v_isShared_7063_; uint8_t v_isSharedCheck_7067_; 
lean_dec_ref(v___x_7052_);
lean_del_object(v___x_7049_);
v_a_7060_ = lean_ctor_get(v___y_7059_, 0);
v_isSharedCheck_7067_ = !lean_is_exclusive(v___y_7059_);
if (v_isSharedCheck_7067_ == 0)
{
v___x_7062_ = v___y_7059_;
v_isShared_7063_ = v_isSharedCheck_7067_;
goto v_resetjp_7061_;
}
else
{
lean_inc(v_a_7060_);
lean_dec(v___y_7059_);
v___x_7062_ = lean_box(0);
v_isShared_7063_ = v_isSharedCheck_7067_;
goto v_resetjp_7061_;
}
v_resetjp_7061_:
{
lean_object* v___x_7065_; 
if (v_isShared_7063_ == 0)
{
v___x_7065_ = v___x_7062_;
goto v_reusejp_7064_;
}
else
{
lean_object* v_reuseFailAlloc_7066_; 
v_reuseFailAlloc_7066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7066_, 0, v_a_7060_);
v___x_7065_ = v_reuseFailAlloc_7066_;
goto v_reusejp_7064_;
}
v_reusejp_7064_:
{
return v___x_7065_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg___boxed(lean_object* v_entriesForConst_7081_, lean_object* v_a_7082_, lean_object* v_a_7083_, lean_object* v_a_7084_){
_start:
{
lean_object* v_res_7085_; 
v_res_7085_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(v_entriesForConst_7081_, v_a_7082_, v_a_7083_);
lean_dec(v_a_7083_);
lean_dec_ref(v_a_7082_);
return v_res_7085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree(lean_object* v_00_u03b1_7086_, lean_object* v_entriesForConst_7087_, lean_object* v_a_7088_, lean_object* v_a_7089_){
_start:
{
lean_object* v___x_7091_; 
v___x_7091_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(v_entriesForConst_7087_, v_a_7088_, v_a_7089_);
return v___x_7091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___boxed(lean_object* v_00_u03b1_7092_, lean_object* v_entriesForConst_7093_, lean_object* v_a_7094_, lean_object* v_a_7095_, lean_object* v_a_7096_){
_start:
{
lean_object* v_res_7097_; 
v_res_7097_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree(v_00_u03b1_7092_, v_entriesForConst_7093_, v_a_7094_, v_a_7095_);
lean_dec(v_a_7095_);
lean_dec_ref(v_a_7094_);
return v_res_7097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0(lean_object* v_entriesForConst_7098_, lean_object* v_droppedEntriesRef_7099_, lean_object* v_droppedKeys_7100_, lean_object* v___y_7101_, lean_object* v___y_7102_, lean_object* v___y_7103_, lean_object* v___y_7104_){
_start:
{
lean_object* v_t_7107_; lean_object* v___x_7110_; 
v___x_7110_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(v_entriesForConst_7098_, v___y_7103_, v___y_7104_);
if (lean_obj_tag(v___x_7110_) == 0)
{
if (lean_obj_tag(v_droppedEntriesRef_7099_) == 1)
{
lean_object* v_a_7111_; lean_object* v_val_7112_; lean_object* v___x_7114_; uint8_t v_isShared_7115_; uint8_t v_isSharedCheck_7138_; 
v_a_7111_ = lean_ctor_get(v___x_7110_, 0);
lean_inc(v_a_7111_);
lean_dec_ref_known(v___x_7110_, 1);
v_val_7112_ = lean_ctor_get(v_droppedEntriesRef_7099_, 0);
v_isSharedCheck_7138_ = !lean_is_exclusive(v_droppedEntriesRef_7099_);
if (v_isSharedCheck_7138_ == 0)
{
v___x_7114_ = v_droppedEntriesRef_7099_;
v_isShared_7115_ = v_isSharedCheck_7138_;
goto v_resetjp_7113_;
}
else
{
lean_inc(v_val_7112_);
lean_dec(v_droppedEntriesRef_7099_);
v___x_7114_ = lean_box(0);
v_isShared_7115_ = v_isSharedCheck_7138_;
goto v_resetjp_7113_;
}
v_resetjp_7113_:
{
lean_object* v___x_7116_; 
v___x_7116_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_a_7111_, v_droppedKeys_7100_, v___y_7101_, v___y_7102_, v___y_7103_, v___y_7104_);
lean_dec(v_droppedKeys_7100_);
if (lean_obj_tag(v___x_7116_) == 0)
{
lean_object* v_a_7117_; lean_object* v_fst_7118_; lean_object* v_snd_7119_; lean_object* v___x_7120_; lean_object* v___y_7122_; 
v_a_7117_ = lean_ctor_get(v___x_7116_, 0);
lean_inc(v_a_7117_);
lean_dec_ref_known(v___x_7116_, 1);
v_fst_7118_ = lean_ctor_get(v_a_7117_, 0);
lean_inc(v_fst_7118_);
v_snd_7119_ = lean_ctor_get(v_a_7117_, 1);
lean_inc(v_snd_7119_);
lean_dec(v_a_7117_);
v___x_7120_ = lean_st_ref_get(v_val_7112_);
if (lean_obj_tag(v___x_7120_) == 0)
{
lean_object* v___x_7128_; 
v___x_7128_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___y_7122_ = v___x_7128_;
goto v___jp_7121_;
}
else
{
lean_object* v_val_7129_; 
v_val_7129_ = lean_ctor_get(v___x_7120_, 0);
lean_inc(v_val_7129_);
lean_dec_ref_known(v___x_7120_, 1);
v___y_7122_ = v_val_7129_;
goto v___jp_7121_;
}
v___jp_7121_:
{
lean_object* v___x_7123_; lean_object* v___x_7125_; 
v___x_7123_ = l_Array_append___redArg(v___y_7122_, v_fst_7118_);
lean_dec(v_fst_7118_);
if (v_isShared_7115_ == 0)
{
lean_ctor_set(v___x_7114_, 0, v___x_7123_);
v___x_7125_ = v___x_7114_;
goto v_reusejp_7124_;
}
else
{
lean_object* v_reuseFailAlloc_7127_; 
v_reuseFailAlloc_7127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7127_, 0, v___x_7123_);
v___x_7125_ = v_reuseFailAlloc_7127_;
goto v_reusejp_7124_;
}
v_reusejp_7124_:
{
lean_object* v___x_7126_; 
v___x_7126_ = lean_st_ref_swap(v_val_7112_, v___x_7125_);
lean_dec(v_val_7112_);
lean_dec(v___x_7126_);
v_t_7107_ = v_snd_7119_;
goto v___jp_7106_;
}
}
}
else
{
lean_object* v_a_7130_; lean_object* v___x_7132_; uint8_t v_isShared_7133_; uint8_t v_isSharedCheck_7137_; 
lean_del_object(v___x_7114_);
lean_dec(v_val_7112_);
v_a_7130_ = lean_ctor_get(v___x_7116_, 0);
v_isSharedCheck_7137_ = !lean_is_exclusive(v___x_7116_);
if (v_isSharedCheck_7137_ == 0)
{
v___x_7132_ = v___x_7116_;
v_isShared_7133_ = v_isSharedCheck_7137_;
goto v_resetjp_7131_;
}
else
{
lean_inc(v_a_7130_);
lean_dec(v___x_7116_);
v___x_7132_ = lean_box(0);
v_isShared_7133_ = v_isSharedCheck_7137_;
goto v_resetjp_7131_;
}
v_resetjp_7131_:
{
lean_object* v___x_7135_; 
if (v_isShared_7133_ == 0)
{
v___x_7135_ = v___x_7132_;
goto v_reusejp_7134_;
}
else
{
lean_object* v_reuseFailAlloc_7136_; 
v_reuseFailAlloc_7136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7136_, 0, v_a_7130_);
v___x_7135_ = v_reuseFailAlloc_7136_;
goto v_reusejp_7134_;
}
v_reusejp_7134_:
{
return v___x_7135_;
}
}
}
}
}
else
{
lean_object* v_a_7139_; lean_object* v___x_7140_; 
lean_dec(v_droppedEntriesRef_7099_);
v_a_7139_ = lean_ctor_get(v___x_7110_, 0);
lean_inc(v_a_7139_);
lean_dec_ref_known(v___x_7110_, 1);
v___x_7140_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_a_7139_, v_droppedKeys_7100_, v___y_7101_, v___y_7102_, v___y_7103_, v___y_7104_);
if (lean_obj_tag(v___x_7140_) == 0)
{
lean_object* v_a_7141_; 
v_a_7141_ = lean_ctor_get(v___x_7140_, 0);
lean_inc(v_a_7141_);
lean_dec_ref_known(v___x_7140_, 1);
v_t_7107_ = v_a_7141_;
goto v___jp_7106_;
}
else
{
lean_object* v_a_7142_; lean_object* v___x_7144_; uint8_t v_isShared_7145_; uint8_t v_isSharedCheck_7149_; 
v_a_7142_ = lean_ctor_get(v___x_7140_, 0);
v_isSharedCheck_7149_ = !lean_is_exclusive(v___x_7140_);
if (v_isSharedCheck_7149_ == 0)
{
v___x_7144_ = v___x_7140_;
v_isShared_7145_ = v_isSharedCheck_7149_;
goto v_resetjp_7143_;
}
else
{
lean_inc(v_a_7142_);
lean_dec(v___x_7140_);
v___x_7144_ = lean_box(0);
v_isShared_7145_ = v_isSharedCheck_7149_;
goto v_resetjp_7143_;
}
v_resetjp_7143_:
{
lean_object* v___x_7147_; 
if (v_isShared_7145_ == 0)
{
v___x_7147_ = v___x_7144_;
goto v_reusejp_7146_;
}
else
{
lean_object* v_reuseFailAlloc_7148_; 
v_reuseFailAlloc_7148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7148_, 0, v_a_7142_);
v___x_7147_ = v_reuseFailAlloc_7148_;
goto v_reusejp_7146_;
}
v_reusejp_7146_:
{
return v___x_7147_;
}
}
}
}
}
else
{
lean_object* v_a_7150_; lean_object* v___x_7152_; uint8_t v_isShared_7153_; uint8_t v_isSharedCheck_7157_; 
lean_dec(v_droppedKeys_7100_);
lean_dec(v_droppedEntriesRef_7099_);
v_a_7150_ = lean_ctor_get(v___x_7110_, 0);
v_isSharedCheck_7157_ = !lean_is_exclusive(v___x_7110_);
if (v_isSharedCheck_7157_ == 0)
{
v___x_7152_ = v___x_7110_;
v_isShared_7153_ = v_isSharedCheck_7157_;
goto v_resetjp_7151_;
}
else
{
lean_inc(v_a_7150_);
lean_dec(v___x_7110_);
v___x_7152_ = lean_box(0);
v_isShared_7153_ = v_isSharedCheck_7157_;
goto v_resetjp_7151_;
}
v_resetjp_7151_:
{
lean_object* v___x_7155_; 
if (v_isShared_7153_ == 0)
{
v___x_7155_ = v___x_7152_;
goto v_reusejp_7154_;
}
else
{
lean_object* v_reuseFailAlloc_7156_; 
v_reuseFailAlloc_7156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7156_, 0, v_a_7150_);
v___x_7155_ = v_reuseFailAlloc_7156_;
goto v_reusejp_7154_;
}
v_reusejp_7154_:
{
return v___x_7155_;
}
}
}
v___jp_7106_:
{
lean_object* v___x_7108_; lean_object* v___x_7109_; 
v___x_7108_ = lean_st_mk_ref(v_t_7107_);
v___x_7109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7109_, 0, v___x_7108_);
return v___x_7109_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0___boxed(lean_object* v_entriesForConst_7158_, lean_object* v_droppedEntriesRef_7159_, lean_object* v_droppedKeys_7160_, lean_object* v___y_7161_, lean_object* v___y_7162_, lean_object* v___y_7163_, lean_object* v___y_7164_, lean_object* v___y_7165_){
_start:
{
lean_object* v_res_7166_; 
v_res_7166_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0(v_entriesForConst_7158_, v_droppedEntriesRef_7159_, v_droppedKeys_7160_, v___y_7161_, v___y_7162_, v___y_7163_, v___y_7164_);
lean_dec(v___y_7164_);
lean_dec_ref(v___y_7163_);
lean_dec(v___y_7162_);
lean_dec_ref(v___y_7161_);
return v_res_7166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(lean_object* v_entriesForConst_7168_, lean_object* v_droppedKeys_7169_, lean_object* v_droppedEntriesRef_7170_, lean_object* v_a_7171_, lean_object* v_a_7172_, lean_object* v_a_7173_, lean_object* v_a_7174_){
_start:
{
lean_object* v___f_7176_; lean_object* v___x_7177_; lean_object* v___x_7178_; lean_object* v___x_7179_; lean_object* v___x_7180_; 
v___f_7176_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_7176_, 0, v_entriesForConst_7168_);
lean_closure_set(v___f_7176_, 1, v_droppedEntriesRef_7170_);
lean_closure_set(v___f_7176_, 2, v_droppedKeys_7169_);
v___x_7177_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_7173_);
v___x_7178_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___closed__0));
v___x_7179_ = lean_box(0);
v___x_7180_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v___x_7178_, v___x_7177_, v___f_7176_, v___x_7179_, v_a_7171_, v_a_7172_, v_a_7173_, v_a_7174_);
lean_dec_ref(v___x_7177_);
return v___x_7180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___boxed(lean_object* v_entriesForConst_7181_, lean_object* v_droppedKeys_7182_, lean_object* v_droppedEntriesRef_7183_, lean_object* v_a_7184_, lean_object* v_a_7185_, lean_object* v_a_7186_, lean_object* v_a_7187_, lean_object* v_a_7188_){
_start:
{
lean_object* v_res_7189_; 
v_res_7189_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v_entriesForConst_7181_, v_droppedKeys_7182_, v_droppedEntriesRef_7183_, v_a_7184_, v_a_7185_, v_a_7186_, v_a_7187_);
lean_dec(v_a_7187_);
lean_dec_ref(v_a_7186_);
lean_dec(v_a_7185_);
lean_dec_ref(v_a_7184_);
return v_res_7189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef(lean_object* v_00_u03b1_7190_, lean_object* v_entriesForConst_7191_, lean_object* v_droppedKeys_7192_, lean_object* v_droppedEntriesRef_7193_, lean_object* v_a_7194_, lean_object* v_a_7195_, lean_object* v_a_7196_, lean_object* v_a_7197_){
_start:
{
lean_object* v___x_7199_; 
v___x_7199_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v_entriesForConst_7191_, v_droppedKeys_7192_, v_droppedEntriesRef_7193_, v_a_7194_, v_a_7195_, v_a_7196_, v_a_7197_);
return v___x_7199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___boxed(lean_object* v_00_u03b1_7200_, lean_object* v_entriesForConst_7201_, lean_object* v_droppedKeys_7202_, lean_object* v_droppedEntriesRef_7203_, lean_object* v_a_7204_, lean_object* v_a_7205_, lean_object* v_a_7206_, lean_object* v_a_7207_, lean_object* v_a_7208_){
_start:
{
lean_object* v_res_7209_; 
v_res_7209_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef(v_00_u03b1_7200_, v_entriesForConst_7201_, v_droppedKeys_7202_, v_droppedEntriesRef_7203_, v_a_7204_, v_a_7205_, v_a_7206_, v_a_7207_);
lean_dec(v_a_7207_);
lean_dec_ref(v_a_7206_);
lean_dec(v_a_7205_);
lean_dec_ref(v_a_7204_);
return v_res_7209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0(lean_object* v_moduleRef_7210_, lean_object* v_ty_7211_, lean_object* v___y_7212_, lean_object* v___y_7213_, lean_object* v___y_7214_, lean_object* v___y_7215_){
_start:
{
lean_object* v___x_7217_; lean_object* v___x_7218_; 
v___x_7217_ = lean_st_ref_get(v_moduleRef_7210_);
v___x_7218_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v___x_7217_, v_ty_7211_, v___y_7212_, v___y_7213_, v___y_7214_, v___y_7215_);
if (lean_obj_tag(v___x_7218_) == 0)
{
lean_object* v_a_7219_; lean_object* v___x_7221_; uint8_t v_isShared_7222_; uint8_t v_isSharedCheck_7229_; 
v_a_7219_ = lean_ctor_get(v___x_7218_, 0);
v_isSharedCheck_7229_ = !lean_is_exclusive(v___x_7218_);
if (v_isSharedCheck_7229_ == 0)
{
v___x_7221_ = v___x_7218_;
v_isShared_7222_ = v_isSharedCheck_7229_;
goto v_resetjp_7220_;
}
else
{
lean_inc(v_a_7219_);
lean_dec(v___x_7218_);
v___x_7221_ = lean_box(0);
v_isShared_7222_ = v_isSharedCheck_7229_;
goto v_resetjp_7220_;
}
v_resetjp_7220_:
{
lean_object* v_fst_7223_; lean_object* v_snd_7224_; lean_object* v___x_7225_; lean_object* v___x_7227_; 
v_fst_7223_ = lean_ctor_get(v_a_7219_, 0);
lean_inc(v_fst_7223_);
v_snd_7224_ = lean_ctor_get(v_a_7219_, 1);
lean_inc(v_snd_7224_);
lean_dec(v_a_7219_);
v___x_7225_ = lean_st_ref_swap(v_moduleRef_7210_, v_snd_7224_);
lean_dec(v___x_7225_);
if (v_isShared_7222_ == 0)
{
lean_ctor_set(v___x_7221_, 0, v_fst_7223_);
v___x_7227_ = v___x_7221_;
goto v_reusejp_7226_;
}
else
{
lean_object* v_reuseFailAlloc_7228_; 
v_reuseFailAlloc_7228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7228_, 0, v_fst_7223_);
v___x_7227_ = v_reuseFailAlloc_7228_;
goto v_reusejp_7226_;
}
v_reusejp_7226_:
{
return v___x_7227_;
}
}
}
else
{
lean_object* v_a_7230_; lean_object* v___x_7232_; uint8_t v_isShared_7233_; uint8_t v_isSharedCheck_7237_; 
v_a_7230_ = lean_ctor_get(v___x_7218_, 0);
v_isSharedCheck_7237_ = !lean_is_exclusive(v___x_7218_);
if (v_isSharedCheck_7237_ == 0)
{
v___x_7232_ = v___x_7218_;
v_isShared_7233_ = v_isSharedCheck_7237_;
goto v_resetjp_7231_;
}
else
{
lean_inc(v_a_7230_);
lean_dec(v___x_7218_);
v___x_7232_ = lean_box(0);
v_isShared_7233_ = v_isSharedCheck_7237_;
goto v_resetjp_7231_;
}
v_resetjp_7231_:
{
lean_object* v___x_7235_; 
if (v_isShared_7233_ == 0)
{
v___x_7235_ = v___x_7232_;
goto v_reusejp_7234_;
}
else
{
lean_object* v_reuseFailAlloc_7236_; 
v_reuseFailAlloc_7236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7236_, 0, v_a_7230_);
v___x_7235_ = v_reuseFailAlloc_7236_;
goto v_reusejp_7234_;
}
v_reusejp_7234_:
{
return v___x_7235_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0___boxed(lean_object* v_moduleRef_7238_, lean_object* v_ty_7239_, lean_object* v___y_7240_, lean_object* v___y_7241_, lean_object* v___y_7242_, lean_object* v___y_7243_, lean_object* v___y_7244_){
_start:
{
lean_object* v_res_7245_; 
v_res_7245_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0(v_moduleRef_7238_, v_ty_7239_, v___y_7240_, v___y_7241_, v___y_7242_, v___y_7243_);
lean_dec(v___y_7243_);
lean_dec_ref(v___y_7242_);
lean_dec(v___y_7241_);
lean_dec_ref(v___y_7240_);
lean_dec(v_moduleRef_7238_);
return v_res_7245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(lean_object* v_moduleRef_7247_, lean_object* v_ty_7248_, lean_object* v_a_7249_, lean_object* v_a_7250_, lean_object* v_a_7251_, lean_object* v_a_7252_){
_start:
{
lean_object* v___f_7254_; lean_object* v___x_7255_; lean_object* v___x_7256_; lean_object* v___x_7257_; lean_object* v___x_7258_; 
v___f_7254_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_7254_, 0, v_moduleRef_7247_);
lean_closure_set(v___f_7254_, 1, v_ty_7248_);
v___x_7255_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_7251_);
v___x_7256_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___closed__0));
v___x_7257_ = lean_box(0);
v___x_7258_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v___x_7256_, v___x_7255_, v___f_7254_, v___x_7257_, v_a_7249_, v_a_7250_, v_a_7251_, v_a_7252_);
lean_dec_ref(v___x_7255_);
return v___x_7258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___boxed(lean_object* v_moduleRef_7259_, lean_object* v_ty_7260_, lean_object* v_a_7261_, lean_object* v_a_7262_, lean_object* v_a_7263_, lean_object* v_a_7264_, lean_object* v_a_7265_){
_start:
{
lean_object* v_res_7266_; 
v_res_7266_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(v_moduleRef_7259_, v_ty_7260_, v_a_7261_, v_a_7262_, v_a_7263_, v_a_7264_);
lean_dec(v_a_7264_);
lean_dec_ref(v_a_7263_);
lean_dec(v_a_7262_);
lean_dec_ref(v_a_7261_);
return v_res_7266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches(lean_object* v_00_u03b1_7267_, lean_object* v_moduleRef_7268_, lean_object* v_ty_7269_, lean_object* v_a_7270_, lean_object* v_a_7271_, lean_object* v_a_7272_, lean_object* v_a_7273_){
_start:
{
lean_object* v___x_7275_; 
v___x_7275_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(v_moduleRef_7268_, v_ty_7269_, v_a_7270_, v_a_7271_, v_a_7272_, v_a_7273_);
return v___x_7275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___boxed(lean_object* v_00_u03b1_7276_, lean_object* v_moduleRef_7277_, lean_object* v_ty_7278_, lean_object* v_a_7279_, lean_object* v_a_7280_, lean_object* v_a_7281_, lean_object* v_a_7282_, lean_object* v_a_7283_){
_start:
{
lean_object* v_res_7284_; 
v_res_7284_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches(v_00_u03b1_7276_, v_moduleRef_7277_, v_ty_7278_, v_a_7279_, v_a_7280_, v_a_7281_, v_a_7282_);
lean_dec(v_a_7282_);
lean_dec_ref(v_a_7281_);
lean_dec(v_a_7280_);
lean_dec_ref(v_a_7279_);
return v_res_7284_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(lean_object* v_adjustResult_7285_, lean_object* v_j_7286_, size_t v_sz_7287_, size_t v_i_7288_, lean_object* v_bs_7289_){
_start:
{
uint8_t v___x_7290_; 
v___x_7290_ = lean_usize_dec_lt(v_i_7288_, v_sz_7287_);
if (v___x_7290_ == 0)
{
lean_dec(v_j_7286_);
lean_dec(v_adjustResult_7285_);
return v_bs_7289_;
}
else
{
lean_object* v_v_7291_; lean_object* v___x_7292_; lean_object* v_bs_x27_7293_; lean_object* v___x_7294_; size_t v___x_7295_; size_t v___x_7296_; lean_object* v___x_7297_; 
v_v_7291_ = lean_array_uget(v_bs_7289_, v_i_7288_);
v___x_7292_ = lean_unsigned_to_nat(0u);
v_bs_x27_7293_ = lean_array_uset(v_bs_7289_, v_i_7288_, v___x_7292_);
lean_inc(v_adjustResult_7285_);
lean_inc(v_j_7286_);
v___x_7294_ = lean_apply_2(v_adjustResult_7285_, v_j_7286_, v_v_7291_);
v___x_7295_ = ((size_t)1ULL);
v___x_7296_ = lean_usize_add(v_i_7288_, v___x_7295_);
v___x_7297_ = lean_array_uset(v_bs_x27_7293_, v_i_7288_, v___x_7294_);
v_i_7288_ = v___x_7296_;
v_bs_7289_ = v___x_7297_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg___boxed(lean_object* v_adjustResult_7299_, lean_object* v_j_7300_, lean_object* v_sz_7301_, lean_object* v_i_7302_, lean_object* v_bs_7303_){
_start:
{
size_t v_sz_boxed_7304_; size_t v_i_boxed_7305_; lean_object* v_res_7306_; 
v_sz_boxed_7304_ = lean_unbox_usize(v_sz_7301_);
lean_dec(v_sz_7301_);
v_i_boxed_7305_ = lean_unbox_usize(v_i_7302_);
lean_dec(v_i_7302_);
v_res_7306_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(v_adjustResult_7299_, v_j_7300_, v_sz_boxed_7304_, v_i_boxed_7305_, v_bs_7303_);
return v_res_7306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(lean_object* v_adjustResult_7307_, lean_object* v_j_7308_, lean_object* v_as_7309_, size_t v_i_7310_, size_t v_stop_7311_, lean_object* v_b_7312_){
_start:
{
uint8_t v___x_7313_; 
v___x_7313_ = lean_usize_dec_eq(v_i_7310_, v_stop_7311_);
if (v___x_7313_ == 0)
{
lean_object* v___x_7314_; size_t v_sz_7315_; size_t v___x_7316_; lean_object* v___x_7317_; lean_object* v___x_7318_; size_t v___x_7319_; size_t v___x_7320_; 
v___x_7314_ = lean_array_uget_borrowed(v_as_7309_, v_i_7310_);
v_sz_7315_ = lean_array_size(v___x_7314_);
v___x_7316_ = ((size_t)0ULL);
lean_inc(v___x_7314_);
lean_inc(v_j_7308_);
lean_inc(v_adjustResult_7307_);
v___x_7317_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(v_adjustResult_7307_, v_j_7308_, v_sz_7315_, v___x_7316_, v___x_7314_);
v___x_7318_ = l_Array_append___redArg(v_b_7312_, v___x_7317_);
lean_dec_ref(v___x_7317_);
v___x_7319_ = ((size_t)1ULL);
v___x_7320_ = lean_usize_add(v_i_7310_, v___x_7319_);
v_i_7310_ = v___x_7320_;
v_b_7312_ = v___x_7318_;
goto _start;
}
else
{
lean_dec(v_j_7308_);
lean_dec(v_adjustResult_7307_);
return v_b_7312_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg___boxed(lean_object* v_adjustResult_7322_, lean_object* v_j_7323_, lean_object* v_as_7324_, lean_object* v_i_7325_, lean_object* v_stop_7326_, lean_object* v_b_7327_){
_start:
{
size_t v_i_boxed_7328_; size_t v_stop_boxed_7329_; lean_object* v_res_7330_; 
v_i_boxed_7328_ = lean_unbox_usize(v_i_7325_);
lean_dec(v_i_7325_);
v_stop_boxed_7329_ = lean_unbox_usize(v_stop_7326_);
lean_dec(v_stop_7326_);
v_res_7330_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7322_, v_j_7323_, v_as_7324_, v_i_boxed_7328_, v_stop_boxed_7329_, v_b_7327_);
lean_dec_ref(v_as_7324_);
return v_res_7330_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(lean_object* v_n_7331_, lean_object* v_aa_7332_, lean_object* v_adjustResult_7333_, lean_object* v_n_7334_, lean_object* v_j_7335_, lean_object* v_a_7336_){
_start:
{
lean_object* v_zero_7337_; uint8_t v_isZero_7338_; 
v_zero_7337_ = lean_unsigned_to_nat(0u);
v_isZero_7338_ = lean_nat_dec_eq(v_j_7335_, v_zero_7337_);
if (v_isZero_7338_ == 1)
{
lean_dec(v_j_7335_);
lean_dec(v_adjustResult_7333_);
return v_a_7336_;
}
else
{
lean_object* v_one_7339_; lean_object* v_n_7340_; lean_object* v___x_7341_; lean_object* v___x_7342_; lean_object* v_j_7343_; lean_object* v_b_7344_; lean_object* v___x_7345_; uint8_t v___x_7346_; 
v_one_7339_ = lean_unsigned_to_nat(1u);
v_n_7340_ = lean_nat_sub(v_j_7335_, v_one_7339_);
v___x_7341_ = lean_nat_sub(v_n_7334_, v_j_7335_);
lean_dec(v_j_7335_);
v___x_7342_ = lean_nat_sub(v_n_7331_, v_one_7339_);
v_j_7343_ = lean_nat_sub(v___x_7342_, v___x_7341_);
lean_dec(v___x_7341_);
lean_dec(v___x_7342_);
v_b_7344_ = lean_array_fget_borrowed(v_aa_7332_, v_j_7343_);
v___x_7345_ = lean_array_get_size(v_b_7344_);
v___x_7346_ = lean_nat_dec_lt(v_zero_7337_, v___x_7345_);
if (v___x_7346_ == 0)
{
lean_dec(v_j_7343_);
v_j_7335_ = v_n_7340_;
goto _start;
}
else
{
size_t v___x_7348_; size_t v___x_7349_; lean_object* v___x_7350_; 
v___x_7348_ = ((size_t)0ULL);
v___x_7349_ = lean_usize_of_nat(v___x_7345_);
lean_inc(v_adjustResult_7333_);
v___x_7350_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7333_, v_j_7343_, v_b_7344_, v___x_7348_, v___x_7349_, v_a_7336_);
v_j_7335_ = v_n_7340_;
v_a_7336_ = v___x_7350_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_n_7352_, lean_object* v_aa_7353_, lean_object* v_adjustResult_7354_, lean_object* v_n_7355_, lean_object* v_j_7356_, lean_object* v_a_7357_){
_start:
{
lean_object* v_res_7358_; 
v_res_7358_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7352_, v_aa_7353_, v_adjustResult_7354_, v_n_7355_, v_j_7356_, v_a_7357_);
lean_dec(v_n_7355_);
lean_dec_ref(v_aa_7353_);
lean_dec(v_n_7352_);
return v_res_7358_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(lean_object* v_n_7359_, lean_object* v_adjustResult_7360_, lean_object* v_aa_7361_, lean_object* v_n_7362_, lean_object* v_j_7363_, lean_object* v_a_7364_){
_start:
{
lean_object* v_zero_7365_; uint8_t v_isZero_7366_; 
v_zero_7365_ = lean_unsigned_to_nat(0u);
v_isZero_7366_ = lean_nat_dec_eq(v_j_7363_, v_zero_7365_);
if (v_isZero_7366_ == 1)
{
lean_dec(v_adjustResult_7360_);
return v_a_7364_;
}
else
{
lean_object* v_one_7367_; lean_object* v_n_7368_; lean_object* v___x_7369_; lean_object* v___x_7370_; lean_object* v_j_7371_; lean_object* v_b_7372_; lean_object* v___x_7373_; uint8_t v___x_7374_; 
v_one_7367_ = lean_unsigned_to_nat(1u);
v_n_7368_ = lean_nat_sub(v_j_7363_, v_one_7367_);
v___x_7369_ = lean_nat_sub(v_n_7362_, v_j_7363_);
v___x_7370_ = lean_nat_sub(v_n_7359_, v_one_7367_);
v_j_7371_ = lean_nat_sub(v___x_7370_, v___x_7369_);
lean_dec(v___x_7369_);
lean_dec(v___x_7370_);
v_b_7372_ = lean_array_fget_borrowed(v_aa_7361_, v_j_7371_);
v___x_7373_ = lean_array_get_size(v_b_7372_);
v___x_7374_ = lean_nat_dec_lt(v_zero_7365_, v___x_7373_);
if (v___x_7374_ == 0)
{
lean_object* v___x_7375_; 
lean_dec(v_j_7371_);
v___x_7375_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7359_, v_aa_7361_, v_adjustResult_7360_, v_n_7362_, v_n_7368_, v_a_7364_);
return v___x_7375_;
}
else
{
size_t v___x_7376_; size_t v___x_7377_; lean_object* v___x_7378_; lean_object* v___x_7379_; 
v___x_7376_ = ((size_t)0ULL);
v___x_7377_ = lean_usize_of_nat(v___x_7373_);
lean_inc(v_adjustResult_7360_);
v___x_7378_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7360_, v_j_7371_, v_b_7372_, v___x_7376_, v___x_7377_, v_a_7364_);
v___x_7379_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7359_, v_aa_7361_, v_adjustResult_7360_, v_n_7362_, v_n_7368_, v___x_7378_);
return v___x_7379_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg___boxed(lean_object* v_n_7380_, lean_object* v_adjustResult_7381_, lean_object* v_aa_7382_, lean_object* v_n_7383_, lean_object* v_j_7384_, lean_object* v_a_7385_){
_start:
{
lean_object* v_res_7386_; 
v_res_7386_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(v_n_7380_, v_adjustResult_7381_, v_aa_7382_, v_n_7383_, v_j_7384_, v_a_7385_);
lean_dec(v_j_7384_);
lean_dec(v_n_7383_);
lean_dec_ref(v_aa_7382_);
lean_dec(v_n_7380_);
return v_res_7386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(lean_object* v_adjustResult_7387_, lean_object* v_mr_7388_, lean_object* v_a_7389_){
_start:
{
lean_object* v_n_7390_; lean_object* v___x_7391_; 
v_n_7390_ = lean_array_get_size(v_mr_7388_);
v___x_7391_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(v_n_7390_, v_adjustResult_7387_, v_mr_7388_, v_n_7390_, v_n_7390_, v_a_7389_);
return v___x_7391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg___boxed(lean_object* v_adjustResult_7392_, lean_object* v_mr_7393_, lean_object* v_a_7394_){
_start:
{
lean_object* v_res_7395_; 
v_res_7395_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7392_, v_mr_7393_, v_a_7394_);
lean_dec_ref(v_mr_7393_);
return v_res_7395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(lean_object* v_moduleTreeRef_7396_, lean_object* v_ref_7397_, lean_object* v_addEntry_7398_, lean_object* v_droppedKeys_7399_, lean_object* v_constantsPerTask_7400_, lean_object* v_droppedEntriesRef_7401_, lean_object* v_adjustResult_7402_, lean_object* v_ty_7403_, lean_object* v_a_7404_, lean_object* v_a_7405_, lean_object* v_a_7406_, lean_object* v_a_7407_){
_start:
{
lean_object* v___x_7409_; 
lean_inc_ref(v_ty_7403_);
v___x_7409_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(v_moduleTreeRef_7396_, v_ty_7403_, v_a_7404_, v_a_7405_, v_a_7406_, v_a_7407_);
if (lean_obj_tag(v___x_7409_) == 0)
{
lean_object* v_a_7410_; lean_object* v___x_7411_; 
v_a_7410_ = lean_ctor_get(v___x_7409_, 0);
lean_inc(v_a_7410_);
lean_dec_ref_known(v___x_7409_, 1);
v___x_7411_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(v_ref_7397_, v_addEntry_7398_, v_droppedKeys_7399_, v_constantsPerTask_7400_, v_droppedEntriesRef_7401_, v_ty_7403_, v_a_7404_, v_a_7405_, v_a_7406_, v_a_7407_);
if (lean_obj_tag(v___x_7411_) == 0)
{
lean_object* v_a_7412_; lean_object* v___x_7414_; uint8_t v_isShared_7415_; uint8_t v_isSharedCheck_7425_; 
v_a_7412_ = lean_ctor_get(v___x_7411_, 0);
v_isSharedCheck_7425_ = !lean_is_exclusive(v___x_7411_);
if (v_isSharedCheck_7425_ == 0)
{
v___x_7414_ = v___x_7411_;
v_isShared_7415_ = v_isSharedCheck_7425_;
goto v_resetjp_7413_;
}
else
{
lean_inc(v_a_7412_);
lean_dec(v___x_7411_);
v___x_7414_ = lean_box(0);
v_isShared_7415_ = v_isSharedCheck_7425_;
goto v_resetjp_7413_;
}
v_resetjp_7413_:
{
lean_object* v___x_7416_; lean_object* v___x_7417_; lean_object* v___x_7418_; lean_object* v___x_7419_; lean_object* v___x_7420_; lean_object* v___x_7421_; lean_object* v___x_7423_; 
v___x_7416_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_a_7410_);
v___x_7417_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_a_7412_);
v___x_7418_ = lean_nat_add(v___x_7416_, v___x_7417_);
lean_dec(v___x_7417_);
lean_dec(v___x_7416_);
v___x_7419_ = lean_mk_empty_array_with_capacity(v___x_7418_);
lean_dec(v___x_7418_);
lean_inc(v_adjustResult_7402_);
v___x_7420_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7402_, v_a_7410_, v___x_7419_);
lean_dec(v_a_7410_);
v___x_7421_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7402_, v_a_7412_, v___x_7420_);
lean_dec(v_a_7412_);
if (v_isShared_7415_ == 0)
{
lean_ctor_set(v___x_7414_, 0, v___x_7421_);
v___x_7423_ = v___x_7414_;
goto v_reusejp_7422_;
}
else
{
lean_object* v_reuseFailAlloc_7424_; 
v_reuseFailAlloc_7424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7424_, 0, v___x_7421_);
v___x_7423_ = v_reuseFailAlloc_7424_;
goto v_reusejp_7422_;
}
v_reusejp_7422_:
{
return v___x_7423_;
}
}
}
else
{
lean_object* v_a_7426_; lean_object* v___x_7428_; uint8_t v_isShared_7429_; uint8_t v_isSharedCheck_7433_; 
lean_dec(v_a_7410_);
lean_dec(v_adjustResult_7402_);
v_a_7426_ = lean_ctor_get(v___x_7411_, 0);
v_isSharedCheck_7433_ = !lean_is_exclusive(v___x_7411_);
if (v_isSharedCheck_7433_ == 0)
{
v___x_7428_ = v___x_7411_;
v_isShared_7429_ = v_isSharedCheck_7433_;
goto v_resetjp_7427_;
}
else
{
lean_inc(v_a_7426_);
lean_dec(v___x_7411_);
v___x_7428_ = lean_box(0);
v_isShared_7429_ = v_isSharedCheck_7433_;
goto v_resetjp_7427_;
}
v_resetjp_7427_:
{
lean_object* v___x_7431_; 
if (v_isShared_7429_ == 0)
{
v___x_7431_ = v___x_7428_;
goto v_reusejp_7430_;
}
else
{
lean_object* v_reuseFailAlloc_7432_; 
v_reuseFailAlloc_7432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7432_, 0, v_a_7426_);
v___x_7431_ = v_reuseFailAlloc_7432_;
goto v_reusejp_7430_;
}
v_reusejp_7430_:
{
return v___x_7431_;
}
}
}
}
else
{
lean_object* v_a_7434_; lean_object* v___x_7436_; uint8_t v_isShared_7437_; uint8_t v_isSharedCheck_7441_; 
lean_dec_ref(v_ty_7403_);
lean_dec(v_adjustResult_7402_);
lean_dec(v_droppedEntriesRef_7401_);
lean_dec(v_constantsPerTask_7400_);
lean_dec(v_droppedKeys_7399_);
lean_dec_ref(v_addEntry_7398_);
v_a_7434_ = lean_ctor_get(v___x_7409_, 0);
v_isSharedCheck_7441_ = !lean_is_exclusive(v___x_7409_);
if (v_isSharedCheck_7441_ == 0)
{
v___x_7436_ = v___x_7409_;
v_isShared_7437_ = v_isSharedCheck_7441_;
goto v_resetjp_7435_;
}
else
{
lean_inc(v_a_7434_);
lean_dec(v___x_7409_);
v___x_7436_ = lean_box(0);
v_isShared_7437_ = v_isSharedCheck_7441_;
goto v_resetjp_7435_;
}
v_resetjp_7435_:
{
lean_object* v___x_7439_; 
if (v_isShared_7437_ == 0)
{
v___x_7439_ = v___x_7436_;
goto v_reusejp_7438_;
}
else
{
lean_object* v_reuseFailAlloc_7440_; 
v_reuseFailAlloc_7440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7440_, 0, v_a_7434_);
v___x_7439_ = v_reuseFailAlloc_7440_;
goto v_reusejp_7438_;
}
v_reusejp_7438_:
{
return v___x_7439_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg___boxed(lean_object* v_moduleTreeRef_7442_, lean_object* v_ref_7443_, lean_object* v_addEntry_7444_, lean_object* v_droppedKeys_7445_, lean_object* v_constantsPerTask_7446_, lean_object* v_droppedEntriesRef_7447_, lean_object* v_adjustResult_7448_, lean_object* v_ty_7449_, lean_object* v_a_7450_, lean_object* v_a_7451_, lean_object* v_a_7452_, lean_object* v_a_7453_, lean_object* v_a_7454_){
_start:
{
lean_object* v_res_7455_; 
v_res_7455_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_moduleTreeRef_7442_, v_ref_7443_, v_addEntry_7444_, v_droppedKeys_7445_, v_constantsPerTask_7446_, v_droppedEntriesRef_7447_, v_adjustResult_7448_, v_ty_7449_, v_a_7450_, v_a_7451_, v_a_7452_, v_a_7453_);
lean_dec(v_a_7453_);
lean_dec_ref(v_a_7452_);
lean_dec(v_a_7451_);
lean_dec_ref(v_a_7450_);
lean_dec(v_ref_7443_);
return v_res_7455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt(lean_object* v_00_u03b1_7456_, lean_object* v_00_u03b2_7457_, lean_object* v_moduleTreeRef_7458_, lean_object* v_ref_7459_, lean_object* v_addEntry_7460_, lean_object* v_droppedKeys_7461_, lean_object* v_constantsPerTask_7462_, lean_object* v_droppedEntriesRef_7463_, lean_object* v_adjustResult_7464_, lean_object* v_ty_7465_, lean_object* v_a_7466_, lean_object* v_a_7467_, lean_object* v_a_7468_, lean_object* v_a_7469_){
_start:
{
lean_object* v___x_7471_; 
v___x_7471_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_moduleTreeRef_7458_, v_ref_7459_, v_addEntry_7460_, v_droppedKeys_7461_, v_constantsPerTask_7462_, v_droppedEntriesRef_7463_, v_adjustResult_7464_, v_ty_7465_, v_a_7466_, v_a_7467_, v_a_7468_, v_a_7469_);
return v___x_7471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___boxed(lean_object* v_00_u03b1_7472_, lean_object* v_00_u03b2_7473_, lean_object* v_moduleTreeRef_7474_, lean_object* v_ref_7475_, lean_object* v_addEntry_7476_, lean_object* v_droppedKeys_7477_, lean_object* v_constantsPerTask_7478_, lean_object* v_droppedEntriesRef_7479_, lean_object* v_adjustResult_7480_, lean_object* v_ty_7481_, lean_object* v_a_7482_, lean_object* v_a_7483_, lean_object* v_a_7484_, lean_object* v_a_7485_, lean_object* v_a_7486_){
_start:
{
lean_object* v_res_7487_; 
v_res_7487_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt(v_00_u03b1_7472_, v_00_u03b2_7473_, v_moduleTreeRef_7474_, v_ref_7475_, v_addEntry_7476_, v_droppedKeys_7477_, v_constantsPerTask_7478_, v_droppedEntriesRef_7479_, v_adjustResult_7480_, v_ty_7481_, v_a_7482_, v_a_7483_, v_a_7484_, v_a_7485_);
lean_dec(v_a_7485_);
lean_dec_ref(v_a_7484_);
lean_dec(v_a_7483_);
lean_dec_ref(v_a_7482_);
lean_dec(v_ref_7475_);
return v_res_7487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0(lean_object* v_00_u03b1_7488_, lean_object* v_00_u03b2_7489_, lean_object* v_adjustResult_7490_, lean_object* v_mr_7491_, lean_object* v_a_7492_){
_start:
{
lean_object* v___x_7493_; 
v___x_7493_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7490_, v_mr_7491_, v_a_7492_);
return v___x_7493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___boxed(lean_object* v_00_u03b1_7494_, lean_object* v_00_u03b2_7495_, lean_object* v_adjustResult_7496_, lean_object* v_mr_7497_, lean_object* v_a_7498_){
_start:
{
lean_object* v_res_7499_; 
v_res_7499_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0(v_00_u03b1_7494_, v_00_u03b2_7495_, v_adjustResult_7496_, v_mr_7497_, v_a_7498_);
lean_dec_ref(v_mr_7497_);
return v_res_7499_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0(lean_object* v_00_u03b1_7500_, lean_object* v_00_u03b2_7501_, lean_object* v_adjustResult_7502_, lean_object* v_j_7503_, size_t v_sz_7504_, size_t v_i_7505_, lean_object* v_bs_7506_){
_start:
{
lean_object* v___x_7507_; 
v___x_7507_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(v_adjustResult_7502_, v_j_7503_, v_sz_7504_, v_i_7505_, v_bs_7506_);
return v___x_7507_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___boxed(lean_object* v_00_u03b1_7508_, lean_object* v_00_u03b2_7509_, lean_object* v_adjustResult_7510_, lean_object* v_j_7511_, lean_object* v_sz_7512_, lean_object* v_i_7513_, lean_object* v_bs_7514_){
_start:
{
size_t v_sz_boxed_7515_; size_t v_i_boxed_7516_; lean_object* v_res_7517_; 
v_sz_boxed_7515_ = lean_unbox_usize(v_sz_7512_);
lean_dec(v_sz_7512_);
v_i_boxed_7516_ = lean_unbox_usize(v_i_7513_);
lean_dec(v_i_7513_);
v_res_7517_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0(v_00_u03b1_7508_, v_00_u03b2_7509_, v_adjustResult_7510_, v_j_7511_, v_sz_boxed_7515_, v_i_boxed_7516_, v_bs_7514_);
return v_res_7517_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1(lean_object* v_00_u03b1_7518_, lean_object* v_00_u03b2_7519_, lean_object* v_adjustResult_7520_, lean_object* v_j_7521_, lean_object* v_as_7522_, size_t v_i_7523_, size_t v_stop_7524_, lean_object* v_b_7525_){
_start:
{
lean_object* v___x_7526_; 
v___x_7526_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7520_, v_j_7521_, v_as_7522_, v_i_7523_, v_stop_7524_, v_b_7525_);
return v___x_7526_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___boxed(lean_object* v_00_u03b1_7527_, lean_object* v_00_u03b2_7528_, lean_object* v_adjustResult_7529_, lean_object* v_j_7530_, lean_object* v_as_7531_, lean_object* v_i_7532_, lean_object* v_stop_7533_, lean_object* v_b_7534_){
_start:
{
size_t v_i_boxed_7535_; size_t v_stop_boxed_7536_; lean_object* v_res_7537_; 
v_i_boxed_7535_ = lean_unbox_usize(v_i_7532_);
lean_dec(v_i_7532_);
v_stop_boxed_7536_ = lean_unbox_usize(v_stop_7533_);
lean_dec(v_stop_7533_);
v_res_7537_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1(v_00_u03b1_7527_, v_00_u03b2_7528_, v_adjustResult_7529_, v_j_7530_, v_as_7531_, v_i_boxed_7535_, v_stop_boxed_7536_, v_b_7534_);
lean_dec_ref(v_as_7531_);
return v_res_7537_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2(lean_object* v_00_u03b2_7538_, lean_object* v_n_7539_, lean_object* v_00_u03b1_7540_, lean_object* v_adjustResult_7541_, lean_object* v_aa_7542_, lean_object* v_n_7543_, lean_object* v_j_7544_, lean_object* v_a_7545_, lean_object* v_a_7546_){
_start:
{
lean_object* v___x_7547_; 
v___x_7547_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(v_n_7539_, v_adjustResult_7541_, v_aa_7542_, v_n_7543_, v_j_7544_, v_a_7546_);
return v___x_7547_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___boxed(lean_object* v_00_u03b2_7548_, lean_object* v_n_7549_, lean_object* v_00_u03b1_7550_, lean_object* v_adjustResult_7551_, lean_object* v_aa_7552_, lean_object* v_n_7553_, lean_object* v_j_7554_, lean_object* v_a_7555_, lean_object* v_a_7556_){
_start:
{
lean_object* v_res_7557_; 
v_res_7557_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2(v_00_u03b2_7548_, v_n_7549_, v_00_u03b1_7550_, v_adjustResult_7551_, v_aa_7552_, v_n_7553_, v_j_7554_, v_a_7555_, v_a_7556_);
lean_dec(v_j_7554_);
lean_dec(v_n_7553_);
lean_dec_ref(v_aa_7552_);
lean_dec(v_n_7549_);
return v_res_7557_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_7558_, lean_object* v_n_7559_, lean_object* v_00_u03b1_7560_, lean_object* v_aa_7561_, lean_object* v_adjustResult_7562_, lean_object* v_n_7563_, lean_object* v_j_7564_, lean_object* v_a_7565_, lean_object* v_a_7566_){
_start:
{
lean_object* v___x_7567_; 
v___x_7567_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7559_, v_aa_7561_, v_adjustResult_7562_, v_n_7563_, v_j_7564_, v_a_7566_);
return v___x_7567_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b2_7568_, lean_object* v_n_7569_, lean_object* v_00_u03b1_7570_, lean_object* v_aa_7571_, lean_object* v_adjustResult_7572_, lean_object* v_n_7573_, lean_object* v_j_7574_, lean_object* v_a_7575_, lean_object* v_a_7576_){
_start:
{
lean_object* v_res_7577_; 
v_res_7577_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3(v_00_u03b2_7568_, v_n_7569_, v_00_u03b1_7570_, v_aa_7571_, v_adjustResult_7572_, v_n_7573_, v_j_7574_, v_a_7575_, v_a_7576_);
lean_dec(v_n_7573_);
lean_dec_ref(v_aa_7571_);
lean_dec(v_n_7569_);
return v_res_7577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg___lam__0(lean_object* v_x_7578_, lean_object* v_v_7579_){
_start:
{
lean_inc(v_v_7579_);
return v_v_7579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg___lam__0___boxed(lean_object* v_x_7580_, lean_object* v_v_7581_){
_start:
{
lean_object* v_res_7582_; 
v_res_7582_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg___lam__0(v_x_7580_, v_v_7581_);
lean_dec(v_v_7581_);
lean_dec(v_x_7580_);
return v_res_7582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg(lean_object* v_ref_7584_, lean_object* v_addEntry_7585_, lean_object* v_droppedKeys_7586_, lean_object* v_constantsPerTask_7587_, lean_object* v_droppedEntriesRef_7588_, lean_object* v_ty_7589_, lean_object* v_a_7590_, lean_object* v_a_7591_, lean_object* v_a_7592_, lean_object* v_a_7593_){
_start:
{
lean_object* v___f_7595_; lean_object* v___x_7596_; 
v___f_7595_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_findMatches___redArg___closed__0));
lean_inc(v_droppedEntriesRef_7588_);
lean_inc(v_droppedKeys_7586_);
lean_inc_ref(v_addEntry_7585_);
v___x_7596_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v_addEntry_7585_, v_droppedKeys_7586_, v_droppedEntriesRef_7588_, v_a_7590_, v_a_7591_, v_a_7592_, v_a_7593_);
if (lean_obj_tag(v___x_7596_) == 0)
{
lean_object* v_a_7597_; lean_object* v___x_7598_; 
v_a_7597_ = lean_ctor_get(v___x_7596_, 0);
lean_inc(v_a_7597_);
lean_dec_ref_known(v___x_7596_, 1);
v___x_7598_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_a_7597_, v_ref_7584_, v_addEntry_7585_, v_droppedKeys_7586_, v_constantsPerTask_7587_, v_droppedEntriesRef_7588_, v___f_7595_, v_ty_7589_, v_a_7590_, v_a_7591_, v_a_7592_, v_a_7593_);
return v___x_7598_;
}
else
{
lean_object* v_a_7599_; lean_object* v___x_7601_; uint8_t v_isShared_7602_; uint8_t v_isSharedCheck_7606_; 
lean_dec_ref(v_ty_7589_);
lean_dec(v_droppedEntriesRef_7588_);
lean_dec(v_constantsPerTask_7587_);
lean_dec(v_droppedKeys_7586_);
lean_dec_ref(v_addEntry_7585_);
v_a_7599_ = lean_ctor_get(v___x_7596_, 0);
v_isSharedCheck_7606_ = !lean_is_exclusive(v___x_7596_);
if (v_isSharedCheck_7606_ == 0)
{
v___x_7601_ = v___x_7596_;
v_isShared_7602_ = v_isSharedCheck_7606_;
goto v_resetjp_7600_;
}
else
{
lean_inc(v_a_7599_);
lean_dec(v___x_7596_);
v___x_7601_ = lean_box(0);
v_isShared_7602_ = v_isSharedCheck_7606_;
goto v_resetjp_7600_;
}
v_resetjp_7600_:
{
lean_object* v___x_7604_; 
if (v_isShared_7602_ == 0)
{
v___x_7604_ = v___x_7601_;
goto v_reusejp_7603_;
}
else
{
lean_object* v_reuseFailAlloc_7605_; 
v_reuseFailAlloc_7605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7605_, 0, v_a_7599_);
v___x_7604_ = v_reuseFailAlloc_7605_;
goto v_reusejp_7603_;
}
v_reusejp_7603_:
{
return v___x_7604_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg___boxed(lean_object* v_ref_7607_, lean_object* v_addEntry_7608_, lean_object* v_droppedKeys_7609_, lean_object* v_constantsPerTask_7610_, lean_object* v_droppedEntriesRef_7611_, lean_object* v_ty_7612_, lean_object* v_a_7613_, lean_object* v_a_7614_, lean_object* v_a_7615_, lean_object* v_a_7616_, lean_object* v_a_7617_){
_start:
{
lean_object* v_res_7618_; 
v_res_7618_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg(v_ref_7607_, v_addEntry_7608_, v_droppedKeys_7609_, v_constantsPerTask_7610_, v_droppedEntriesRef_7611_, v_ty_7612_, v_a_7613_, v_a_7614_, v_a_7615_, v_a_7616_);
lean_dec(v_a_7616_);
lean_dec_ref(v_a_7615_);
lean_dec(v_a_7614_);
lean_dec_ref(v_a_7613_);
lean_dec(v_ref_7607_);
return v_res_7618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches(lean_object* v_00_u03b1_7619_, lean_object* v_ref_7620_, lean_object* v_addEntry_7621_, lean_object* v_droppedKeys_7622_, lean_object* v_constantsPerTask_7623_, lean_object* v_droppedEntriesRef_7624_, lean_object* v_ty_7625_, lean_object* v_a_7626_, lean_object* v_a_7627_, lean_object* v_a_7628_, lean_object* v_a_7629_){
_start:
{
lean_object* v___x_7631_; 
v___x_7631_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg(v_ref_7620_, v_addEntry_7621_, v_droppedKeys_7622_, v_constantsPerTask_7623_, v_droppedEntriesRef_7624_, v_ty_7625_, v_a_7626_, v_a_7627_, v_a_7628_, v_a_7629_);
return v___x_7631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___boxed(lean_object* v_00_u03b1_7632_, lean_object* v_ref_7633_, lean_object* v_addEntry_7634_, lean_object* v_droppedKeys_7635_, lean_object* v_constantsPerTask_7636_, lean_object* v_droppedEntriesRef_7637_, lean_object* v_ty_7638_, lean_object* v_a_7639_, lean_object* v_a_7640_, lean_object* v_a_7641_, lean_object* v_a_7642_, lean_object* v_a_7643_){
_start:
{
lean_object* v_res_7644_; 
v_res_7644_ = l_Lean_Meta_LazyDiscrTree_findMatches(v_00_u03b1_7632_, v_ref_7633_, v_addEntry_7634_, v_droppedKeys_7635_, v_constantsPerTask_7636_, v_droppedEntriesRef_7637_, v_ty_7638_, v_a_7639_, v_a_7640_, v_a_7641_, v_a_7642_);
lean_dec(v_a_7642_);
lean_dec_ref(v_a_7641_);
lean_dec(v_a_7640_);
lean_dec_ref(v_a_7639_);
lean_dec(v_ref_7633_);
return v_res_7644_;
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
