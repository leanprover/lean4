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
lean_object* l_Lean_Expr_updateAppN(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t l_IO_CancelToken_isSet(lean_object*);
extern lean_object* l_Lean_interruptExceptionId;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "transform"};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0_spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0;
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1;
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2;
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3;
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Cache_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0(lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___boxed(lean_object*, lean_object*);
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
lean_object* v_f_490_; 
v_f_490_ = l_Lean_Expr_getAppFn(v_e_489_);
switch(lean_obj_tag(v_f_490_))
{
case 9:
{
lean_object* v_a_491_; 
lean_dec_ref(v_e_489_);
v_a_491_ = lean_ctor_get(v_f_490_, 0);
lean_inc_ref(v_a_491_);
lean_dec_ref_known(v_f_490_, 1);
if (lean_obj_tag(v_a_491_) == 0)
{
lean_object* v_val_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_499_; 
v_val_492_ = lean_ctor_get(v_a_491_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v_a_491_);
if (v_isSharedCheck_499_ == 0)
{
v___x_494_ = v_a_491_;
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_val_492_);
lean_dec(v_a_491_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_497_; 
if (v_isShared_495_ == 0)
{
lean_ctor_set_tag(v___x_494_, 1);
v___x_497_ = v___x_494_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_val_492_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
else
{
lean_object* v___x_500_; 
lean_dec_ref(v_a_491_);
v___x_500_ = lean_box(0);
return v___x_500_;
}
}
case 4:
{
lean_object* v_declName_501_; lean_object* v___x_522_; uint8_t v___x_523_; 
v_declName_501_ = lean_ctor_get(v_f_490_, 0);
lean_inc(v_declName_501_);
lean_dec_ref_known(v_f_490_, 2);
v___x_522_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__7));
v___x_523_ = lean_name_eq(v_declName_501_, v___x_522_);
if (v___x_523_ == 0)
{
goto v___jp_511_;
}
else
{
lean_object* v___x_524_; lean_object* v___x_525_; uint8_t v___x_526_; 
v___x_524_ = l_Lean_Expr_getAppNumArgs(v_e_489_);
v___x_525_ = lean_unsigned_to_nat(1u);
v___x_526_ = lean_nat_dec_eq(v___x_524_, v___x_525_);
lean_dec(v___x_524_);
if (v___x_526_ == 0)
{
goto v___jp_511_;
}
else
{
lean_object* v___x_527_; lean_object* v___x_528_; 
lean_dec(v_declName_501_);
v___x_527_ = l_Lean_Expr_appArg_x21(v_e_489_);
lean_dec_ref(v_e_489_);
v___x_528_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f_loop(v___x_527_);
if (lean_obj_tag(v___x_528_) == 0)
{
return v___x_528_;
}
else
{
lean_object* v_val_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_537_; 
v_val_529_ = lean_ctor_get(v___x_528_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_537_ == 0)
{
v___x_531_ = v___x_528_;
v_isShared_532_ = v_isSharedCheck_537_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_val_529_);
lean_dec(v___x_528_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_537_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_533_; lean_object* v___x_535_; 
v___x_533_ = lean_nat_add(v_val_529_, v___x_525_);
lean_dec(v_val_529_);
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 0, v___x_533_);
v___x_535_ = v___x_531_;
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
v___jp_502_:
{
lean_object* v___x_503_; uint8_t v___x_504_; 
v___x_503_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__2));
v___x_504_ = lean_name_eq(v_declName_501_, v___x_503_);
lean_dec(v_declName_501_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; 
lean_dec_ref(v_e_489_);
v___x_505_ = lean_box(0);
return v___x_505_;
}
else
{
lean_object* v___x_506_; lean_object* v___x_507_; uint8_t v___x_508_; 
v___x_506_ = l_Lean_Expr_getAppNumArgs(v_e_489_);
lean_dec_ref(v_e_489_);
v___x_507_ = lean_unsigned_to_nat(0u);
v___x_508_ = lean_nat_dec_eq(v___x_506_, v___x_507_);
lean_dec(v___x_506_);
if (v___x_508_ == 0)
{
lean_object* v___x_509_; 
v___x_509_ = lean_box(0);
return v___x_509_;
}
else
{
lean_object* v___x_510_; 
v___x_510_ = ((lean_object*)(l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f_loop___closed__0));
return v___x_510_;
}
}
}
v___jp_511_:
{
lean_object* v___x_512_; uint8_t v___x_513_; 
v___x_512_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__5));
v___x_513_ = lean_name_eq(v_declName_501_, v___x_512_);
if (v___x_513_ == 0)
{
goto v___jp_502_;
}
else
{
lean_object* v___x_514_; lean_object* v___x_515_; uint8_t v___x_516_; 
v___x_514_ = l_Lean_Expr_getAppNumArgs(v_e_489_);
v___x_515_ = lean_unsigned_to_nat(3u);
v___x_516_ = lean_nat_dec_eq(v___x_514_, v___x_515_);
if (v___x_516_ == 0)
{
lean_dec(v___x_514_);
goto v___jp_502_;
}
else
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
lean_dec(v_declName_501_);
v___x_517_ = lean_unsigned_to_nat(1u);
v___x_518_ = lean_nat_sub(v___x_514_, v___x_517_);
lean_dec(v___x_514_);
v___x_519_ = lean_nat_sub(v___x_518_, v___x_517_);
lean_dec(v___x_518_);
v___x_520_ = l_Lean_Expr_getRevArg_x21(v_e_489_, v___x_519_);
lean_dec_ref(v_e_489_);
v_e_489_ = v___x_520_;
goto _start;
}
}
}
}
default: 
{
lean_object* v___x_538_; 
lean_dec_ref(v_f_490_);
lean_dec_ref(v_e_489_);
v___x_538_ = lean_box(0);
return v___x_538_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f(lean_object* v_e_539_){
_start:
{
uint8_t v___x_540_; 
lean_inc_ref(v_e_539_);
v___x_540_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral(v_e_539_);
if (v___x_540_ == 0)
{
lean_object* v___x_541_; 
lean_dec_ref(v_e_539_);
v___x_541_ = lean_box(0);
return v___x_541_;
}
else
{
lean_object* v___x_542_; 
v___x_542_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f_loop(v_e_539_);
if (lean_obj_tag(v___x_542_) == 1)
{
lean_object* v_val_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_551_; 
v_val_543_ = lean_ctor_get(v___x_542_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_551_ == 0)
{
v___x_545_ = v___x_542_;
v_isShared_546_ = v_isSharedCheck_551_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_val_543_);
lean_dec(v___x_542_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_551_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_547_; lean_object* v___x_549_; 
v___x_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_547_, 0, v_val_543_);
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 0, v___x_547_);
v___x_549_ = v___x_545_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v___x_547_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
else
{
lean_object* v___x_552_; 
lean_dec(v___x_542_);
v___x_552_ = lean_box(0);
return v___x_552_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNatType(lean_object* v_e_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_){
_start:
{
lean_object* v___x_561_; 
lean_inc(v_a_559_);
lean_inc_ref(v_a_558_);
lean_inc(v_a_557_);
lean_inc_ref(v_a_556_);
v___x_561_ = lean_whnf(v_e_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_);
if (lean_obj_tag(v___x_561_) == 0)
{
lean_object* v_a_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_572_; 
v_a_562_ = lean_ctor_get(v___x_561_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_561_);
if (v_isSharedCheck_572_ == 0)
{
v___x_564_ = v___x_561_;
v_isShared_565_ = v_isSharedCheck_572_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_a_562_);
lean_dec(v___x_561_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_572_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_566_; uint8_t v___x_567_; lean_object* v___x_568_; lean_object* v___x_570_; 
v___x_566_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNatType___closed__0));
v___x_567_ = l_Lean_Expr_isConstOf(v_a_562_, v___x_566_);
lean_dec(v_a_562_);
v___x_568_ = lean_box(v___x_567_);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 0, v___x_568_);
v___x_570_ = v___x_564_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_568_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
else
{
lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_580_; 
v_a_573_ = lean_ctor_get(v___x_561_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_561_);
if (v_isSharedCheck_580_ == 0)
{
v___x_575_ = v___x_561_;
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_dec(v___x_561_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_578_; 
if (v_isShared_576_ == 0)
{
v___x_578_ = v___x_575_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_a_573_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNatType___boxed(lean_object* v_e_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNatType(v_e_581_, v_a_582_, v_a_583_, v_a_584_, v_a_585_);
lean_dec(v_a_585_);
lean_dec_ref(v_a_584_);
lean_dec(v_a_583_);
lean_dec_ref(v_a_582_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset(lean_object* v_fName_601_, lean_object* v_e_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_){
_start:
{
lean_object* v___x_665_; uint8_t v___x_666_; 
v___x_665_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___closed__6));
v___x_666_ = lean_name_eq(v_fName_601_, v___x_665_);
if (v___x_666_ == 0)
{
goto v___jp_642_;
}
else
{
lean_object* v___x_667_; lean_object* v___x_668_; uint8_t v___x_669_; 
v___x_667_ = l_Lean_Expr_getAppNumArgs(v_e_602_);
v___x_668_ = lean_unsigned_to_nat(2u);
v___x_669_ = lean_nat_dec_eq(v___x_667_, v___x_668_);
lean_dec(v___x_667_);
if (v___x_669_ == 0)
{
goto v___jp_642_;
}
else
{
lean_object* v___x_670_; uint8_t v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_670_ = l_Lean_Expr_appArg_x21(v_e_602_);
v___x_671_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral(v___x_670_);
v___x_672_ = lean_box(v___x_671_);
v___x_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
return v___x_673_;
}
}
v___jp_608_:
{
lean_object* v___x_609_; uint8_t v___x_610_; 
v___x_609_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__7));
v___x_610_ = lean_name_eq(v_fName_601_, v___x_609_);
if (v___x_610_ == 0)
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = lean_box(v___x_610_);
v___x_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
return v___x_612_;
}
else
{
lean_object* v___x_613_; lean_object* v___x_614_; uint8_t v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_613_ = l_Lean_Expr_getAppNumArgs(v_e_602_);
v___x_614_ = lean_unsigned_to_nat(1u);
v___x_615_ = lean_nat_dec_eq(v___x_613_, v___x_614_);
lean_dec(v___x_613_);
v___x_616_ = lean_box(v___x_615_);
v___x_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_617_, 0, v___x_616_);
return v___x_617_;
}
}
v___jp_618_:
{
lean_object* v___x_619_; uint8_t v___x_620_; 
v___x_619_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___closed__2));
v___x_620_ = lean_name_eq(v_fName_601_, v___x_619_);
if (v___x_620_ == 0)
{
goto v___jp_608_;
}
else
{
lean_object* v___x_621_; lean_object* v___x_622_; uint8_t v___x_623_; 
v___x_621_ = l_Lean_Expr_getAppNumArgs(v_e_602_);
v___x_622_ = lean_unsigned_to_nat(6u);
v___x_623_ = lean_nat_dec_eq(v___x_621_, v___x_622_);
if (v___x_623_ == 0)
{
lean_dec(v___x_621_);
goto v___jp_608_;
}
else
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_624_ = lean_unsigned_to_nat(1u);
v___x_625_ = lean_nat_sub(v___x_621_, v___x_624_);
lean_dec(v___x_621_);
v___x_626_ = lean_nat_sub(v___x_625_, v___x_624_);
lean_dec(v___x_625_);
v___x_627_ = l_Lean_Expr_getRevArg_x21(v_e_602_, v___x_626_);
v___x_628_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNatType(v___x_627_, v_a_603_, v_a_604_, v_a_605_, v_a_606_);
if (lean_obj_tag(v___x_628_) == 0)
{
lean_object* v_a_629_; uint8_t v___x_630_; 
v_a_629_ = lean_ctor_get(v___x_628_, 0);
v___x_630_ = lean_unbox(v_a_629_);
if (v___x_630_ == 0)
{
return v___x_628_;
}
else
{
lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_640_; 
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_640_ == 0)
{
lean_object* v_unused_641_; 
v_unused_641_ = lean_ctor_get(v___x_628_, 0);
lean_dec(v_unused_641_);
v___x_632_ = v___x_628_;
v_isShared_633_ = v_isSharedCheck_640_;
goto v_resetjp_631_;
}
else
{
lean_dec(v___x_628_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_640_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_634_; uint8_t v___x_635_; lean_object* v___x_636_; lean_object* v___x_638_; 
v___x_634_ = l_Lean_Expr_appArg_x21(v_e_602_);
v___x_635_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral(v___x_634_);
v___x_636_ = lean_box(v___x_635_);
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 0, v___x_636_);
v___x_638_ = v___x_632_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v___x_636_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
}
else
{
return v___x_628_;
}
}
}
}
v___jp_642_:
{
lean_object* v___x_643_; uint8_t v___x_644_; 
v___x_643_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___closed__5));
v___x_644_ = lean_name_eq(v_fName_601_, v___x_643_);
if (v___x_644_ == 0)
{
goto v___jp_618_;
}
else
{
lean_object* v___x_645_; lean_object* v___x_646_; uint8_t v___x_647_; 
v___x_645_ = l_Lean_Expr_getAppNumArgs(v_e_602_);
v___x_646_ = lean_unsigned_to_nat(4u);
v___x_647_ = lean_nat_dec_eq(v___x_645_, v___x_646_);
if (v___x_647_ == 0)
{
lean_dec(v___x_645_);
goto v___jp_618_;
}
else
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_648_ = lean_unsigned_to_nat(1u);
v___x_649_ = lean_nat_sub(v___x_645_, v___x_648_);
lean_dec(v___x_645_);
v___x_650_ = l_Lean_Expr_getRevArg_x21(v_e_602_, v___x_649_);
v___x_651_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNatType(v___x_650_, v_a_603_, v_a_604_, v_a_605_, v_a_606_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_a_652_; uint8_t v___x_653_; 
v_a_652_ = lean_ctor_get(v___x_651_, 0);
v___x_653_ = lean_unbox(v_a_652_);
if (v___x_653_ == 0)
{
return v___x_651_;
}
else
{
lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_663_; 
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_663_ == 0)
{
lean_object* v_unused_664_; 
v_unused_664_ = lean_ctor_get(v___x_651_, 0);
lean_dec(v_unused_664_);
v___x_655_ = v___x_651_;
v_isShared_656_ = v_isSharedCheck_663_;
goto v_resetjp_654_;
}
else
{
lean_dec(v___x_651_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_663_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_657_; uint8_t v___x_658_; lean_object* v___x_659_; lean_object* v___x_661_; 
v___x_657_ = l_Lean_Expr_appArg_x21(v_e_602_);
v___x_658_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral(v___x_657_);
v___x_659_ = lean_box(v___x_658_);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 0, v___x_659_);
v___x_661_ = v___x_655_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v___x_659_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
}
else
{
return v___x_651_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___boxed(lean_object* v_fName_674_, lean_object* v_e_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset(v_fName_674_, v_e_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_);
lean_dec(v_a_679_);
lean_dec_ref(v_a_678_);
lean_dec(v_a_677_);
lean_dec_ref(v_a_676_);
lean_dec_ref(v_e_675_);
lean_dec(v_fName_674_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_shouldAddAsStar(lean_object* v_fName_682_, lean_object* v_e_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_){
_start:
{
lean_object* v___x_689_; 
v___x_689_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset(v_fName_682_, v_e_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_shouldAddAsStar___boxed(lean_object* v_fName_690_, lean_object* v_e_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Lean_Meta_LazyDiscrTree_MatchClone_shouldAddAsStar(v_fName_690_, v_e_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_);
lean_dec(v_a_695_);
lean_dec_ref(v_a_694_);
lean_dec(v_a_693_);
lean_dec_ref(v_a_692_);
lean_dec_ref(v_e_691_);
lean_dec(v_fName_690_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__0(lean_object* v_e_700_, lean_object* v___y_701_, lean_object* v___y_702_){
_start:
{
uint8_t v___x_704_; 
v___x_704_ = l_Lean_Expr_hasLooseBVars(v_e_700_);
if (v___x_704_ == 0)
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_705_, 0, v_e_700_);
v___x_706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_706_, 0, v___x_705_);
return v___x_706_;
}
else
{
uint8_t v___x_707_; uint8_t v___x_708_; 
v___x_707_ = 0;
v___x_708_ = l_Lean_Expr_isHeadBetaTarget(v_e_700_, v___x_707_);
if (v___x_708_ == 0)
{
lean_object* v___x_709_; lean_object* v___x_710_; 
lean_dec_ref(v_e_700_);
v___x_709_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__0___closed__0));
v___x_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_710_, 0, v___x_709_);
return v___x_710_;
}
else
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_711_ = l_Lean_Expr_headBeta(v_e_700_);
v___x_712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_712_, 0, v___x_711_);
v___x_713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_713_, 0, v___x_712_);
return v___x_713_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__0___boxed(lean_object* v_e_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__0(v_e_714_, v___y_715_, v___y_716_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__1(lean_object* v_e_719_, lean_object* v___y_720_, lean_object* v___y_721_){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_723_, 0, v_e_719_);
v___x_724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_724_, 0, v___x_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__1___boxed(lean_object* v_e_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__1(v_e_725_, v___y_726_, v___y_727_);
lean_dec(v___y_727_);
lean_dec_ref(v___y_726_);
return v_res_729_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_730_ = lean_box(0);
v___x_731_ = l_Lean_interruptExceptionId;
v___x_732_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_732_, 0, v___x_731_);
lean_ctor_set(v___x_732_, 1, v___x_730_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg(){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_734_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg___closed__0);
v___x_735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_735_, 0, v___x_734_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg___boxed(lean_object* v___y_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg();
return v_res_737_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = l_Lean_maxRecDepthErrorMessage;
v___x_744_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_744_, 0, v___x_743_);
return v___x_744_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_745_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__3);
v___x_746_ = l_Lean_MessageData_ofFormat(v___x_745_);
return v___x_746_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_747_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__4);
v___x_748_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__2));
v___x_749_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_749_, 0, v___x_748_);
lean_ctor_set(v___x_749_, 1, v___x_747_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_ref_750_){
_start:
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_752_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_753_, 0, v_ref_750_);
lean_ctor_set(v___x_753_, 1, v___x_752_);
v___x_754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_ref_755_, lean_object* v___y_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_755_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg(lean_object* v_x_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_){
_start:
{
lean_object* v___y_764_; lean_object* v___y_774_; uint8_t v___y_775_; uint8_t v___y_776_; uint16_t v___y_777_; uint8_t v___y_778_; lean_object* v___y_779_; lean_object* v___y_780_; lean_object* v_toCold_785_; lean_object* v_currRecDepth_786_; lean_object* v_ref_787_; uint16_t v_optionFlags_788_; uint8_t v_suppressElabErrors_789_; uint8_t v_checkDeprecated_790_; uint8_t v_isRecordingDeps_791_; lean_object* v_maxRecDepth_792_; lean_object* v_cancelTk_x3f_793_; 
v_toCold_785_ = lean_ctor_get(v___y_760_, 0);
v_currRecDepth_786_ = lean_ctor_get(v___y_760_, 1);
v_ref_787_ = lean_ctor_get(v___y_760_, 2);
v_optionFlags_788_ = lean_ctor_get_uint16(v___y_760_, sizeof(void*)*3);
v_suppressElabErrors_789_ = lean_ctor_get_uint8(v___y_760_, sizeof(void*)*3 + 2);
v_checkDeprecated_790_ = lean_ctor_get_uint8(v___y_760_, sizeof(void*)*3 + 3);
v_isRecordingDeps_791_ = lean_ctor_get_uint8(v___y_760_, sizeof(void*)*3 + 4);
v_maxRecDepth_792_ = lean_ctor_get(v_toCold_785_, 3);
v_cancelTk_x3f_793_ = lean_ctor_get(v_toCold_785_, 10);
if (lean_obj_tag(v_cancelTk_x3f_793_) == 1)
{
lean_object* v_val_799_; uint8_t v___x_800_; 
v_val_799_ = lean_ctor_get(v_cancelTk_x3f_793_, 0);
v___x_800_ = l_IO_CancelToken_isSet(v_val_799_);
if (v___x_800_ == 0)
{
goto v___jp_794_;
}
else
{
lean_object* v___x_801_; lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_809_; 
lean_dec_ref(v_x_758_);
v___x_801_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg();
v_a_802_ = lean_ctor_get(v___x_801_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_801_);
if (v_isSharedCheck_809_ == 0)
{
v___x_804_ = v___x_801_;
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v___x_801_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_807_; 
if (v_isShared_805_ == 0)
{
v___x_807_ = v___x_804_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_a_802_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
else
{
goto v___jp_794_;
}
v___jp_763_:
{
if (lean_obj_tag(v___y_764_) == 0)
{
return v___y_764_;
}
else
{
lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_772_; 
v_a_765_ = lean_ctor_get(v___y_764_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v___y_764_);
if (v_isSharedCheck_772_ == 0)
{
v___x_767_ = v___y_764_;
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_a_765_);
lean_dec(v___y_764_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_770_; 
if (v_isShared_768_ == 0)
{
v___x_770_ = v___x_767_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_a_765_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
}
v___jp_773_:
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_781_ = lean_unsigned_to_nat(1u);
v___x_782_ = lean_nat_add(v___y_779_, v___x_781_);
lean_inc_ref(v___y_774_);
v___x_783_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_783_, 0, v___y_774_);
lean_ctor_set(v___x_783_, 1, v___x_782_);
lean_ctor_set(v___x_783_, 2, v___y_780_);
lean_ctor_set_uint16(v___x_783_, sizeof(void*)*3, v___y_777_);
lean_ctor_set_uint8(v___x_783_, sizeof(void*)*3 + 2, v___y_776_);
lean_ctor_set_uint8(v___x_783_, sizeof(void*)*3 + 3, v___y_778_);
lean_ctor_set_uint8(v___x_783_, sizeof(void*)*3 + 4, v___y_775_);
lean_inc(v___y_761_);
lean_inc(v___y_759_);
v___x_784_ = lean_apply_4(v_x_758_, v___y_759_, v___x_783_, v___y_761_, lean_box(0));
v___y_764_ = v___x_784_;
goto v___jp_763_;
}
v___jp_794_:
{
lean_object* v___x_795_; uint8_t v___x_796_; 
v___x_795_ = lean_unsigned_to_nat(0u);
v___x_796_ = lean_nat_dec_eq(v_maxRecDepth_792_, v___x_795_);
if (v___x_796_ == 0)
{
uint8_t v___x_797_; 
v___x_797_ = lean_nat_dec_eq(v_currRecDepth_786_, v_maxRecDepth_792_);
if (v___x_797_ == 0)
{
lean_inc(v_ref_787_);
v___y_774_ = v_toCold_785_;
v___y_775_ = v_isRecordingDeps_791_;
v___y_776_ = v_suppressElabErrors_789_;
v___y_777_ = v_optionFlags_788_;
v___y_778_ = v_checkDeprecated_790_;
v___y_779_ = v_currRecDepth_786_;
v___y_780_ = v_ref_787_;
goto v___jp_773_;
}
else
{
lean_object* v___x_798_; 
lean_dec_ref(v_x_758_);
lean_inc(v_ref_787_);
v___x_798_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_787_);
v___y_764_ = v___x_798_;
goto v___jp_763_;
}
}
else
{
lean_inc(v_ref_787_);
v___y_774_ = v_toCold_785_;
v___y_775_ = v_isRecordingDeps_791_;
v___y_776_ = v_suppressElabErrors_789_;
v___y_777_ = v_optionFlags_788_;
v___y_778_ = v_checkDeprecated_790_;
v___y_779_ = v_currRecDepth_786_;
v___y_780_ = v_ref_787_;
goto v___jp_773_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg(v_x_810_, v___y_811_, v___y_812_, v___y_813_);
lean_dec(v___y_813_);
lean_dec_ref(v___y_812_);
lean_dec(v___y_811_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12___redArg(lean_object* v_a_816_, lean_object* v_b_817_, lean_object* v_x_818_){
_start:
{
if (lean_obj_tag(v_x_818_) == 0)
{
lean_dec(v_b_817_);
lean_dec_ref(v_a_816_);
return v_x_818_;
}
else
{
lean_object* v_key_819_; lean_object* v_value_820_; lean_object* v_tail_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_833_; 
v_key_819_ = lean_ctor_get(v_x_818_, 0);
v_value_820_ = lean_ctor_get(v_x_818_, 1);
v_tail_821_ = lean_ctor_get(v_x_818_, 2);
v_isSharedCheck_833_ = !lean_is_exclusive(v_x_818_);
if (v_isSharedCheck_833_ == 0)
{
v___x_823_ = v_x_818_;
v_isShared_824_ = v_isSharedCheck_833_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_tail_821_);
lean_inc(v_value_820_);
lean_inc(v_key_819_);
lean_dec(v_x_818_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_833_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
uint8_t v___x_825_; 
v___x_825_ = l_Lean_ExprStructEq_beq(v_key_819_, v_a_816_);
if (v___x_825_ == 0)
{
lean_object* v___x_826_; lean_object* v___x_828_; 
v___x_826_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12___redArg(v_a_816_, v_b_817_, v_tail_821_);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 2, v___x_826_);
v___x_828_ = v___x_823_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_key_819_);
lean_ctor_set(v_reuseFailAlloc_829_, 1, v_value_820_);
lean_ctor_set(v_reuseFailAlloc_829_, 2, v___x_826_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
else
{
lean_object* v___x_831_; 
lean_dec(v_value_820_);
lean_dec(v_key_819_);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 1, v_b_817_);
lean_ctor_set(v___x_823_, 0, v_a_816_);
v___x_831_ = v___x_823_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_a_816_);
lean_ctor_set(v_reuseFailAlloc_832_, 1, v_b_817_);
lean_ctor_set(v_reuseFailAlloc_832_, 2, v_tail_821_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(lean_object* v_x_834_, lean_object* v_x_835_){
_start:
{
if (lean_obj_tag(v_x_835_) == 0)
{
return v_x_834_;
}
else
{
lean_object* v_key_836_; lean_object* v_value_837_; lean_object* v_tail_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_861_; 
v_key_836_ = lean_ctor_get(v_x_835_, 0);
v_value_837_ = lean_ctor_get(v_x_835_, 1);
v_tail_838_ = lean_ctor_get(v_x_835_, 2);
v_isSharedCheck_861_ = !lean_is_exclusive(v_x_835_);
if (v_isSharedCheck_861_ == 0)
{
v___x_840_ = v_x_835_;
v_isShared_841_ = v_isSharedCheck_861_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_tail_838_);
lean_inc(v_value_837_);
lean_inc(v_key_836_);
lean_dec(v_x_835_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_861_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_842_; uint64_t v___x_843_; uint64_t v___x_844_; uint64_t v___x_845_; uint64_t v_fold_846_; uint64_t v___x_847_; uint64_t v___x_848_; uint64_t v___x_849_; size_t v___x_850_; size_t v___x_851_; size_t v___x_852_; size_t v___x_853_; size_t v___x_854_; lean_object* v___x_855_; lean_object* v___x_857_; 
v___x_842_ = lean_array_get_size(v_x_834_);
v___x_843_ = l_Lean_ExprStructEq_hash(v_key_836_);
v___x_844_ = 32ULL;
v___x_845_ = lean_uint64_shift_right(v___x_843_, v___x_844_);
v_fold_846_ = lean_uint64_xor(v___x_843_, v___x_845_);
v___x_847_ = 16ULL;
v___x_848_ = lean_uint64_shift_right(v_fold_846_, v___x_847_);
v___x_849_ = lean_uint64_xor(v_fold_846_, v___x_848_);
v___x_850_ = lean_uint64_to_usize(v___x_849_);
v___x_851_ = lean_usize_of_nat(v___x_842_);
v___x_852_ = ((size_t)1ULL);
v___x_853_ = lean_usize_sub(v___x_851_, v___x_852_);
v___x_854_ = lean_usize_land(v___x_850_, v___x_853_);
v___x_855_ = lean_array_uget_borrowed(v_x_834_, v___x_854_);
lean_inc(v___x_855_);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 2, v___x_855_);
v___x_857_ = v___x_840_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_key_836_);
lean_ctor_set(v_reuseFailAlloc_860_, 1, v_value_837_);
lean_ctor_set(v_reuseFailAlloc_860_, 2, v___x_855_);
v___x_857_ = v_reuseFailAlloc_860_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
lean_object* v___x_858_; 
v___x_858_ = lean_array_uset(v_x_834_, v___x_854_, v___x_857_);
v_x_834_ = v___x_858_;
v_x_835_ = v_tail_838_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(lean_object* v_i_862_, lean_object* v_source_863_, lean_object* v_target_864_){
_start:
{
lean_object* v___x_865_; uint8_t v___x_866_; 
v___x_865_ = lean_array_get_size(v_source_863_);
v___x_866_ = lean_nat_dec_lt(v_i_862_, v___x_865_);
if (v___x_866_ == 0)
{
lean_dec_ref(v_source_863_);
lean_dec(v_i_862_);
return v_target_864_;
}
else
{
lean_object* v_es_867_; lean_object* v___x_868_; lean_object* v_source_869_; lean_object* v_target_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
v_es_867_ = lean_array_fget(v_source_863_, v_i_862_);
v___x_868_ = lean_box(0);
v_source_869_ = lean_array_fset(v_source_863_, v_i_862_, v___x_868_);
v_target_870_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_target_864_, v_es_867_);
v___x_871_ = lean_unsigned_to_nat(1u);
v___x_872_ = lean_nat_add(v_i_862_, v___x_871_);
lean_dec(v_i_862_);
v_i_862_ = v___x_872_;
v_source_863_ = v_source_869_;
v_target_864_ = v_target_870_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11___redArg(lean_object* v_data_874_){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v_nbuckets_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_875_ = lean_array_get_size(v_data_874_);
v___x_876_ = lean_unsigned_to_nat(2u);
v_nbuckets_877_ = lean_nat_mul(v___x_875_, v___x_876_);
v___x_878_ = lean_unsigned_to_nat(0u);
v___x_879_ = lean_box(0);
v___x_880_ = lean_mk_array(v_nbuckets_877_, v___x_879_);
v___x_881_ = lean_array_propagate_mark(v_data_874_, v___x_880_);
v___x_882_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v___x_878_, v_data_874_, v___x_881_);
return v___x_882_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(lean_object* v_a_883_, lean_object* v_x_884_){
_start:
{
if (lean_obj_tag(v_x_884_) == 0)
{
uint8_t v___x_885_; 
v___x_885_ = 0;
return v___x_885_;
}
else
{
lean_object* v_key_886_; lean_object* v_tail_887_; uint8_t v___x_888_; 
v_key_886_ = lean_ctor_get(v_x_884_, 0);
v_tail_887_ = lean_ctor_get(v_x_884_, 2);
v___x_888_ = l_Lean_ExprStructEq_beq(v_key_886_, v_a_883_);
if (v___x_888_ == 0)
{
v_x_884_ = v_tail_887_;
goto _start;
}
else
{
return v___x_888_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg___boxed(lean_object* v_a_890_, lean_object* v_x_891_){
_start:
{
uint8_t v_res_892_; lean_object* v_r_893_; 
v_res_892_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(v_a_890_, v_x_891_);
lean_dec(v_x_891_);
lean_dec_ref(v_a_890_);
v_r_893_ = lean_box(v_res_892_);
return v_r_893_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6___redArg(lean_object* v_m_894_, lean_object* v_a_895_, lean_object* v_b_896_){
_start:
{
lean_object* v_size_897_; lean_object* v_buckets_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_941_; 
v_size_897_ = lean_ctor_get(v_m_894_, 0);
v_buckets_898_ = lean_ctor_get(v_m_894_, 1);
v_isSharedCheck_941_ = !lean_is_exclusive(v_m_894_);
if (v_isSharedCheck_941_ == 0)
{
v___x_900_ = v_m_894_;
v_isShared_901_ = v_isSharedCheck_941_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_buckets_898_);
lean_inc(v_size_897_);
lean_dec(v_m_894_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_941_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_902_; uint64_t v___x_903_; uint64_t v___x_904_; uint64_t v___x_905_; uint64_t v_fold_906_; uint64_t v___x_907_; uint64_t v___x_908_; uint64_t v___x_909_; size_t v___x_910_; size_t v___x_911_; size_t v___x_912_; size_t v___x_913_; size_t v___x_914_; lean_object* v_bkt_915_; uint8_t v___x_916_; 
v___x_902_ = lean_array_get_size(v_buckets_898_);
v___x_903_ = l_Lean_ExprStructEq_hash(v_a_895_);
v___x_904_ = 32ULL;
v___x_905_ = lean_uint64_shift_right(v___x_903_, v___x_904_);
v_fold_906_ = lean_uint64_xor(v___x_903_, v___x_905_);
v___x_907_ = 16ULL;
v___x_908_ = lean_uint64_shift_right(v_fold_906_, v___x_907_);
v___x_909_ = lean_uint64_xor(v_fold_906_, v___x_908_);
v___x_910_ = lean_uint64_to_usize(v___x_909_);
v___x_911_ = lean_usize_of_nat(v___x_902_);
v___x_912_ = ((size_t)1ULL);
v___x_913_ = lean_usize_sub(v___x_911_, v___x_912_);
v___x_914_ = lean_usize_land(v___x_910_, v___x_913_);
v_bkt_915_ = lean_array_uget_borrowed(v_buckets_898_, v___x_914_);
v___x_916_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(v_a_895_, v_bkt_915_);
if (v___x_916_ == 0)
{
lean_object* v___x_917_; lean_object* v_size_x27_918_; lean_object* v___x_919_; lean_object* v_buckets_x27_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; uint8_t v___x_926_; 
v___x_917_ = lean_unsigned_to_nat(1u);
v_size_x27_918_ = lean_nat_add(v_size_897_, v___x_917_);
lean_dec(v_size_897_);
lean_inc(v_bkt_915_);
v___x_919_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_919_, 0, v_a_895_);
lean_ctor_set(v___x_919_, 1, v_b_896_);
lean_ctor_set(v___x_919_, 2, v_bkt_915_);
v_buckets_x27_920_ = lean_array_uset(v_buckets_898_, v___x_914_, v___x_919_);
v___x_921_ = lean_unsigned_to_nat(4u);
v___x_922_ = lean_nat_mul(v_size_x27_918_, v___x_921_);
v___x_923_ = lean_unsigned_to_nat(3u);
v___x_924_ = lean_nat_div(v___x_922_, v___x_923_);
lean_dec(v___x_922_);
v___x_925_ = lean_array_get_size(v_buckets_x27_920_);
v___x_926_ = lean_nat_dec_le(v___x_924_, v___x_925_);
lean_dec(v___x_924_);
if (v___x_926_ == 0)
{
lean_object* v_val_927_; lean_object* v___x_929_; 
v_val_927_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11___redArg(v_buckets_x27_920_);
if (v_isShared_901_ == 0)
{
lean_ctor_set(v___x_900_, 1, v_val_927_);
lean_ctor_set(v___x_900_, 0, v_size_x27_918_);
v___x_929_ = v___x_900_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_size_x27_918_);
lean_ctor_set(v_reuseFailAlloc_930_, 1, v_val_927_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
else
{
lean_object* v___x_932_; 
if (v_isShared_901_ == 0)
{
lean_ctor_set(v___x_900_, 1, v_buckets_x27_920_);
lean_ctor_set(v___x_900_, 0, v_size_x27_918_);
v___x_932_ = v___x_900_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_size_x27_918_);
lean_ctor_set(v_reuseFailAlloc_933_, 1, v_buckets_x27_920_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
else
{
lean_object* v___x_934_; lean_object* v_buckets_x27_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_939_; 
lean_inc(v_bkt_915_);
v___x_934_ = lean_box(0);
v_buckets_x27_935_ = lean_array_uset(v_buckets_898_, v___x_914_, v___x_934_);
v___x_936_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12___redArg(v_a_895_, v_b_896_, v_bkt_915_);
v___x_937_ = lean_array_uset(v_buckets_x27_935_, v___x_914_, v___x_936_);
if (v_isShared_901_ == 0)
{
lean_ctor_set(v___x_900_, 1, v___x_937_);
v___x_939_ = v___x_900_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_size_897_);
lean_ctor_set(v_reuseFailAlloc_940_, 1, v___x_937_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2(lean_object* v_a_942_, lean_object* v_e_943_, lean_object* v_a_944_){
_start:
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_946_ = lean_st_ref_take(v_a_942_);
v___x_947_ = lean_box(0);
v___x_948_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6___redArg(v___x_946_, v_e_943_, v_a_944_);
v___x_949_ = lean_st_ref_put(v_a_942_, v___x_948_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2___boxed(lean_object* v_a_950_, lean_object* v_e_951_, lean_object* v_a_952_, lean_object* v___y_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2(v_a_950_, v_e_951_, v_a_952_);
lean_dec(v_a_950_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_a_955_, lean_object* v_x_956_){
_start:
{
if (lean_obj_tag(v_x_956_) == 0)
{
lean_object* v___x_957_; 
v___x_957_ = lean_box(0);
return v___x_957_;
}
else
{
lean_object* v_key_958_; lean_object* v_value_959_; lean_object* v_tail_960_; uint8_t v___x_961_; 
v_key_958_ = lean_ctor_get(v_x_956_, 0);
v_value_959_ = lean_ctor_get(v_x_956_, 1);
v_tail_960_ = lean_ctor_get(v_x_956_, 2);
v___x_961_ = l_Lean_ExprStructEq_beq(v_key_958_, v_a_955_);
if (v___x_961_ == 0)
{
v_x_956_ = v_tail_960_;
goto _start;
}
else
{
lean_object* v___x_963_; 
lean_inc(v_value_959_);
v___x_963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_963_, 0, v_value_959_);
return v___x_963_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_a_964_, lean_object* v_x_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1_spec__2___redArg(v_a_964_, v_x_965_);
lean_dec(v_x_965_);
lean_dec_ref(v_a_964_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1___redArg(lean_object* v_m_967_, lean_object* v_a_968_){
_start:
{
lean_object* v_buckets_969_; lean_object* v___x_970_; uint64_t v___x_971_; uint64_t v___x_972_; uint64_t v___x_973_; uint64_t v_fold_974_; uint64_t v___x_975_; uint64_t v___x_976_; uint64_t v___x_977_; size_t v___x_978_; size_t v___x_979_; size_t v___x_980_; size_t v___x_981_; size_t v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v_buckets_969_ = lean_ctor_get(v_m_967_, 1);
v___x_970_ = lean_array_get_size(v_buckets_969_);
v___x_971_ = l_Lean_ExprStructEq_hash(v_a_968_);
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
v___x_983_ = lean_array_uget_borrowed(v_buckets_969_, v___x_982_);
v___x_984_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1_spec__2___redArg(v_a_968_, v___x_983_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_m_985_, lean_object* v_a_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1___redArg(v_m_985_, v_a_986_);
lean_dec_ref(v_a_986_);
lean_dec_ref(v_m_985_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_988_, lean_object* v_x_989_, lean_object* v___y_990_, lean_object* v___y_991_){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_993_ = lean_apply_1(v_x_989_, lean_box(0));
v___x_994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_994_, 0, v___x_993_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_995_, lean_object* v_x_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(v_00_u03b1_995_, v_x_996_, v___y_997_, v___y_998_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
return v_res_1000_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0(void){
_start:
{
lean_object* v___x_1002_; lean_object* v_dummy_1003_; 
v___x_1002_ = lean_box(0);
v_dummy_1003_ = l_Lean_Expr_sort___override(v___x_1002_);
return v_dummy_1003_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(lean_object* v_pre_1004_, lean_object* v_post_1005_, size_t v_sz_1006_, size_t v_i_1007_, lean_object* v_bs_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
uint8_t v___x_1013_; 
v___x_1013_ = lean_usize_dec_lt(v_i_1007_, v_sz_1006_);
if (v___x_1013_ == 0)
{
lean_object* v___x_1014_; 
lean_dec_ref(v_post_1005_);
lean_dec_ref(v_pre_1004_);
v___x_1014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1014_, 0, v_bs_1008_);
return v___x_1014_;
}
else
{
lean_object* v_v_1015_; lean_object* v___x_1016_; lean_object* v_bs_x27_1017_; lean_object* v___x_1018_; 
v_v_1015_ = lean_array_uget(v_bs_1008_, v_i_1007_);
v___x_1016_ = lean_unsigned_to_nat(0u);
v_bs_x27_1017_ = lean_array_uset(v_bs_1008_, v_i_1007_, v___x_1016_);
lean_inc_ref(v_post_1005_);
lean_inc_ref(v_pre_1004_);
v___x_1018_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1004_, v_post_1005_, v_v_1015_, v___y_1009_, v___y_1010_, v___y_1011_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v_a_1019_; size_t v___x_1020_; size_t v___x_1021_; lean_object* v___x_1022_; 
v_a_1019_ = lean_ctor_get(v___x_1018_, 0);
lean_inc(v_a_1019_);
lean_dec_ref_known(v___x_1018_, 1);
v___x_1020_ = ((size_t)1ULL);
v___x_1021_ = lean_usize_add(v_i_1007_, v___x_1020_);
v___x_1022_ = lean_array_uset(v_bs_x27_1017_, v_i_1007_, v_a_1019_);
v_i_1007_ = v___x_1021_;
v_bs_1008_ = v___x_1022_;
goto _start;
}
else
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1031_; 
lean_dec_ref(v_bs_x27_1017_);
lean_dec_ref(v_post_1005_);
lean_dec_ref(v_pre_1004_);
v_a_1024_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1026_ = v___x_1018_;
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_1018_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1029_; 
if (v_isShared_1027_ == 0)
{
v___x_1029_ = v___x_1026_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_a_1024_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4(lean_object* v_pre_1032_, lean_object* v_post_1033_, lean_object* v___y_1034_, lean_object* v_x_1035_, lean_object* v_x_1036_, lean_object* v_x_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
if (lean_obj_tag(v_x_1035_) == 5)
{
lean_object* v_fn_1042_; lean_object* v_arg_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
v_fn_1042_ = lean_ctor_get(v_x_1035_, 0);
lean_inc_ref(v_fn_1042_);
v_arg_1043_ = lean_ctor_get(v_x_1035_, 1);
lean_inc_ref(v_arg_1043_);
lean_dec_ref_known(v_x_1035_, 2);
v___x_1044_ = lean_array_set(v_x_1036_, v_x_1037_, v_arg_1043_);
v___x_1045_ = lean_unsigned_to_nat(1u);
v___x_1046_ = lean_nat_sub(v_x_1037_, v___x_1045_);
lean_dec(v_x_1037_);
v_x_1035_ = v_fn_1042_;
v_x_1036_ = v___x_1044_;
v_x_1037_ = v___x_1046_;
goto _start;
}
else
{
lean_object* v___x_1048_; 
lean_dec(v_x_1037_);
lean_inc_ref(v_post_1033_);
lean_inc_ref(v_pre_1032_);
v___x_1048_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1032_, v_post_1033_, v_x_1035_, v___y_1038_, v___y_1039_, v___y_1040_);
if (lean_obj_tag(v___x_1048_) == 0)
{
lean_object* v_a_1049_; size_t v_sz_1050_; size_t v___x_1051_; lean_object* v___x_1052_; 
v_a_1049_ = lean_ctor_get(v___x_1048_, 0);
lean_inc(v_a_1049_);
lean_dec_ref_known(v___x_1048_, 1);
v_sz_1050_ = lean_array_size(v_x_1036_);
v___x_1051_ = ((size_t)0ULL);
v___x_1052_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1032_, v_post_1033_, v_sz_1050_, v___x_1051_, v_x_1036_, v___y_1038_, v___y_1039_, v___y_1040_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1061_; 
v_a_1053_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1055_ = v___x_1052_;
v_isShared_1056_ = v_isSharedCheck_1061_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1052_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1061_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1057_; lean_object* v___x_1059_; 
v___x_1057_ = l_Lean_Expr_updateAppN(v___y_1034_, v_a_1049_, v_a_1053_);
lean_dec(v_a_1053_);
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 0, v___x_1057_);
v___x_1059_ = v___x_1055_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1057_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
else
{
lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1069_; 
lean_dec(v_a_1049_);
v_a_1062_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1064_ = v___x_1052_;
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v___x_1052_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1067_; 
if (v_isShared_1065_ == 0)
{
v___x_1067_ = v___x_1064_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_a_1062_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
else
{
lean_dec_ref(v_x_1036_);
lean_dec_ref(v_post_1033_);
lean_dec_ref(v_pre_1032_);
return v___x_1048_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1(lean_object* v___x_1070_, lean_object* v_pre_1071_, lean_object* v_e_1072_, lean_object* v_post_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_){
_start:
{
lean_object* v___x_1078_; 
v___x_1078_ = l_Lean_Core_checkSystem(v___x_1070_, v___y_1075_, v___y_1076_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_object* v___x_1079_; 
lean_dec_ref_known(v___x_1078_, 1);
lean_inc_ref(v_pre_1071_);
lean_inc(v___y_1076_);
lean_inc_ref(v___y_1075_);
lean_inc_ref(v_e_1072_);
v___x_1079_ = lean_apply_4(v_pre_1071_, v_e_1072_, v___y_1075_, v___y_1076_, lean_box(0));
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1197_; 
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1197_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1082_ = v___x_1079_;
v_isShared_1083_ = v_isSharedCheck_1197_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1079_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1197_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___y_1085_; 
switch(lean_obj_tag(v_a_1080_))
{
case 0:
{
lean_object* v_e_1187_; lean_object* v___x_1189_; 
lean_dec_ref(v_post_1073_);
lean_dec_ref(v_e_1072_);
lean_dec_ref(v_pre_1071_);
v_e_1187_ = lean_ctor_get(v_a_1080_, 0);
lean_inc_ref(v_e_1187_);
lean_dec_ref_known(v_a_1080_, 1);
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 0, v_e_1187_);
v___x_1189_ = v___x_1082_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_e_1187_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
case 1:
{
lean_object* v_e_1191_; lean_object* v___x_1192_; 
lean_del_object(v___x_1082_);
lean_dec_ref(v_e_1072_);
v_e_1191_ = lean_ctor_get(v_a_1080_, 0);
lean_inc_ref(v_e_1191_);
lean_dec_ref_known(v_a_1080_, 1);
lean_inc_ref(v_post_1073_);
lean_inc_ref(v_pre_1071_);
v___x_1192_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1071_, v_post_1073_, v_e_1191_, v___y_1074_, v___y_1075_, v___y_1076_);
if (lean_obj_tag(v___x_1192_) == 0)
{
lean_object* v_a_1193_; lean_object* v___x_1194_; 
v_a_1193_ = lean_ctor_get(v___x_1192_, 0);
lean_inc(v_a_1193_);
lean_dec_ref_known(v___x_1192_, 1);
v___x_1194_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3(v_pre_1071_, v_post_1073_, v_a_1193_, v___y_1074_, v___y_1075_, v___y_1076_);
return v___x_1194_;
}
else
{
lean_dec_ref(v_post_1073_);
lean_dec_ref(v_pre_1071_);
return v___x_1192_;
}
}
default: 
{
lean_object* v_e_x3f_1195_; 
lean_del_object(v___x_1082_);
v_e_x3f_1195_ = lean_ctor_get(v_a_1080_, 0);
lean_inc(v_e_x3f_1195_);
lean_dec_ref_known(v_a_1080_, 1);
if (lean_obj_tag(v_e_x3f_1195_) == 0)
{
v___y_1085_ = v_e_1072_;
goto v___jp_1084_;
}
else
{
lean_object* v_val_1196_; 
lean_dec_ref(v_e_1072_);
v_val_1196_ = lean_ctor_get(v_e_x3f_1195_, 0);
lean_inc(v_val_1196_);
lean_dec_ref_known(v_e_x3f_1195_, 1);
v___y_1085_ = v_val_1196_;
goto v___jp_1084_;
}
}
}
v___jp_1084_:
{
switch(lean_obj_tag(v___y_1085_))
{
case 7:
{
lean_object* v_binderName_1086_; lean_object* v_binderType_1087_; lean_object* v_body_1088_; uint8_t v_binderInfo_1089_; lean_object* v___x_1090_; 
v_binderName_1086_ = lean_ctor_get(v___y_1085_, 0);
v_binderType_1087_ = lean_ctor_get(v___y_1085_, 1);
v_body_1088_ = lean_ctor_get(v___y_1085_, 2);
v_binderInfo_1089_ = lean_ctor_get_uint8(v___y_1085_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1087_);
lean_inc_ref(v_post_1073_);
lean_inc_ref(v_pre_1071_);
v___x_1090_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1071_, v_post_1073_, v_binderType_1087_, v___y_1074_, v___y_1075_, v___y_1076_);
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_object* v_a_1091_; lean_object* v___x_1092_; 
v_a_1091_ = lean_ctor_get(v___x_1090_, 0);
lean_inc(v_a_1091_);
lean_dec_ref_known(v___x_1090_, 1);
lean_inc_ref(v_body_1088_);
lean_inc_ref(v_post_1073_);
lean_inc_ref(v_pre_1071_);
v___x_1092_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1071_, v_post_1073_, v_body_1088_, v___y_1074_, v___y_1075_, v___y_1076_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_object* v_a_1093_; size_t v___x_1094_; size_t v___x_1095_; uint8_t v___x_1096_; 
v_a_1093_ = lean_ctor_get(v___x_1092_, 0);
lean_inc(v_a_1093_);
lean_dec_ref_known(v___x_1092_, 1);
v___x_1094_ = lean_ptr_addr(v_binderType_1087_);
v___x_1095_ = lean_ptr_addr(v_a_1091_);
v___x_1096_ = lean_usize_dec_eq(v___x_1094_, v___x_1095_);
if (v___x_1096_ == 0)
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
lean_inc(v_binderName_1086_);
lean_dec_ref_known(v___y_1085_, 3);
v___x_1097_ = l_Lean_Expr_forallE___override(v_binderName_1086_, v_a_1091_, v_a_1093_, v_binderInfo_1089_);
v___x_1098_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3(v_pre_1071_, v_post_1073_, v___x_1097_, v___y_1074_, v___y_1075_, v___y_1076_);
return v___x_1098_;
}
else
{
size_t v___x_1099_; size_t v___x_1100_; uint8_t v___x_1101_; 
v___x_1099_ = lean_ptr_addr(v_body_1088_);
v___x_1100_ = lean_ptr_addr(v_a_1093_);
v___x_1101_ = lean_usize_dec_eq(v___x_1099_, v___x_1100_);
if (v___x_1101_ == 0)
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
lean_inc(v_binderName_1086_);
lean_dec_ref_known(v___y_1085_, 3);
v___x_1102_ = l_Lean_Expr_forallE___override(v_binderName_1086_, v_a_1091_, v_a_1093_, v_binderInfo_1089_);
v___x_1103_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3(v_pre_1071_, v_post_1073_, v___x_1102_, v___y_1074_, v___y_1075_, v___y_1076_);
return v___x_1103_;
}
else
{
uint8_t v___x_1104_; 
v___x_1104_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1089_, v_binderInfo_1089_);
if (v___x_1104_ == 0)
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
lean_inc(v_binderName_1086_);
lean_dec_ref_known(v___y_1085_, 3);
v___x_1105_ = l_Lean_Expr_forallE___override(v_binderName_1086_, v_a_1091_, v_a_1093_, v_binderInfo_1089_);
v___x_1106_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3(v_pre_1071_, v_post_1073_, v___x_1105_, v___y_1074_, v___y_1075_, v___y_1076_);
return v___x_1106_;
}
else
{
lean_object* v___x_1107_; 
lean_dec(v_a_1093_);
lean_dec(v_a_1091_);
v___x_1107_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3(v_pre_1071_, v_post_1073_, v___y_1085_, v___y_1074_, v___y_1075_, v___y_1076_);
return v___x_1107_;
}
}
}
}
else
{
lean_dec(v_a_1091_);
lean_dec_ref_known(v___y_1085_, 3);
lean_dec_ref(v_post_1073_);
lean_dec_ref(v_pre_1071_);
return v___x_1092_;
}
}
else
{
lean_dec_ref_known(v___y_1085_, 3);
lean_dec_ref(v_post_1073_);
lean_dec_ref(v_pre_1071_);
return v___x_1090_;
}
}
case 6:
{
lean_object* v_binderName_1108_; lean_object* v_binderType_1109_; lean_object* v_body_1110_; uint8_t v_binderInfo_1111_; lean_object* v___x_1112_; 
v_binderName_1108_ = lean_ctor_get(v___y_1085_, 0);
v_binderType_1109_ = lean_ctor_get(v___y_1085_, 1);
v_body_1110_ = lean_ctor_get(v___y_1085_, 2);
v_binderInfo_1111_ = lean_ctor_get_uint8(v___y_1085_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1109_);
lean_inc_ref(v_post_1073_);
lean_inc_ref(v_pre_1071_);
v___x_1112_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1071_, v_post_1073_, v_binderType_1109_, v___y_1074_, v___y_1075_, v___y_1076_);
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v_a_1113_; lean_object* v___x_1114_; 
v_a_1113_ = lean_ctor_get(v___x_1112_, 0);
lean_inc(v_a_1113_);
lean_dec_ref_known(v___x_1112_, 1);
lean_inc_ref(v_body_1110_);
lean_inc_ref(v_post_1073_);
lean_inc_ref(v_pre_1071_);
v___x_1114_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1071_, v_post_1073_, v_body_1110_, v___y_1074_, v___y_1075_, v___y_1076_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v_a_1115_; size_t v___x_1116_; size_t v___x_1117_; uint8_t v___x_1118_; 
v_a_1115_ = lean_ctor_get(v___x_1114_, 0);
lean_inc(v_a_1115_);
lean_dec_ref_known(v___x_1114_, 1);
v___x_1116_ = lean_ptr_addr(v_binderType_1109_);
v___x_1117_ = lean_ptr_addr(v_a_1113_);
v___x_1118_ = lean_usize_dec_eq(v___x_1116_, v___x_1117_);
if (v___x_1118_ == 0)
{
lean_object* v___x_1119_; lean_object* v___x_1120_; 
lean_inc(v_binderName_1108_);
lean_dec_ref_known(v___y_1085_, 3);
v___x_1119_ = l_Lean_Expr_lam___override(v_binderName_1108_, v_a_1113_, v_a_1115_, v_binderInfo_1111_);
v___x_1120_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3(v_pre_1071_, v_post_1073_, v___x_1119_, v___y_1074_, v___y_1075_, v___y_1076_);
return v___x_1120_;
}
else
{
size_t v___x_1121_; size_t v___x_1122_; uint8_t v___x_1123_; 
v___x_1121_ = lean_ptr_addr(v_body_1110_);
v___x_1122_ = lean_ptr_addr(v_a_1115_);
v___x_1123_ = lean_usize_dec_eq(v___x_1121_, v___x_1122_);
if (v___x_1123_ == 0)
{
lean_object* v___x_1124_; lean_object* v___x_1125_; 
lean_inc(v_binderName_1108_);
lean_dec_ref_known(v___y_1085_, 3);
v___x_1124_ = l_Lean_Expr_lam___override(v_binderName_1108_, v_a_1113_, v_a_1115_, v_binderInfo_1111_);
v___x_1125_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3(v_pre_1071_, v_post_1073_, v___x_1124_, v___y_1074_, v___y_1075_, v___y_1076_);
return v___x_1125_;
}
else
{
uint8_t v___x_1126_; 
v___x_1126_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1111_, v_binderInfo_1111_);
if (v___x_1126_ == 0)
{
lean_object* v___x_1127_; lean_object* v___x_1128_; 
lean_inc(v_binderName_1108_);
lean_dec_ref_known(v___y_1085_, 3);
v___x_1127_ = l_Lean_Expr_lam___override(v_binderName_1108_, v_a_1113_, v_a_1115_, v_binderInfo_1111_);
v___x_1128_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3(v_pre_1071_, v_post_1073_, v___x_1127_, v___y_1074_, v___y_1075_, v___y_1076_);
return v___x_1128_;
}
else
{
lean_object* v___x_1129_; 
lean_dec(v_a_1115_);
lean_dec(v_a_1113_);
v___x_1129_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3(v_pre_1071_, v_post_1073_, v___y_1085_, v___y_1074_, v___y_1075_, v___y_1076_);
return v___x_1129_;
}
}
}
}
else
{
lean_dec(v_a_1113_);
lean_dec_ref_known(v___y_1085_, 3);
lean_dec_ref(v_post_1073_);
lean_dec_ref(v_pre_1071_);
return v___x_1114_;
}
}
else
{
lean_dec_ref_known(v___y_1085_, 3);
lean_dec_ref(v_post_1073_);
lean_dec_ref(v_pre_1071_);
return v___x_1112_;
}
}
case 8:
{
lean_object* v_declName_1130_; lean_object* v_type_1131_; lean_object* v_value_1132_; lean_object* v_body_1133_; uint8_t v_nondep_1134_; lean_object* v___x_1135_; 
v_declName_1130_ = lean_ctor_get(v___y_1085_, 0);
v_type_1131_ = lean_ctor_get(v___y_1085_, 1);
v_value_1132_ = lean_ctor_get(v___y_1085_, 2);
v_body_1133_ = lean_ctor_get(v___y_1085_, 3);
v_nondep_1134_ = lean_ctor_get_uint8(v___y_1085_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_1131_);
lean_inc_ref(v_post_1073_);
lean_inc_ref(v_pre_1071_);
v___x_1135_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1071_, v_post_1073_, v_type_1131_, v___y_1074_, v___y_1075_, v___y_1076_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v_a_1136_; lean_object* v___x_1137_; 
v_a_1136_ = lean_ctor_get(v___x_1135_, 0);
lean_inc(v_a_1136_);
lean_dec_ref_known(v___x_1135_, 1);
lean_inc_ref(v_value_1132_);
lean_inc_ref(v_post_1073_);
lean_inc_ref(v_pre_1071_);
v___x_1137_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1071_, v_post_1073_, v_value_1132_, v___y_1074_, v___y_1075_, v___y_1076_);
if (lean_obj_tag(v___x_1137_) == 0)
{
lean_object* v_a_1138_; lean_object* v___x_1139_; 
v_a_1138_ = lean_ctor_get(v___x_1137_, 0);
lean_inc(v_a_1138_);
lean_dec_ref_known(v___x_1137_, 1);
lean_inc_ref(v_body_1133_);
lean_inc_ref(v_post_1073_);
lean_inc_ref(v_pre_1071_);
v___x_1139_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1071_, v_post_1073_, v_body_1133_, v___y_1074_, v___y_1075_, v___y_1076_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v_a_1140_; size_t v___x_1141_; size_t v___x_1142_; uint8_t v___x_1143_; 
v_a_1140_ = lean_ctor_get(v___x_1139_, 0);
lean_inc(v_a_1140_);
lean_dec_ref_known(v___x_1139_, 1);
v___x_1141_ = lean_ptr_addr(v_type_1131_);
v___x_1142_ = lean_ptr_addr(v_a_1136_);
v___x_1143_ = lean_usize_dec_eq(v___x_1141_, v___x_1142_);
if (v___x_1143_ == 0)
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
lean_inc(v_declName_1130_);
lean_dec_ref_known(v___y_1085_, 4);
v___x_1144_ = l_Lean_Expr_letE___override(v_declName_1130_, v_a_1136_, v_a_1138_, v_a_1140_, v_nondep_1134_);
v___x_1145_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3(v_pre_1071_, v_post_1073_, v___x_1144_, v___y_1074_, v___y_1075_, v___y_1076_);
return v___x_1145_;
}
else
{
size_t v___x_1146_; size_t v___x_1147_; uint8_t v___x_1148_; 
v___x_1146_ = lean_ptr_addr(v_value_1132_);
v___x_1147_ = lean_ptr_addr(v_a_1138_);
v___x_1148_ = lean_usize_dec_eq(v___x_1146_, v___x_1147_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
lean_inc(v_declName_1130_);
lean_dec_ref_known(v___y_1085_, 4);
v___x_1149_ = l_Lean_Expr_letE___override(v_declName_1130_, v_a_1136_, v_a_1138_, v_a_1140_, v_nondep_1134_);
v___x_1150_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3(v_pre_1071_, v_post_1073_, v___x_1149_, v___y_1074_, v___y_1075_, v___y_1076_);
return v___x_1150_;
}
else
{
size_t v___x_1151_; size_t v___x_1152_; uint8_t v___x_1153_; 
v___x_1151_ = lean_ptr_addr(v_body_1133_);
v___x_1152_ = lean_ptr_addr(v_a_1140_);
v___x_1153_ = lean_usize_dec_eq(v___x_1151_, v___x_1152_);
if (v___x_1153_ == 0)
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
lean_inc(v_declName_1130_);
lean_dec_ref_known(v___y_1085_, 4);
v___x_1154_ = l_Lean_Expr_letE___override(v_declName_1130_, v_a_1136_, v_a_1138_, v_a_1140_, v_nondep_1134_);
v___x_1155_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3(v_pre_1071_, v_post_1073_, v___x_1154_, v___y_1074_, v___y_1075_, v___y_1076_);
return v___x_1155_;
}
else
{
lean_object* v___x_1156_; 
lean_dec(v_a_1140_);
lean_dec(v_a_1138_);
lean_dec(v_a_1136_);
v___x_1156_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3(v_pre_1071_, v_post_1073_, v___y_1085_, v___y_1074_, v___y_1075_, v___y_1076_);
return v___x_1156_;
}
}
}
}
else
{
lean_dec(v_a_1138_);
lean_dec(v_a_1136_);
lean_dec_ref_known(v___y_1085_, 4);
lean_dec_ref(v_post_1073_);
lean_dec_ref(v_pre_1071_);
return v___x_1139_;
}
}
else
{
lean_dec(v_a_1136_);
lean_dec_ref_known(v___y_1085_, 4);
lean_dec_ref(v_post_1073_);
lean_dec_ref(v_pre_1071_);
return v___x_1137_;
}
}
else
{
lean_dec_ref_known(v___y_1085_, 4);
lean_dec_ref(v_post_1073_);
lean_dec_ref(v_pre_1071_);
return v___x_1135_;
}
}
case 5:
{
lean_object* v_dummy_1157_; lean_object* v_nargs_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v_dummy_1157_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0);
v_nargs_1158_ = l_Lean_Expr_getAppNumArgs(v___y_1085_);
lean_inc(v_nargs_1158_);
v___x_1159_ = lean_mk_array(v_nargs_1158_, v_dummy_1157_);
v___x_1160_ = lean_unsigned_to_nat(1u);
v___x_1161_ = lean_nat_sub(v_nargs_1158_, v___x_1160_);
lean_dec(v_nargs_1158_);
lean_inc_ref(v___y_1085_);
lean_inc_ref(v_post_1073_);
lean_inc_ref(v_pre_1071_);
v___x_1162_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4(v_pre_1071_, v_post_1073_, v___y_1085_, v___y_1085_, v___x_1159_, v___x_1161_, v___y_1074_, v___y_1075_, v___y_1076_);
lean_dec_ref_known(v___y_1085_, 2);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v_a_1163_; lean_object* v___x_1164_; 
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
lean_inc(v_a_1163_);
lean_dec_ref_known(v___x_1162_, 1);
v___x_1164_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3(v_pre_1071_, v_post_1073_, v_a_1163_, v___y_1074_, v___y_1075_, v___y_1076_);
return v___x_1164_;
}
else
{
lean_dec_ref(v_post_1073_);
lean_dec_ref(v_pre_1071_);
return v___x_1162_;
}
}
case 10:
{
lean_object* v_data_1165_; lean_object* v_expr_1166_; lean_object* v___x_1167_; 
v_data_1165_ = lean_ctor_get(v___y_1085_, 0);
v_expr_1166_ = lean_ctor_get(v___y_1085_, 1);
lean_inc_ref(v_expr_1166_);
lean_inc_ref(v_post_1073_);
lean_inc_ref(v_pre_1071_);
v___x_1167_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1071_, v_post_1073_, v_expr_1166_, v___y_1074_, v___y_1075_, v___y_1076_);
if (lean_obj_tag(v___x_1167_) == 0)
{
lean_object* v_a_1168_; size_t v___x_1169_; size_t v___x_1170_; uint8_t v___x_1171_; 
v_a_1168_ = lean_ctor_get(v___x_1167_, 0);
lean_inc(v_a_1168_);
lean_dec_ref_known(v___x_1167_, 1);
v___x_1169_ = lean_ptr_addr(v_expr_1166_);
v___x_1170_ = lean_ptr_addr(v_a_1168_);
v___x_1171_ = lean_usize_dec_eq(v___x_1169_, v___x_1170_);
if (v___x_1171_ == 0)
{
lean_object* v___x_1172_; lean_object* v___x_1173_; 
lean_inc(v_data_1165_);
lean_dec_ref_known(v___y_1085_, 2);
v___x_1172_ = l_Lean_Expr_mdata___override(v_data_1165_, v_a_1168_);
v___x_1173_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3(v_pre_1071_, v_post_1073_, v___x_1172_, v___y_1074_, v___y_1075_, v___y_1076_);
return v___x_1173_;
}
else
{
lean_object* v___x_1174_; 
lean_dec(v_a_1168_);
v___x_1174_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3(v_pre_1071_, v_post_1073_, v___y_1085_, v___y_1074_, v___y_1075_, v___y_1076_);
return v___x_1174_;
}
}
else
{
lean_dec_ref_known(v___y_1085_, 2);
lean_dec_ref(v_post_1073_);
lean_dec_ref(v_pre_1071_);
return v___x_1167_;
}
}
case 11:
{
lean_object* v_typeName_1175_; lean_object* v_idx_1176_; lean_object* v_struct_1177_; lean_object* v___x_1178_; 
v_typeName_1175_ = lean_ctor_get(v___y_1085_, 0);
v_idx_1176_ = lean_ctor_get(v___y_1085_, 1);
v_struct_1177_ = lean_ctor_get(v___y_1085_, 2);
lean_inc_ref(v_struct_1177_);
lean_inc_ref(v_post_1073_);
lean_inc_ref(v_pre_1071_);
v___x_1178_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1071_, v_post_1073_, v_struct_1177_, v___y_1074_, v___y_1075_, v___y_1076_);
if (lean_obj_tag(v___x_1178_) == 0)
{
lean_object* v_a_1179_; size_t v___x_1180_; size_t v___x_1181_; uint8_t v___x_1182_; 
v_a_1179_ = lean_ctor_get(v___x_1178_, 0);
lean_inc(v_a_1179_);
lean_dec_ref_known(v___x_1178_, 1);
v___x_1180_ = lean_ptr_addr(v_struct_1177_);
v___x_1181_ = lean_ptr_addr(v_a_1179_);
v___x_1182_ = lean_usize_dec_eq(v___x_1180_, v___x_1181_);
if (v___x_1182_ == 0)
{
lean_object* v___x_1183_; lean_object* v___x_1184_; 
lean_inc(v_idx_1176_);
lean_inc(v_typeName_1175_);
lean_dec_ref_known(v___y_1085_, 3);
v___x_1183_ = l_Lean_Expr_proj___override(v_typeName_1175_, v_idx_1176_, v_a_1179_);
v___x_1184_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3(v_pre_1071_, v_post_1073_, v___x_1183_, v___y_1074_, v___y_1075_, v___y_1076_);
return v___x_1184_;
}
else
{
lean_object* v___x_1185_; 
lean_dec(v_a_1179_);
v___x_1185_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3(v_pre_1071_, v_post_1073_, v___y_1085_, v___y_1074_, v___y_1075_, v___y_1076_);
return v___x_1185_;
}
}
else
{
lean_dec_ref_known(v___y_1085_, 3);
lean_dec_ref(v_post_1073_);
lean_dec_ref(v_pre_1071_);
return v___x_1178_;
}
}
default: 
{
lean_object* v___x_1186_; 
v___x_1186_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3(v_pre_1071_, v_post_1073_, v___y_1085_, v___y_1074_, v___y_1075_, v___y_1076_);
return v___x_1186_;
}
}
}
}
}
else
{
lean_object* v_a_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1205_; 
lean_dec_ref(v_post_1073_);
lean_dec_ref(v_e_1072_);
lean_dec_ref(v_pre_1071_);
v_a_1198_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1200_ = v___x_1079_;
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_a_1198_);
lean_dec(v___x_1079_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1203_; 
if (v_isShared_1201_ == 0)
{
v___x_1203_ = v___x_1200_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_a_1198_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
}
}
else
{
lean_object* v_a_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1213_; 
lean_dec_ref(v_post_1073_);
lean_dec_ref(v_e_1072_);
lean_dec_ref(v_pre_1071_);
v_a_1206_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1208_ = v___x_1078_;
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_a_1206_);
lean_dec(v___x_1078_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1211_; 
if (v_isShared_1209_ == 0)
{
v___x_1211_ = v___x_1208_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_a_1206_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___boxed(lean_object* v___x_1214_, lean_object* v_pre_1215_, lean_object* v_e_1216_, lean_object* v_post_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1(v___x_1214_, v_pre_1215_, v_e_1216_, v_post_1217_, v___y_1218_, v___y_1219_, v___y_1220_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec(v___y_1218_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(lean_object* v_pre_1223_, lean_object* v_post_1224_, lean_object* v_e_1225_, lean_object* v_a_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_){
_start:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
lean_inc(v_a_1226_);
v___x_1230_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1230_, 0, lean_box(0));
lean_closure_set(v___x_1230_, 1, lean_box(0));
lean_closure_set(v___x_1230_, 2, v_a_1226_);
v___x_1231_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(lean_box(0), v___x_1230_, v___y_1227_, v___y_1228_);
if (lean_obj_tag(v___x_1231_) == 0)
{
lean_object* v_a_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1263_; 
v_a_1232_ = lean_ctor_get(v___x_1231_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1231_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1234_ = v___x_1231_;
v_isShared_1235_ = v_isSharedCheck_1263_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_a_1232_);
lean_dec(v___x_1231_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1263_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1236_; 
v___x_1236_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1___redArg(v_a_1232_, v_e_1225_);
lean_dec(v_a_1232_);
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_object* v___x_1237_; lean_object* v___f_1238_; lean_object* v___x_1239_; 
lean_del_object(v___x_1234_);
v___x_1237_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___closed__0));
lean_inc_ref(v_e_1225_);
v___f_1238_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___boxed), 8, 4);
lean_closure_set(v___f_1238_, 0, v___x_1237_);
lean_closure_set(v___f_1238_, 1, v_pre_1223_);
lean_closure_set(v___f_1238_, 2, v_e_1225_);
lean_closure_set(v___f_1238_, 3, v_post_1224_);
v___x_1239_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg(v___f_1238_, v_a_1226_, v___y_1227_, v___y_1228_);
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_object* v_a_1240_; lean_object* v___f_1241_; lean_object* v___x_1242_; 
v_a_1240_ = lean_ctor_get(v___x_1239_, 0);
lean_inc_n(v_a_1240_, 2);
lean_dec_ref_known(v___x_1239_, 1);
lean_inc(v_a_1226_);
v___f_1241_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1241_, 0, v_a_1226_);
lean_closure_set(v___f_1241_, 1, v_e_1225_);
lean_closure_set(v___f_1241_, 2, v_a_1240_);
v___x_1242_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(lean_box(0), v___f_1241_, v___y_1227_, v___y_1228_);
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1249_; 
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1249_ == 0)
{
lean_object* v_unused_1250_; 
v_unused_1250_ = lean_ctor_get(v___x_1242_, 0);
lean_dec(v_unused_1250_);
v___x_1244_ = v___x_1242_;
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
else
{
lean_dec(v___x_1242_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1247_; 
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 0, v_a_1240_);
v___x_1247_ = v___x_1244_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_a_1240_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
}
else
{
lean_object* v_a_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1258_; 
lean_dec(v_a_1240_);
v_a_1251_ = lean_ctor_get(v___x_1242_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1253_ = v___x_1242_;
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_a_1251_);
lean_dec(v___x_1242_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1256_; 
if (v_isShared_1254_ == 0)
{
v___x_1256_ = v___x_1253_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_a_1251_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
}
else
{
lean_dec_ref(v_e_1225_);
return v___x_1239_;
}
}
else
{
lean_object* v_val_1259_; lean_object* v___x_1261_; 
lean_dec_ref(v_e_1225_);
lean_dec_ref(v_post_1224_);
lean_dec_ref(v_pre_1223_);
v_val_1259_ = lean_ctor_get(v___x_1236_, 0);
lean_inc(v_val_1259_);
lean_dec_ref_known(v___x_1236_, 1);
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 0, v_val_1259_);
v___x_1261_ = v___x_1234_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_val_1259_);
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
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1271_; 
lean_dec_ref(v_e_1225_);
lean_dec_ref(v_post_1224_);
lean_dec_ref(v_pre_1223_);
v_a_1264_ = lean_ctor_get(v___x_1231_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1231_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1266_ = v___x_1231_;
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1231_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1269_; 
if (v_isShared_1267_ == 0)
{
v___x_1269_ = v___x_1266_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_a_1264_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3(lean_object* v_pre_1272_, lean_object* v_post_1273_, lean_object* v_e_1274_, lean_object* v_a_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_){
_start:
{
lean_object* v___x_1279_; 
lean_inc_ref(v_post_1273_);
lean_inc(v___y_1277_);
lean_inc_ref(v___y_1276_);
lean_inc_ref(v_e_1274_);
v___x_1279_ = lean_apply_4(v_post_1273_, v_e_1274_, v___y_1276_, v___y_1277_, lean_box(0));
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1298_; 
v_a_1280_ = lean_ctor_get(v___x_1279_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1282_ = v___x_1279_;
v_isShared_1283_ = v_isSharedCheck_1298_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_dec(v___x_1279_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1298_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
switch(lean_obj_tag(v_a_1280_))
{
case 0:
{
lean_object* v_e_1284_; lean_object* v___x_1286_; 
lean_dec_ref(v_e_1274_);
lean_dec_ref(v_post_1273_);
lean_dec_ref(v_pre_1272_);
v_e_1284_ = lean_ctor_get(v_a_1280_, 0);
lean_inc_ref(v_e_1284_);
lean_dec_ref_known(v_a_1280_, 1);
if (v_isShared_1283_ == 0)
{
lean_ctor_set(v___x_1282_, 0, v_e_1284_);
v___x_1286_ = v___x_1282_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_e_1284_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
case 1:
{
lean_object* v_e_1288_; lean_object* v___x_1289_; 
lean_del_object(v___x_1282_);
lean_dec_ref(v_e_1274_);
v_e_1288_ = lean_ctor_get(v_a_1280_, 0);
lean_inc_ref(v_e_1288_);
lean_dec_ref_known(v_a_1280_, 1);
v___x_1289_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1272_, v_post_1273_, v_e_1288_, v_a_1275_, v___y_1276_, v___y_1277_);
return v___x_1289_;
}
default: 
{
lean_object* v_e_x3f_1290_; 
lean_dec_ref(v_post_1273_);
lean_dec_ref(v_pre_1272_);
v_e_x3f_1290_ = lean_ctor_get(v_a_1280_, 0);
lean_inc(v_e_x3f_1290_);
lean_dec_ref_known(v_a_1280_, 1);
if (lean_obj_tag(v_e_x3f_1290_) == 0)
{
lean_object* v___x_1292_; 
if (v_isShared_1283_ == 0)
{
lean_ctor_set(v___x_1282_, 0, v_e_1274_);
v___x_1292_ = v___x_1282_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_e_1274_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
else
{
lean_object* v_val_1294_; lean_object* v___x_1296_; 
lean_dec_ref(v_e_1274_);
v_val_1294_ = lean_ctor_get(v_e_x3f_1290_, 0);
lean_inc(v_val_1294_);
lean_dec_ref_known(v_e_x3f_1290_, 1);
if (v_isShared_1283_ == 0)
{
lean_ctor_set(v___x_1282_, 0, v_val_1294_);
v___x_1296_ = v___x_1282_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_val_1294_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
}
}
else
{
lean_object* v_a_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1306_; 
lean_dec_ref(v_e_1274_);
lean_dec_ref(v_post_1273_);
lean_dec_ref(v_pre_1272_);
v_a_1299_ = lean_ctor_get(v___x_1279_, 0);
v_isSharedCheck_1306_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1301_ = v___x_1279_;
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_a_1299_);
lean_dec(v___x_1279_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1304_; 
if (v_isShared_1302_ == 0)
{
v___x_1304_ = v___x_1301_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_a_1299_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___boxed(lean_object* v_pre_1307_, lean_object* v_post_1308_, lean_object* v_e_1309_, lean_object* v_a_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_){
_start:
{
lean_object* v_res_1314_; 
v_res_1314_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3(v_pre_1307_, v_post_1308_, v_e_1309_, v_a_1310_, v___y_1311_, v___y_1312_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec(v_a_1310_);
return v_res_1314_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_1315_, lean_object* v_post_1316_, lean_object* v_sz_1317_, lean_object* v_i_1318_, lean_object* v_bs_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_){
_start:
{
size_t v_sz_boxed_1324_; size_t v_i_boxed_1325_; lean_object* v_res_1326_; 
v_sz_boxed_1324_ = lean_unbox_usize(v_sz_1317_);
lean_dec(v_sz_1317_);
v_i_boxed_1325_ = lean_unbox_usize(v_i_1318_);
lean_dec(v_i_1318_);
v_res_1326_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1315_, v_post_1316_, v_sz_boxed_1324_, v_i_boxed_1325_, v_bs_1319_, v___y_1320_, v___y_1321_, v___y_1322_);
lean_dec(v___y_1322_);
lean_dec_ref(v___y_1321_);
lean_dec(v___y_1320_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_1327_, lean_object* v_post_1328_, lean_object* v___y_1329_, lean_object* v_x_1330_, lean_object* v_x_1331_, lean_object* v_x_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4(v_pre_1327_, v_post_1328_, v___y_1329_, v_x_1330_, v_x_1331_, v_x_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1329_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___boxed(lean_object* v_pre_1338_, lean_object* v_post_1339_, lean_object* v_e_1340_, lean_object* v_a_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1338_, v_post_1339_, v_e_1340_, v_a_1341_, v___y_1342_, v___y_1343_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
lean_dec(v_a_1341_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(lean_object* v_00_u03b1_1346_, lean_object* v_x_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1351_ = lean_apply_1(v_x_1347_, lean_box(0));
v___x_1352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1351_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1353_, lean_object* v_x_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(v_00_u03b1_1353_, v_x_1354_, v___y_1355_, v___y_1356_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
return v_res_1358_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1359_ = lean_box(0);
v___x_1360_ = lean_unsigned_to_nat(16u);
v___x_1361_ = lean_mk_array(v___x_1360_, v___x_1359_);
return v___x_1361_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1362_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0, &l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0);
v___x_1363_ = lean_unsigned_to_nat(0u);
v___x_1364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1363_);
lean_ctor_set(v___x_1364_, 1, v___x_1362_);
return v___x_1364_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1365_; lean_object* v___x_1366_; 
v___x_1365_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1, &l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1_once, _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1);
v___x_1366_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1366_, 0, lean_box(0));
lean_closure_set(v___x_1366_, 1, lean_box(0));
lean_closure_set(v___x_1366_, 2, v___x_1365_);
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0(lean_object* v_input_1367_, lean_object* v_pre_1368_, lean_object* v_post_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v_a_1375_; lean_object* v___x_1376_; 
v___x_1373_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2);
v___x_1374_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(lean_box(0), v___x_1373_, v___y_1370_, v___y_1371_);
v_a_1375_ = lean_ctor_get(v___x_1374_, 0);
lean_inc(v_a_1375_);
lean_dec_ref(v___x_1374_);
v___x_1376_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1368_, v_post_1369_, v_input_1367_, v_a_1375_, v___y_1370_, v___y_1371_);
if (lean_obj_tag(v___x_1376_) == 0)
{
lean_object* v_a_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1386_; 
v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
lean_inc(v_a_1377_);
lean_dec_ref_known(v___x_1376_, 1);
v___x_1378_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1378_, 0, lean_box(0));
lean_closure_set(v___x_1378_, 1, lean_box(0));
lean_closure_set(v___x_1378_, 2, v_a_1375_);
v___x_1379_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(lean_box(0), v___x_1378_, v___y_1370_, v___y_1371_);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1386_ == 0)
{
lean_object* v_unused_1387_; 
v_unused_1387_ = lean_ctor_get(v___x_1379_, 0);
lean_dec(v_unused_1387_);
v___x_1381_ = v___x_1379_;
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
else
{
lean_dec(v___x_1379_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1384_; 
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 0, v_a_1377_);
v___x_1384_ = v___x_1381_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_a_1377_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
else
{
lean_dec(v_a_1375_);
return v___x_1376_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___boxed(lean_object* v_input_1388_, lean_object* v_pre_1389_, lean_object* v_post_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_){
_start:
{
lean_object* v_res_1394_; 
v_res_1394_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0(v_input_1388_, v_pre_1389_, v_post_1390_, v___y_1391_, v___y_1392_);
lean_dec(v___y_1392_);
lean_dec_ref(v___y_1391_);
return v_res_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(lean_object* v_e_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_){
_start:
{
lean_object* v___f_1401_; lean_object* v___f_1402_; lean_object* v___x_1403_; 
v___f_1401_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___closed__0));
v___f_1402_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___closed__1));
v___x_1403_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0(v_e_1397_, v___f_1401_, v___f_1402_, v_a_1398_, v_a_1399_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___boxed(lean_object* v_e_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(v_e_1404_, v_a_1405_, v_a_1406_);
lean_dec(v_a_1406_);
lean_dec_ref(v_a_1405_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1409_, lean_object* v_m_1410_, lean_object* v_a_1411_){
_start:
{
lean_object* v___x_1412_; 
v___x_1412_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1___redArg(v_m_1410_, v_a_1411_);
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1413_, lean_object* v_m_1414_, lean_object* v_a_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1(v_00_u03b2_1413_, v_m_1414_, v_a_1415_);
lean_dec_ref(v_a_1415_);
lean_dec_ref(v_m_1414_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_1417_, lean_object* v_ref_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
lean_object* v___x_1422_; 
v___x_1422_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1418_);
return v___x_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1423_, lean_object* v_ref_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_){
_start:
{
lean_object* v_res_1428_; 
v_res_1428_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_1423_, v_ref_1424_, v___y_1425_, v___y_1426_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
return v_res_1428_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8(lean_object* v_00_u03b1_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
lean_object* v___x_1433_; 
v___x_1433_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg();
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_){
_start:
{
lean_object* v_res_1438_; 
v_res_1438_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8(v_00_u03b1_1434_, v___y_1435_, v___y_1436_);
lean_dec(v___y_1436_);
lean_dec_ref(v___y_1435_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_1439_, lean_object* v_x_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_){
_start:
{
lean_object* v___x_1445_; 
v___x_1445_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg(v_x_1440_, v___y_1441_, v___y_1442_, v___y_1443_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_1446_, lean_object* v_x_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5(v_00_u03b1_1446_, v_x_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
lean_dec(v___y_1450_);
lean_dec_ref(v___y_1449_);
lean_dec(v___y_1448_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_1453_, lean_object* v_m_1454_, lean_object* v_a_1455_, lean_object* v_b_1456_){
_start:
{
lean_object* v___x_1457_; 
v___x_1457_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6___redArg(v_m_1454_, v_a_1455_, v_b_1456_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1458_, lean_object* v_a_1459_, lean_object* v_x_1460_){
_start:
{
lean_object* v___x_1461_; 
v___x_1461_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1_spec__2___redArg(v_a_1459_, v_x_1460_);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1462_, lean_object* v_a_1463_, lean_object* v_x_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_1462_, v_a_1463_, v_x_1464_);
lean_dec(v_x_1464_);
lean_dec_ref(v_a_1463_);
return v_res_1465_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_1466_, lean_object* v_a_1467_, lean_object* v_x_1468_){
_start:
{
uint8_t v___x_1469_; 
v___x_1469_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1467_, v_x_1468_);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___boxed(lean_object* v_00_u03b2_1470_, lean_object* v_a_1471_, lean_object* v_x_1472_){
_start:
{
uint8_t v_res_1473_; lean_object* v_r_1474_; 
v_res_1473_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10(v_00_u03b2_1470_, v_a_1471_, v_x_1472_);
lean_dec(v_x_1472_);
lean_dec_ref(v_a_1471_);
v_r_1474_ = lean_box(v_res_1473_);
return v_r_1474_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_1475_, lean_object* v_data_1476_){
_start:
{
lean_object* v___x_1477_; 
v___x_1477_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11___redArg(v_data_1476_);
return v___x_1477_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12(lean_object* v_00_u03b2_1478_, lean_object* v_a_1479_, lean_object* v_b_1480_, lean_object* v_x_1481_){
_start:
{
lean_object* v___x_1482_; 
v___x_1482_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1479_, v_b_1480_, v_x_1481_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12(lean_object* v_00_u03b2_1483_, lean_object* v_i_1484_, lean_object* v_source_1485_, lean_object* v_target_1486_){
_start:
{
lean_object* v___x_1487_; 
v___x_1487_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v_i_1484_, v_source_1485_, v_target_1486_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_1488_, lean_object* v_x_1489_, lean_object* v_x_1490_){
_start:
{
lean_object* v___x_1491_; 
v___x_1491_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_x_1489_, v_x_1490_);
return v___x_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(lean_object* v_declName_1492_, lean_object* v___y_1493_){
_start:
{
lean_object* v___x_1495_; lean_object* v_env_1496_; uint8_t v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1495_ = lean_st_ref_get(v___y_1493_);
v_env_1496_ = lean_ctor_get(v___x_1495_, 0);
lean_inc_ref(v_env_1496_);
lean_dec(v___x_1495_);
v___x_1497_ = l_Lean_isRecCore(v_env_1496_, v_declName_1492_);
v___x_1498_ = lean_box(v___x_1497_);
v___x_1499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1499_, 0, v___x_1498_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg___boxed(lean_object* v_declName_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(v_declName_1500_, v___y_1501_);
lean_dec(v___y_1501_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2(lean_object* v_declName_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
lean_object* v___x_1510_; 
v___x_1510_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(v_declName_1504_, v___y_1508_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___boxed(lean_object* v_declName_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_){
_start:
{
lean_object* v_res_1517_; 
v_res_1517_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2(v_declName_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_);
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
lean_dec(v___y_1513_);
lean_dec_ref(v___y_1512_);
return v_res_1517_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(lean_object* v_declName_1518_, lean_object* v___y_1519_){
_start:
{
lean_object* v___x_1521_; lean_object* v_env_1522_; uint8_t v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; 
v___x_1521_ = lean_st_ref_get(v___y_1519_);
v_env_1522_ = lean_ctor_get(v___x_1521_, 0);
lean_inc_ref(v_env_1522_);
lean_dec(v___x_1521_);
v___x_1523_ = l_Lean_getReducibilityStatusCore(v_env_1522_, v_declName_1518_);
v___x_1524_ = lean_box(v___x_1523_);
v___x_1525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1524_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg___boxed(lean_object* v_declName_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_){
_start:
{
lean_object* v_res_1529_; 
v_res_1529_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(v_declName_1526_, v___y_1527_);
lean_dec(v___y_1527_);
return v_res_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0(lean_object* v_declName_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
lean_object* v___x_1536_; lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1552_; 
v___x_1536_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(v_declName_1530_, v___y_1534_);
v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1552_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1539_ = v___x_1536_;
v_isShared_1540_ = v_isSharedCheck_1552_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v___x_1536_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1552_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
uint8_t v___x_1541_; 
v___x_1541_ = lean_unbox(v_a_1537_);
lean_dec(v_a_1537_);
if (v___x_1541_ == 0)
{
uint8_t v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1545_; 
v___x_1542_ = 1;
v___x_1543_ = lean_box(v___x_1542_);
if (v_isShared_1540_ == 0)
{
lean_ctor_set(v___x_1539_, 0, v___x_1543_);
v___x_1545_ = v___x_1539_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v___x_1543_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
else
{
uint8_t v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1550_; 
v___x_1547_ = 0;
v___x_1548_ = lean_box(v___x_1547_);
if (v_isShared_1540_ == 0)
{
lean_ctor_set(v___x_1539_, 0, v___x_1548_);
v___x_1550_ = v___x_1539_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v___x_1548_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
return v___x_1550_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0___boxed(lean_object* v_declName_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_){
_start:
{
lean_object* v_res_1559_; 
v_res_1559_ = l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0(v_declName_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_);
lean_dec(v___y_1557_);
lean_dec_ref(v___y_1556_);
lean_dec(v___y_1555_);
lean_dec_ref(v___y_1554_);
return v_res_1559_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(lean_object* v_a_1560_, lean_object* v_b_1561_){
_start:
{
lean_object* v_array_1563_; lean_object* v_start_1564_; lean_object* v_stop_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1582_; 
v_array_1563_ = lean_ctor_get(v_a_1560_, 0);
v_start_1564_ = lean_ctor_get(v_a_1560_, 1);
v_stop_1565_ = lean_ctor_get(v_a_1560_, 2);
v_isSharedCheck_1582_ = !lean_is_exclusive(v_a_1560_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1567_ = v_a_1560_;
v_isShared_1568_ = v_isSharedCheck_1582_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_stop_1565_);
lean_inc(v_start_1564_);
lean_inc(v_array_1563_);
lean_dec(v_a_1560_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1582_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
uint8_t v___x_1569_; 
v___x_1569_ = lean_nat_dec_lt(v_start_1564_, v_stop_1565_);
if (v___x_1569_ == 0)
{
lean_object* v___x_1570_; 
lean_del_object(v___x_1567_);
lean_dec(v_stop_1565_);
lean_dec(v_start_1564_);
lean_dec_ref(v_array_1563_);
v___x_1570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1570_, 0, v_b_1561_);
return v___x_1570_;
}
else
{
lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1575_; 
v___x_1571_ = lean_box(0);
v___x_1572_ = lean_unsigned_to_nat(1u);
v___x_1573_ = lean_nat_add(v_start_1564_, v___x_1572_);
lean_inc_ref(v_array_1563_);
if (v_isShared_1568_ == 0)
{
lean_ctor_set(v___x_1567_, 1, v___x_1573_);
v___x_1575_ = v___x_1567_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_array_1563_);
lean_ctor_set(v_reuseFailAlloc_1581_, 1, v___x_1573_);
lean_ctor_set(v_reuseFailAlloc_1581_, 2, v_stop_1565_);
v___x_1575_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
lean_object* v___x_1576_; uint8_t v___x_1577_; 
v___x_1576_ = lean_array_fget(v_array_1563_, v_start_1564_);
lean_dec(v_start_1564_);
lean_dec_ref(v_array_1563_);
v___x_1577_ = l_Lean_Expr_hasExprMVar(v___x_1576_);
lean_dec(v___x_1576_);
if (v___x_1577_ == 0)
{
v_a_1560_ = v___x_1575_;
v_b_1561_ = v___x_1571_;
goto _start;
}
else
{
lean_object* v___x_1579_; 
v___x_1579_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_dec_ref_known(v___x_1579_, 1);
v_a_1560_ = v___x_1575_;
v_b_1561_ = v___x_1571_;
goto _start;
}
else
{
lean_dec_ref(v___x_1575_);
return v___x_1579_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg___boxed(lean_object* v_a_1583_, lean_object* v_b_1584_, lean_object* v___y_1585_){
_start:
{
lean_object* v_res_1586_; 
v_res_1586_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(v_a_1583_, v_b_1584_);
return v_res_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(lean_object* v_e_1595_, uint8_t v_isMatch_1596_, uint8_t v_root_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_){
_start:
{
lean_object* v___y_1604_; lean_object* v_b_1605_; lean_object* v___x_1616_; 
v___x_1616_ = l_Lean_Meta_DiscrTree_reduceDT(v_e_1595_, v_root_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_);
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_object* v_a_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1779_; 
v_a_1617_ = lean_ctor_get(v___x_1616_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1619_ = v___x_1616_;
v_isShared_1620_ = v_isSharedCheck_1779_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_a_1617_);
lean_dec(v___x_1616_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1779_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___y_1622_; lean_object* v___y_1632_; lean_object* v___y_1633_; lean_object* v___y_1634_; lean_object* v___y_1635_; 
if (v_root_1597_ == 0)
{
lean_object* v___x_1767_; 
lean_inc(v_a_1617_);
v___x_1767_ = l_Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f(v_a_1617_);
if (lean_obj_tag(v___x_1767_) == 1)
{
lean_object* v_val_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1778_; 
lean_del_object(v___x_1619_);
lean_dec(v_a_1617_);
v_val_1768_ = lean_ctor_get(v___x_1767_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1770_ = v___x_1767_;
v_isShared_1771_ = v_isSharedCheck_1778_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_val_1768_);
lean_dec(v___x_1767_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1778_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1773_; 
if (v_isShared_1771_ == 0)
{
lean_ctor_set_tag(v___x_1770_, 2);
v___x_1773_ = v___x_1770_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_val_1768_);
v___x_1773_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1774_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
v___x_1775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1773_);
lean_ctor_set(v___x_1775_, 1, v___x_1774_);
v___x_1776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1775_);
return v___x_1776_;
}
}
}
else
{
lean_dec(v___x_1767_);
v___y_1632_ = v_a_1598_;
v___y_1633_ = v_a_1599_;
v___y_1634_ = v_a_1600_;
v___y_1635_ = v_a_1601_;
goto v___jp_1631_;
}
}
else
{
v___y_1632_ = v_a_1598_;
v___y_1633_ = v_a_1599_;
v___y_1634_ = v_a_1600_;
v___y_1635_ = v_a_1601_;
goto v___jp_1631_;
}
v___jp_1621_:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1629_; 
v___x_1623_ = l_Lean_Expr_getAppNumArgs(v_a_1617_);
lean_inc(v___x_1623_);
v___x_1624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1624_, 0, v___y_1622_);
lean_ctor_set(v___x_1624_, 1, v___x_1623_);
v___x_1625_ = lean_mk_empty_array_with_capacity(v___x_1623_);
lean_dec(v___x_1623_);
v___x_1626_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1617_, v___x_1625_);
v___x_1627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1624_);
lean_ctor_set(v___x_1627_, 1, v___x_1626_);
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 0, v___x_1627_);
v___x_1629_ = v___x_1619_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v___x_1627_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
v___jp_1631_:
{
lean_object* v___x_1636_; 
v___x_1636_ = l_Lean_Expr_getAppFn(v_a_1617_);
switch(lean_obj_tag(v___x_1636_))
{
case 1:
{
lean_object* v_fvarId_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
lean_del_object(v___x_1619_);
v_fvarId_1637_ = lean_ctor_get(v___x_1636_, 0);
lean_inc(v_fvarId_1637_);
lean_dec_ref_known(v___x_1636_, 1);
v___x_1638_ = l_Lean_Expr_getAppNumArgs(v_a_1617_);
lean_inc(v___x_1638_);
v___x_1639_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1639_, 0, v_fvarId_1637_);
lean_ctor_set(v___x_1639_, 1, v___x_1638_);
v___x_1640_ = lean_mk_empty_array_with_capacity(v___x_1638_);
lean_dec(v___x_1638_);
v___x_1641_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1617_, v___x_1640_);
v___x_1642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1639_);
lean_ctor_set(v___x_1642_, 1, v___x_1641_);
v___x_1643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1642_);
return v___x_1643_;
}
case 2:
{
lean_del_object(v___x_1619_);
lean_dec(v_a_1617_);
if (v_isMatch_1596_ == 0)
{
lean_object* v_mvarId_1644_; lean_object* v___x_1645_; uint8_t v_isDefEqStuckEx_1646_; 
v_mvarId_1644_ = lean_ctor_get(v___x_1636_, 0);
lean_inc(v_mvarId_1644_);
lean_dec_ref_known(v___x_1636_, 1);
v___x_1645_ = l_Lean_Meta_Context_config(v___y_1632_);
v_isDefEqStuckEx_1646_ = lean_ctor_get_uint8(v___x_1645_, 4);
lean_dec_ref(v___x_1645_);
if (v_isDefEqStuckEx_1646_ == 0)
{
lean_object* v___x_1647_; 
v___x_1647_ = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(v_mvarId_1644_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_object* v_a_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1661_; 
v_a_1648_ = lean_ctor_get(v___x_1647_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1650_ = v___x_1647_;
v_isShared_1651_ = v_isSharedCheck_1661_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_a_1648_);
lean_dec(v___x_1647_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1661_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
uint8_t v___x_1652_; 
v___x_1652_ = lean_unbox(v_a_1648_);
lean_dec(v_a_1648_);
if (v___x_1652_ == 0)
{
lean_object* v___x_1653_; lean_object* v___x_1655_; 
v___x_1653_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__2));
if (v_isShared_1651_ == 0)
{
lean_ctor_set(v___x_1650_, 0, v___x_1653_);
v___x_1655_ = v___x_1650_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v___x_1653_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
else
{
lean_object* v___x_1657_; lean_object* v___x_1659_; 
v___x_1657_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
if (v_isShared_1651_ == 0)
{
lean_ctor_set(v___x_1650_, 0, v___x_1657_);
v___x_1659_ = v___x_1650_;
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
}
}
else
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1669_; 
v_a_1662_ = lean_ctor_get(v___x_1647_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1664_ = v___x_1647_;
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1647_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1667_; 
if (v_isShared_1665_ == 0)
{
v___x_1667_ = v___x_1664_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_a_1662_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
}
else
{
lean_object* v___x_1670_; lean_object* v___x_1671_; 
lean_dec(v_mvarId_1644_);
v___x_1670_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__2));
v___x_1671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1670_);
return v___x_1671_;
}
}
else
{
lean_object* v___x_1672_; lean_object* v___x_1673_; 
lean_dec_ref_known(v___x_1636_, 1);
v___x_1672_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
v___x_1673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1672_);
return v___x_1673_;
}
}
case 4:
{
lean_object* v_declName_1674_; lean_object* v___x_1675_; uint8_t v_isDefEqStuckEx_1676_; 
v_declName_1674_ = lean_ctor_get(v___x_1636_, 0);
lean_inc(v_declName_1674_);
lean_dec_ref_known(v___x_1636_, 2);
v___x_1675_ = l_Lean_Meta_Context_config(v___y_1632_);
v_isDefEqStuckEx_1676_ = lean_ctor_get_uint8(v___x_1675_, 4);
lean_dec_ref(v___x_1675_);
if (v_isDefEqStuckEx_1676_ == 0)
{
v___y_1622_ = v_declName_1674_;
goto v___jp_1621_;
}
else
{
uint8_t v___x_1677_; 
v___x_1677_ = l_Lean_Expr_hasExprMVar(v_a_1617_);
if (v___x_1677_ == 0)
{
v___y_1622_ = v_declName_1674_;
goto v___jp_1621_;
}
else
{
lean_object* v___x_1678_; 
lean_inc(v_declName_1674_);
v___x_1678_ = l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0(v_declName_1674_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_);
if (lean_obj_tag(v___x_1678_) == 0)
{
lean_object* v_a_1679_; uint8_t v___x_1680_; 
v_a_1679_ = lean_ctor_get(v___x_1678_, 0);
lean_inc(v_a_1679_);
lean_dec_ref_known(v___x_1678_, 1);
v___x_1680_ = lean_unbox(v_a_1679_);
lean_dec(v_a_1679_);
if (v___x_1680_ == 0)
{
lean_object* v___x_1681_; lean_object* v_env_1682_; lean_object* v___x_1683_; 
v___x_1681_ = lean_st_ref_get(v___y_1635_);
v_env_1682_ = lean_ctor_get(v___x_1681_, 0);
lean_inc_ref(v_env_1682_);
lean_dec(v___x_1681_);
v___x_1683_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_1682_, v_a_1617_);
if (lean_obj_tag(v___x_1683_) == 1)
{
lean_object* v_val_1684_; lean_object* v_numDiscrs_1685_; lean_object* v_nargs_1686_; lean_object* v_dummy_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
v_val_1684_ = lean_ctor_get(v___x_1683_, 0);
lean_inc(v_val_1684_);
lean_dec_ref_known(v___x_1683_, 1);
v_numDiscrs_1685_ = lean_ctor_get(v_val_1684_, 1);
lean_inc(v_numDiscrs_1685_);
v_nargs_1686_ = l_Lean_Expr_getAppNumArgs(v_a_1617_);
v_dummy_1687_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0);
lean_inc(v_nargs_1686_);
v___x_1688_ = lean_mk_array(v_nargs_1686_, v_dummy_1687_);
v___x_1689_ = lean_unsigned_to_nat(1u);
v___x_1690_ = lean_nat_sub(v_nargs_1686_, v___x_1689_);
lean_dec(v_nargs_1686_);
lean_inc(v_a_1617_);
v___x_1691_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1617_, v___x_1688_, v___x_1690_);
v___x_1692_ = l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(v_val_1684_);
lean_dec(v_val_1684_);
v___x_1693_ = lean_nat_add(v___x_1692_, v_numDiscrs_1685_);
lean_dec(v_numDiscrs_1685_);
v___x_1694_ = l_Array_toSubarray___redArg(v___x_1691_, v___x_1692_, v___x_1693_);
v___x_1695_ = lean_box(0);
v___x_1696_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(v___x_1694_, v___x_1695_);
if (lean_obj_tag(v___x_1696_) == 0)
{
lean_dec_ref_known(v___x_1696_, 1);
v___y_1622_ = v_declName_1674_;
goto v___jp_1621_;
}
else
{
lean_object* v_a_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1704_; 
lean_dec(v_declName_1674_);
lean_del_object(v___x_1619_);
lean_dec(v_a_1617_);
v_a_1697_ = lean_ctor_get(v___x_1696_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1696_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1699_ = v___x_1696_;
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_a_1697_);
lean_dec(v___x_1696_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1702_; 
if (v_isShared_1700_ == 0)
{
v___x_1702_ = v___x_1699_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_a_1697_);
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
lean_object* v___x_1705_; lean_object* v_a_1706_; uint8_t v___x_1707_; 
lean_dec(v___x_1683_);
lean_inc(v_declName_1674_);
v___x_1705_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(v_declName_1674_, v___y_1635_);
v_a_1706_ = lean_ctor_get(v___x_1705_, 0);
lean_inc(v_a_1706_);
lean_dec_ref(v___x_1705_);
v___x_1707_ = lean_unbox(v_a_1706_);
lean_dec(v_a_1706_);
if (v___x_1707_ == 0)
{
v___y_1622_ = v_declName_1674_;
goto v___jp_1621_;
}
else
{
lean_object* v___x_1708_; 
v___x_1708_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1708_) == 0)
{
lean_dec_ref_known(v___x_1708_, 1);
v___y_1622_ = v_declName_1674_;
goto v___jp_1621_;
}
else
{
lean_object* v_a_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1716_; 
lean_dec(v_declName_1674_);
lean_del_object(v___x_1619_);
lean_dec(v_a_1617_);
v_a_1709_ = lean_ctor_get(v___x_1708_, 0);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1711_ = v___x_1708_;
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_a_1709_);
lean_dec(v___x_1708_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1714_; 
if (v_isShared_1712_ == 0)
{
v___x_1714_ = v___x_1711_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v_a_1709_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
return v___x_1714_;
}
}
}
}
}
}
else
{
lean_object* v___x_1717_; 
v___x_1717_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1717_) == 0)
{
lean_dec_ref_known(v___x_1717_, 1);
v___y_1622_ = v_declName_1674_;
goto v___jp_1621_;
}
else
{
lean_object* v_a_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1725_; 
lean_dec(v_declName_1674_);
lean_del_object(v___x_1619_);
lean_dec(v_a_1617_);
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
}
else
{
lean_object* v_a_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1733_; 
lean_dec(v_declName_1674_);
lean_del_object(v___x_1619_);
lean_dec(v_a_1617_);
v_a_1726_ = lean_ctor_get(v___x_1678_, 0);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1728_ = v___x_1678_;
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_a_1726_);
lean_dec(v___x_1678_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1731_; 
if (v_isShared_1729_ == 0)
{
v___x_1731_ = v___x_1728_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_a_1726_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
}
}
}
case 7:
{
lean_object* v_binderType_1734_; lean_object* v_body_1735_; uint8_t v___x_1736_; 
lean_del_object(v___x_1619_);
lean_dec(v_a_1617_);
v_binderType_1734_ = lean_ctor_get(v___x_1636_, 1);
lean_inc_ref(v_binderType_1734_);
v_body_1735_ = lean_ctor_get(v___x_1636_, 2);
lean_inc_ref(v_body_1735_);
lean_dec_ref_known(v___x_1636_, 3);
v___x_1736_ = l_Lean_Expr_hasLooseBVars(v_body_1735_);
if (v___x_1736_ == 0)
{
v___y_1604_ = v_binderType_1734_;
v_b_1605_ = v_body_1735_;
goto v___jp_1603_;
}
else
{
lean_object* v___x_1737_; 
v___x_1737_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(v_body_1735_, v___y_1634_, v___y_1635_);
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_object* v_a_1738_; 
v_a_1738_ = lean_ctor_get(v___x_1737_, 0);
lean_inc(v_a_1738_);
lean_dec_ref_known(v___x_1737_, 1);
v___y_1604_ = v_binderType_1734_;
v_b_1605_ = v_a_1738_;
goto v___jp_1603_;
}
else
{
lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1746_; 
lean_dec_ref(v_binderType_1734_);
v_a_1739_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1741_ = v___x_1737_;
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_dec(v___x_1737_);
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
case 9:
{
lean_object* v_a_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
lean_del_object(v___x_1619_);
lean_dec(v_a_1617_);
v_a_1747_ = lean_ctor_get(v___x_1636_, 0);
lean_inc_ref(v_a_1747_);
lean_dec_ref_known(v___x_1636_, 1);
v___x_1748_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1748_, 0, v_a_1747_);
v___x_1749_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
v___x_1750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1750_, 0, v___x_1748_);
lean_ctor_set(v___x_1750_, 1, v___x_1749_);
v___x_1751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1750_);
return v___x_1751_;
}
case 11:
{
lean_object* v_typeName_1752_; lean_object* v_idx_1753_; lean_object* v_struct_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; 
lean_del_object(v___x_1619_);
v_typeName_1752_ = lean_ctor_get(v___x_1636_, 0);
lean_inc(v_typeName_1752_);
v_idx_1753_ = lean_ctor_get(v___x_1636_, 1);
lean_inc(v_idx_1753_);
v_struct_1754_ = lean_ctor_get(v___x_1636_, 2);
lean_inc_ref(v_struct_1754_);
lean_dec_ref_known(v___x_1636_, 3);
v___x_1755_ = l_Lean_Expr_getAppNumArgs(v_a_1617_);
lean_inc(v___x_1755_);
v___x_1756_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_1756_, 0, v_typeName_1752_);
lean_ctor_set(v___x_1756_, 1, v_idx_1753_);
lean_ctor_set(v___x_1756_, 2, v___x_1755_);
v___x_1757_ = lean_unsigned_to_nat(1u);
v___x_1758_ = lean_mk_empty_array_with_capacity(v___x_1757_);
v___x_1759_ = lean_array_push(v___x_1758_, v_struct_1754_);
v___x_1760_ = lean_mk_empty_array_with_capacity(v___x_1755_);
lean_dec(v___x_1755_);
v___x_1761_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1617_, v___x_1760_);
v___x_1762_ = l_Array_append___redArg(v___x_1759_, v___x_1761_);
lean_dec_ref(v___x_1761_);
v___x_1763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1756_);
lean_ctor_set(v___x_1763_, 1, v___x_1762_);
v___x_1764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1764_, 0, v___x_1763_);
return v___x_1764_;
}
default: 
{
lean_object* v___x_1765_; lean_object* v___x_1766_; 
lean_dec_ref(v___x_1636_);
lean_del_object(v___x_1619_);
lean_dec(v_a_1617_);
v___x_1765_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
v___x_1766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1766_, 0, v___x_1765_);
return v___x_1766_;
}
}
}
}
}
else
{
lean_object* v_a_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1787_; 
v_a_1780_ = lean_ctor_get(v___x_1616_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1782_ = v___x_1616_;
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_a_1780_);
lean_dec(v___x_1616_);
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
v___jp_1603_:
{
uint8_t v___x_1606_; 
v___x_1606_ = l_Lean_Expr_hasLooseBVars(v_b_1605_);
if (v___x_1606_ == 0)
{
lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1607_ = lean_box(5);
v___x_1608_ = lean_unsigned_to_nat(2u);
v___x_1609_ = lean_mk_empty_array_with_capacity(v___x_1608_);
v___x_1610_ = lean_array_push(v___x_1609_, v___y_1604_);
v___x_1611_ = lean_array_push(v___x_1610_, v_b_1605_);
v___x_1612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1607_);
lean_ctor_set(v___x_1612_, 1, v___x_1611_);
v___x_1613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1612_);
return v___x_1613_;
}
else
{
lean_object* v___x_1614_; lean_object* v___x_1615_; 
lean_dec_ref(v_b_1605_);
lean_dec_ref(v___y_1604_);
v___x_1614_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
v___x_1615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1614_);
return v___x_1615_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___boxed(lean_object* v_e_1788_, lean_object* v_isMatch_1789_, lean_object* v_root_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_){
_start:
{
uint8_t v_isMatch_boxed_1796_; uint8_t v_root_boxed_1797_; lean_object* v_res_1798_; 
v_isMatch_boxed_1796_ = lean_unbox(v_isMatch_1789_);
v_root_boxed_1797_ = lean_unbox(v_root_1790_);
v_res_1798_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_1788_, v_isMatch_boxed_1796_, v_root_boxed_1797_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_);
lean_dec(v_a_1794_);
lean_dec_ref(v_a_1793_);
lean_dec(v_a_1792_);
lean_dec_ref(v_a_1791_);
return v_res_1798_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0(lean_object* v_declName_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_){
_start:
{
lean_object* v___x_1805_; 
v___x_1805_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(v_declName_1799_, v___y_1803_);
return v___x_1805_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___boxed(lean_object* v_declName_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0(v_declName_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec(v___y_1808_);
lean_dec_ref(v___y_1807_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1(lean_object* v_inst_1813_, lean_object* v_R_1814_, lean_object* v_a_1815_, lean_object* v_b_1816_, lean_object* v_c_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
lean_object* v___x_1823_; 
v___x_1823_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(v_a_1815_, v_b_1816_);
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___boxed(lean_object* v_inst_1824_, lean_object* v_R_1825_, lean_object* v_a_1826_, lean_object* v_b_1827_, lean_object* v_c_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_){
_start:
{
lean_object* v_res_1834_; 
v_res_1834_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1(v_inst_1824_, v_R_1825_, v_a_1826_, v_b_1827_, v_c_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
return v_res_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getMatchKeyArgs(lean_object* v_e_1835_, uint8_t v_root_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_){
_start:
{
uint8_t v___x_1842_; lean_object* v___x_1843_; 
v___x_1842_ = 1;
v___x_1843_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_1835_, v___x_1842_, v_root_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getMatchKeyArgs___boxed(lean_object* v_e_1844_, lean_object* v_root_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_){
_start:
{
uint8_t v_root_boxed_1851_; lean_object* v_res_1852_; 
v_root_boxed_1851_ = lean_unbox(v_root_1845_);
v_res_1852_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getMatchKeyArgs(v_e_1844_, v_root_boxed_1851_, v_a_1846_, v_a_1847_, v_a_1848_, v_a_1849_);
lean_dec(v_a_1849_);
lean_dec_ref(v_a_1848_);
lean_dec(v_a_1847_);
lean_dec_ref(v_a_1846_);
return v_res_1852_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__1(void){
_start:
{
lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1855_ = lean_box(0);
v___x_1856_ = lean_unsigned_to_nat(16u);
v___x_1857_ = lean_mk_array(v___x_1856_, v___x_1855_);
return v___x_1857_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2(void){
_start:
{
lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; 
v___x_1858_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__1);
v___x_1859_ = lean_unsigned_to_nat(0u);
v___x_1860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1859_);
lean_ctor_set(v___x_1860_, 1, v___x_1858_);
return v___x_1860_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__4(void){
_start:
{
lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; 
v___x_1863_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__3));
v___x_1864_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2);
v___x_1865_ = lean_unsigned_to_nat(0u);
v___x_1866_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__0));
v___x_1867_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1867_, 0, v___x_1866_);
lean_ctor_set(v___x_1867_, 1, v___x_1865_);
lean_ctor_set(v___x_1867_, 2, v___x_1864_);
lean_ctor_set(v___x_1867_, 3, v___x_1863_);
return v___x_1867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg(){
_start:
{
lean_object* v___x_1869_; 
v___x_1869_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__4);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___boxed(lean_object* v___dummy_1870_){
_start:
{
lean_object* v_res_1871_; 
v_res_1871_ = l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg();
return v_res_1871_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0(void){
_start:
{
lean_object* v___x_1872_; 
v___x_1872_ = l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg();
return v___x_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default(lean_object* v_00_u03b1_1873_){
_start:
{
lean_object* v___x_1874_; 
v___x_1874_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0);
return v___x_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___redArg(){
_start:
{
lean_object* v___x_1876_; 
v___x_1876_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___redArg___boxed(lean_object* v___dummy_1877_){
_start:
{
lean_object* v_res_1878_; 
v_res_1878_ = l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___redArg();
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie(lean_object* v_a_1879_){
_start:
{
lean_object* v___x_1880_; 
v___x_1880_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0);
return v___x_1880_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__1(void){
_start:
{
lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1883_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2);
v___x_1884_ = lean_unsigned_to_nat(0u);
v___x_1885_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___x_1886_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1885_);
lean_ctor_set(v___x_1886_, 1, v___x_1884_);
lean_ctor_set(v___x_1886_, 2, v___x_1883_);
lean_ctor_set(v___x_1886_, 3, v___x_1885_);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg(){
_start:
{
lean_object* v___x_1888_; 
v___x_1888_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__1);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___boxed(lean_object* v___dummy_1889_){
_start:
{
lean_object* v_res_1890_; 
v_res_1890_ = l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg();
return v_res_1890_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0(void){
_start:
{
lean_object* v___x_1891_; 
v___x_1891_ = l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg();
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie(lean_object* v_00_u03b1_1892_){
_start:
{
lean_object* v___x_1893_; 
v___x_1893_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0, &l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Trie_pushPending___redArg(lean_object* v_x_1894_, lean_object* v_x_1895_){
_start:
{
lean_object* v_values_1896_; lean_object* v_star_1897_; lean_object* v_children_1898_; lean_object* v_pending_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1907_; 
v_values_1896_ = lean_ctor_get(v_x_1894_, 0);
v_star_1897_ = lean_ctor_get(v_x_1894_, 1);
v_children_1898_ = lean_ctor_get(v_x_1894_, 2);
v_pending_1899_ = lean_ctor_get(v_x_1894_, 3);
v_isSharedCheck_1907_ = !lean_is_exclusive(v_x_1894_);
if (v_isSharedCheck_1907_ == 0)
{
v___x_1901_ = v_x_1894_;
v_isShared_1902_ = v_isSharedCheck_1907_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_pending_1899_);
lean_inc(v_children_1898_);
lean_inc(v_star_1897_);
lean_inc(v_values_1896_);
lean_dec(v_x_1894_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1907_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1903_; lean_object* v___x_1905_; 
v___x_1903_ = lean_array_push(v_pending_1899_, v_x_1895_);
if (v_isShared_1902_ == 0)
{
lean_ctor_set(v___x_1901_, 3, v___x_1903_);
v___x_1905_ = v___x_1901_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v_values_1896_);
lean_ctor_set(v_reuseFailAlloc_1906_, 1, v_star_1897_);
lean_ctor_set(v_reuseFailAlloc_1906_, 2, v_children_1898_);
lean_ctor_set(v_reuseFailAlloc_1906_, 3, v___x_1903_);
v___x_1905_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
return v___x_1905_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Trie_pushPending(lean_object* v_00_u03b1_1908_, lean_object* v_x_1909_, lean_object* v_x_1910_){
_start:
{
lean_object* v___x_1911_; 
v___x_1911_ = l_Lean_Meta_LazyDiscrTree_Trie_pushPending___redArg(v_x_1909_, v_x_1910_);
return v___x_1911_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__0(void){
_start:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1912_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0);
v___x_1913_ = lean_unsigned_to_nat(1u);
v___x_1914_ = lean_mk_empty_array_with_capacity(v___x_1913_);
v___x_1915_ = lean_array_push(v___x_1914_, v___x_1912_);
return v___x_1915_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__1(void){
_start:
{
lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; 
v___x_1916_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2);
v___x_1917_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__0);
v___x_1918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1917_);
lean_ctor_set(v___x_1918_, 1, v___x_1916_);
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabited___redArg(){
_start:
{
lean_object* v___x_1920_; 
v___x_1920_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__1);
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___boxed(lean_object* v___dummy_1921_){
_start:
{
lean_object* v_res_1922_; 
v_res_1922_ = l_Lean_Meta_LazyDiscrTree_instInhabited___redArg();
return v_res_1922_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_1923_; 
v___x_1923_ = l_Lean_Meta_LazyDiscrTree_instInhabited___redArg();
return v___x_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabited(lean_object* v_00_u03b1_1924_){
_start:
{
lean_object* v___x_1925_; 
v___x_1925_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0);
return v___x_1925_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(lean_object* v_msgData_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_){
_start:
{
lean_object* v___x_1932_; lean_object* v_env_1933_; uint8_t v___x_1934_; lean_object* v_env_1935_; lean_object* v___x_1936_; lean_object* v_toCold_1937_; lean_object* v_mctx_1938_; lean_object* v_lctx_1939_; lean_object* v_options_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; 
v___x_1932_ = lean_st_ref_get(v___y_1930_);
v_env_1933_ = lean_ctor_get(v___x_1932_, 0);
lean_inc_ref(v_env_1933_);
lean_dec(v___x_1932_);
v___x_1934_ = 0;
v_env_1935_ = l_Lean_Environment_setRecordingDeps(v_env_1933_, v___x_1934_);
v___x_1936_ = lean_st_ref_get(v___y_1928_);
v_toCold_1937_ = lean_ctor_get(v___y_1929_, 0);
v_mctx_1938_ = lean_ctor_get(v___x_1936_, 0);
lean_inc_ref(v_mctx_1938_);
lean_dec(v___x_1936_);
v_lctx_1939_ = lean_ctor_get(v___y_1927_, 2);
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
lean_ctor_set(v___x_1942_, 1, v_msgData_1926_);
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
if (v_root_1978_ == 0)
{
lean_object* v___x_2053_; 
lean_inc(v_a_1993_);
v___x_2053_ = l_Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f(v_a_1993_);
if (lean_obj_tag(v___x_2053_) == 1)
{
lean_object* v_val_2054_; 
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
lean_inc(v_declName_2045_);
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
v_idx_2076_ = lean_ctor_get(v___x_1997_, 1);
v_struct_2077_ = lean_ctor_get(v___x_1997_, 2);
v___x_2078_ = lean_st_ref_get(v_a_1984_);
v_env_2084_ = lean_ctor_get(v___x_2078_, 0);
lean_inc_ref(v_env_2084_);
lean_dec(v___x_2078_);
v___x_2085_ = l_Lean_isClass(v_env_2084_, v_typeName_2075_);
if (v___x_2085_ == 0)
{
lean_inc_ref(v_struct_2077_);
v___y_2080_ = v_struct_2077_;
goto v___jp_2079_;
}
else
{
lean_object* v___x_2086_; 
lean_inc_ref(v_struct_2077_);
v___x_2086_ = l_Lean_Meta_DiscrTree_mkNoindexAnnotation(v_struct_2077_);
v___y_2080_ = v___x_2086_;
goto v___jp_2079_;
}
v___jp_2079_:
{
lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2081_ = l_Lean_Expr_getAppNumArgs(v_a_1993_);
lean_inc(v___x_2081_);
lean_inc(v_idx_2076_);
lean_inc(v_typeName_2075_);
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
uint8_t v___x_3423__boxed_2668_; lean_object* v_res_2669_; 
v___x_3423__boxed_2668_ = lean_unbox(v___x_2659_);
v_res_2669_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0(v___x_3423__boxed_2668_, v_todo_2660_, v_e_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_);
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
size_t v___x_3089_; size_t v___x_3090_; lean_object* v___x_3091_; 
v___x_3089_ = ((size_t)0ULL);
v___x_3090_ = lean_usize_of_nat(v___x_3086_);
v___x_3091_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_entries_3076_, v___x_3089_, v___x_3090_, v___x_3084_, v_a_3077_, v_a_3078_, v_a_3079_, v_a_3080_, v_a_3081_);
return v___x_3091_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg___boxed(lean_object* v_values_3092_, lean_object* v_starIdx_3093_, lean_object* v_children_3094_, lean_object* v_entries_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_){
_start:
{
lean_object* v_res_3102_; 
v_res_3102_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(v_values_3092_, v_starIdx_3093_, v_children_3094_, v_entries_3095_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_);
lean_dec(v_a_3100_);
lean_dec_ref(v_a_3099_);
lean_dec(v_a_3098_);
lean_dec_ref(v_a_3097_);
lean_dec(v_a_3096_);
lean_dec_ref(v_entries_3095_);
return v_res_3102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries(lean_object* v_00_u03b1_3103_, lean_object* v_values_3104_, lean_object* v_starIdx_3105_, lean_object* v_children_3106_, lean_object* v_entries_3107_, lean_object* v_a_3108_, lean_object* v_a_3109_, lean_object* v_a_3110_, lean_object* v_a_3111_, lean_object* v_a_3112_){
_start:
{
lean_object* v___x_3114_; 
v___x_3114_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(v_values_3104_, v_starIdx_3105_, v_children_3106_, v_entries_3107_, v_a_3108_, v_a_3109_, v_a_3110_, v_a_3111_, v_a_3112_);
return v___x_3114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries___boxed(lean_object* v_00_u03b1_3115_, lean_object* v_values_3116_, lean_object* v_starIdx_3117_, lean_object* v_children_3118_, lean_object* v_entries_3119_, lean_object* v_a_3120_, lean_object* v_a_3121_, lean_object* v_a_3122_, lean_object* v_a_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_){
_start:
{
lean_object* v_res_3126_; 
v_res_3126_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries(v_00_u03b1_3115_, v_values_3116_, v_starIdx_3117_, v_children_3118_, v_entries_3119_, v_a_3120_, v_a_3121_, v_a_3122_, v_a_3123_, v_a_3124_);
lean_dec(v_a_3124_);
lean_dec_ref(v_a_3123_);
lean_dec(v_a_3122_);
lean_dec_ref(v_a_3121_);
lean_dec(v_a_3120_);
lean_dec_ref(v_entries_3119_);
return v_res_3126_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0(lean_object* v_00_u03b1_3127_, lean_object* v_as_3128_, size_t v_i_3129_, size_t v_stop_3130_, lean_object* v_b_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_){
_start:
{
lean_object* v___x_3138_; 
v___x_3138_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_as_3128_, v_i_3129_, v_stop_3130_, v_b_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_);
return v___x_3138_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___boxed(lean_object* v_00_u03b1_3139_, lean_object* v_as_3140_, lean_object* v_i_3141_, lean_object* v_stop_3142_, lean_object* v_b_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_){
_start:
{
size_t v_i_boxed_3150_; size_t v_stop_boxed_3151_; lean_object* v_res_3152_; 
v_i_boxed_3150_ = lean_unbox_usize(v_i_3141_);
lean_dec(v_i_3141_);
v_stop_boxed_3151_ = lean_unbox_usize(v_stop_3142_);
lean_dec(v_stop_3142_);
v_res_3152_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0(v_00_u03b1_3139_, v_as_3140_, v_i_boxed_3150_, v_stop_boxed_3151_, v_b_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
lean_dec(v___y_3148_);
lean_dec_ref(v___y_3147_);
lean_dec(v___y_3146_);
lean_dec_ref(v___y_3145_);
lean_dec(v___y_3144_);
lean_dec_ref(v_as_3140_);
return v_res_3152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode___redArg(lean_object* v_c_3153_, lean_object* v_a_3154_, lean_object* v_a_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_){
_start:
{
lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v_values_3163_; lean_object* v_star_3164_; lean_object* v_children_3165_; lean_object* v_pending_3166_; lean_object* v___x_3168_; uint8_t v_isShared_3169_; uint8_t v_isSharedCheck_3196_; 
v___x_3160_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0);
v___x_3161_ = lean_st_ref_get(v_a_3154_);
v___x_3162_ = lean_array_get(v___x_3160_, v___x_3161_, v_c_3153_);
lean_dec(v___x_3161_);
v_values_3163_ = lean_ctor_get(v___x_3162_, 0);
v_star_3164_ = lean_ctor_get(v___x_3162_, 1);
v_children_3165_ = lean_ctor_get(v___x_3162_, 2);
v_pending_3166_ = lean_ctor_get(v___x_3162_, 3);
v_isSharedCheck_3196_ = !lean_is_exclusive(v___x_3162_);
if (v_isSharedCheck_3196_ == 0)
{
v___x_3168_ = v___x_3162_;
v_isShared_3169_ = v_isSharedCheck_3196_;
goto v_resetjp_3167_;
}
else
{
lean_inc(v_pending_3166_);
lean_inc(v_children_3165_);
lean_inc(v_star_3164_);
lean_inc(v_values_3163_);
lean_dec(v___x_3162_);
v___x_3168_ = lean_box(0);
v_isShared_3169_ = v_isSharedCheck_3196_;
goto v_resetjp_3167_;
}
v_resetjp_3167_:
{
lean_object* v___x_3170_; lean_object* v___x_3171_; uint8_t v___x_3172_; 
v___x_3170_ = lean_array_get_size(v_pending_3166_);
v___x_3171_ = lean_unsigned_to_nat(0u);
v___x_3172_ = lean_nat_dec_eq(v___x_3170_, v___x_3171_);
if (v___x_3172_ == 0)
{
lean_object* v___x_3173_; lean_object* v___x_3174_; 
v___x_3173_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_c_3153_, v___x_3160_, v_a_3154_);
lean_dec_ref(v___x_3173_);
v___x_3174_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(v_values_3163_, v_star_3164_, v_children_3165_, v_pending_3166_, v_a_3154_, v_a_3155_, v_a_3156_, v_a_3157_, v_a_3158_);
lean_dec_ref(v_pending_3166_);
if (lean_obj_tag(v___x_3174_) == 0)
{
lean_object* v_a_3175_; lean_object* v_snd_3176_; lean_object* v_fst_3177_; lean_object* v_fst_3178_; lean_object* v_snd_3179_; lean_object* v___x_3180_; lean_object* v___x_3182_; 
v_a_3175_ = lean_ctor_get(v___x_3174_, 0);
lean_inc(v_a_3175_);
lean_dec_ref_known(v___x_3174_, 1);
v_snd_3176_ = lean_ctor_get(v_a_3175_, 1);
v_fst_3177_ = lean_ctor_get(v_a_3175_, 0);
v_fst_3178_ = lean_ctor_get(v_snd_3176_, 0);
v_snd_3179_ = lean_ctor_get(v_snd_3176_, 1);
v___x_3180_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__3));
lean_inc(v_snd_3179_);
lean_inc(v_fst_3178_);
lean_inc(v_fst_3177_);
if (v_isShared_3169_ == 0)
{
lean_ctor_set(v___x_3168_, 3, v___x_3180_);
lean_ctor_set(v___x_3168_, 2, v_snd_3179_);
lean_ctor_set(v___x_3168_, 1, v_fst_3178_);
lean_ctor_set(v___x_3168_, 0, v_fst_3177_);
v___x_3182_ = v___x_3168_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v_fst_3177_);
lean_ctor_set(v_reuseFailAlloc_3192_, 1, v_fst_3178_);
lean_ctor_set(v_reuseFailAlloc_3192_, 2, v_snd_3179_);
lean_ctor_set(v_reuseFailAlloc_3192_, 3, v___x_3180_);
v___x_3182_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
lean_object* v___x_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3190_; 
v___x_3183_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_c_3153_, v___x_3182_, v_a_3154_);
v_isSharedCheck_3190_ = !lean_is_exclusive(v___x_3183_);
if (v_isSharedCheck_3190_ == 0)
{
lean_object* v_unused_3191_; 
v_unused_3191_ = lean_ctor_get(v___x_3183_, 0);
lean_dec(v_unused_3191_);
v___x_3185_ = v___x_3183_;
v_isShared_3186_ = v_isSharedCheck_3190_;
goto v_resetjp_3184_;
}
else
{
lean_dec(v___x_3183_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3190_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
lean_object* v___x_3188_; 
if (v_isShared_3186_ == 0)
{
lean_ctor_set(v___x_3185_, 0, v_a_3175_);
v___x_3188_ = v___x_3185_;
goto v_reusejp_3187_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v_a_3175_);
v___x_3188_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3187_;
}
v_reusejp_3187_:
{
return v___x_3188_;
}
}
}
}
else
{
lean_del_object(v___x_3168_);
return v___x_3174_;
}
}
else
{
lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; 
lean_del_object(v___x_3168_);
lean_dec_ref(v_pending_3166_);
v___x_3193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3193_, 0, v_star_3164_);
lean_ctor_set(v___x_3193_, 1, v_children_3165_);
v___x_3194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3194_, 0, v_values_3163_);
lean_ctor_set(v___x_3194_, 1, v___x_3193_);
v___x_3195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3195_, 0, v___x_3194_);
return v___x_3195_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode___redArg___boxed(lean_object* v_c_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_, lean_object* v_a_3200_, lean_object* v_a_3201_, lean_object* v_a_3202_, lean_object* v_a_3203_){
_start:
{
lean_object* v_res_3204_; 
v_res_3204_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_c_3197_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_, v_a_3202_);
lean_dec(v_a_3202_);
lean_dec_ref(v_a_3201_);
lean_dec(v_a_3200_);
lean_dec_ref(v_a_3199_);
lean_dec(v_a_3198_);
lean_dec(v_c_3197_);
return v_res_3204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode(lean_object* v_00_u03b1_3205_, lean_object* v_c_3206_, lean_object* v_a_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_){
_start:
{
lean_object* v___x_3213_; 
v___x_3213_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_c_3206_, v_a_3207_, v_a_3208_, v_a_3209_, v_a_3210_, v_a_3211_);
return v___x_3213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode___boxed(lean_object* v_00_u03b1_3214_, lean_object* v_c_3215_, lean_object* v_a_3216_, lean_object* v_a_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_){
_start:
{
lean_object* v_res_3222_; 
v_res_3222_ = l_Lean_Meta_LazyDiscrTree_evalNode(v_00_u03b1_3214_, v_c_3215_, v_a_3216_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_);
lean_dec(v_a_3220_);
lean_dec_ref(v_a_3219_);
lean_dec(v_a_3218_);
lean_dec_ref(v_a_3217_);
lean_dec(v_a_3216_);
lean_dec(v_c_3215_);
return v_res_3222_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(lean_object* v_a_3223_, lean_object* v_fallback_3224_, lean_object* v_x_3225_){
_start:
{
if (lean_obj_tag(v_x_3225_) == 0)
{
lean_inc(v_fallback_3224_);
return v_fallback_3224_;
}
else
{
lean_object* v_key_3226_; lean_object* v_value_3227_; lean_object* v_tail_3228_; uint8_t v___x_3229_; 
v_key_3226_ = lean_ctor_get(v_x_3225_, 0);
v_value_3227_ = lean_ctor_get(v_x_3225_, 1);
v_tail_3228_ = lean_ctor_get(v_x_3225_, 2);
v___x_3229_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_3226_, v_a_3223_);
if (v___x_3229_ == 0)
{
v_x_3225_ = v_tail_3228_;
goto _start;
}
else
{
lean_inc(v_value_3227_);
return v_value_3227_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg___boxed(lean_object* v_a_3231_, lean_object* v_fallback_3232_, lean_object* v_x_3233_){
_start:
{
lean_object* v_res_3234_; 
v_res_3234_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(v_a_3231_, v_fallback_3232_, v_x_3233_);
lean_dec(v_x_3233_);
lean_dec(v_fallback_3232_);
lean_dec(v_a_3231_);
return v_res_3234_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(lean_object* v_m_3235_, lean_object* v_a_3236_, lean_object* v_fallback_3237_){
_start:
{
lean_object* v_buckets_3238_; lean_object* v___x_3239_; uint64_t v___x_3240_; uint64_t v___x_3241_; uint64_t v___x_3242_; uint64_t v_fold_3243_; uint64_t v___x_3244_; uint64_t v___x_3245_; uint64_t v___x_3246_; size_t v___x_3247_; size_t v___x_3248_; size_t v___x_3249_; size_t v___x_3250_; size_t v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; 
v_buckets_3238_ = lean_ctor_get(v_m_3235_, 1);
v___x_3239_ = lean_array_get_size(v_buckets_3238_);
v___x_3240_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_a_3236_);
v___x_3241_ = 32ULL;
v___x_3242_ = lean_uint64_shift_right(v___x_3240_, v___x_3241_);
v_fold_3243_ = lean_uint64_xor(v___x_3240_, v___x_3242_);
v___x_3244_ = 16ULL;
v___x_3245_ = lean_uint64_shift_right(v_fold_3243_, v___x_3244_);
v___x_3246_ = lean_uint64_xor(v_fold_3243_, v___x_3245_);
v___x_3247_ = lean_uint64_to_usize(v___x_3246_);
v___x_3248_ = lean_usize_of_nat(v___x_3239_);
v___x_3249_ = ((size_t)1ULL);
v___x_3250_ = lean_usize_sub(v___x_3248_, v___x_3249_);
v___x_3251_ = lean_usize_land(v___x_3247_, v___x_3250_);
v___x_3252_ = lean_array_uget_borrowed(v_buckets_3238_, v___x_3251_);
v___x_3253_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(v_a_3236_, v_fallback_3237_, v___x_3252_);
return v___x_3253_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg___boxed(lean_object* v_m_3254_, lean_object* v_a_3255_, lean_object* v_fallback_3256_){
_start:
{
lean_object* v_res_3257_; 
v_res_3257_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_m_3254_, v_a_3255_, v_fallback_3256_);
lean_dec(v_fallback_3256_);
lean_dec(v_a_3255_);
lean_dec_ref(v_m_3254_);
return v_res_3257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg(lean_object* v_next_3258_, lean_object* v_rest_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_){
_start:
{
lean_object* v___x_3266_; uint8_t v___x_3267_; 
v___x_3266_ = lean_unsigned_to_nat(0u);
v___x_3267_ = lean_nat_dec_eq(v_next_3258_, v___x_3266_);
if (v___x_3267_ == 0)
{
lean_object* v___x_3268_; 
v___x_3268_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_next_3258_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_, v_a_3264_);
if (lean_obj_tag(v___x_3268_) == 0)
{
lean_object* v_a_3269_; lean_object* v___x_3271_; uint8_t v_isShared_3272_; uint8_t v_isSharedCheck_3294_; 
v_a_3269_ = lean_ctor_get(v___x_3268_, 0);
v_isSharedCheck_3294_ = !lean_is_exclusive(v___x_3268_);
if (v_isSharedCheck_3294_ == 0)
{
v___x_3271_ = v___x_3268_;
v_isShared_3272_ = v_isSharedCheck_3294_;
goto v_resetjp_3270_;
}
else
{
lean_inc(v_a_3269_);
lean_dec(v___x_3268_);
v___x_3271_ = lean_box(0);
v_isShared_3272_ = v_isSharedCheck_3294_;
goto v_resetjp_3270_;
}
v_resetjp_3270_:
{
lean_object* v_snd_3273_; 
v_snd_3273_ = lean_ctor_get(v_a_3269_, 1);
lean_inc(v_snd_3273_);
lean_dec(v_a_3269_);
if (lean_obj_tag(v_rest_3259_) == 0)
{
lean_object* v_fst_3274_; lean_object* v_snd_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3283_; 
v_fst_3274_ = lean_ctor_get(v_snd_3273_, 0);
lean_inc(v_fst_3274_);
v_snd_3275_ = lean_ctor_get(v_snd_3273_, 1);
lean_inc(v_snd_3275_);
lean_dec(v_snd_3273_);
v___x_3276_ = lean_st_ref_take(v_a_3260_);
v___x_3277_ = lean_box(0);
v___x_3278_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___x_3279_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3279_, 0, v___x_3278_);
lean_ctor_set(v___x_3279_, 1, v_fst_3274_);
lean_ctor_set(v___x_3279_, 2, v_snd_3275_);
lean_ctor_set(v___x_3279_, 3, v___x_3278_);
v___x_3280_ = lean_array_set(v___x_3276_, v_next_3258_, v___x_3279_);
lean_dec(v_next_3258_);
v___x_3281_ = lean_st_ref_put(v_a_3260_, v___x_3280_);
if (v_isShared_3272_ == 0)
{
lean_ctor_set(v___x_3271_, 0, v___x_3277_);
v___x_3283_ = v___x_3271_;
goto v_reusejp_3282_;
}
else
{
lean_object* v_reuseFailAlloc_3284_; 
v_reuseFailAlloc_3284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3284_, 0, v___x_3277_);
v___x_3283_ = v_reuseFailAlloc_3284_;
goto v_reusejp_3282_;
}
v_reusejp_3282_:
{
return v___x_3283_;
}
}
else
{
lean_object* v_fst_3285_; lean_object* v_snd_3286_; lean_object* v_head_3287_; lean_object* v_tail_3288_; lean_object* v___x_3289_; uint8_t v___x_3290_; 
lean_del_object(v___x_3271_);
lean_dec(v_next_3258_);
v_fst_3285_ = lean_ctor_get(v_snd_3273_, 0);
lean_inc(v_fst_3285_);
v_snd_3286_ = lean_ctor_get(v_snd_3273_, 1);
lean_inc(v_snd_3286_);
lean_dec(v_snd_3273_);
v_head_3287_ = lean_ctor_get(v_rest_3259_, 0);
v_tail_3288_ = lean_ctor_get(v_rest_3259_, 1);
v___x_3289_ = lean_box(3);
v___x_3290_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_head_3287_, v___x_3289_);
if (v___x_3290_ == 0)
{
lean_object* v___x_3291_; 
lean_dec(v_fst_3285_);
v___x_3291_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_snd_3286_, v_head_3287_, v___x_3266_);
lean_dec(v_snd_3286_);
v_next_3258_ = v___x_3291_;
v_rest_3259_ = v_tail_3288_;
goto _start;
}
else
{
lean_dec(v_snd_3286_);
v_next_3258_ = v_fst_3285_;
v_rest_3259_ = v_tail_3288_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3302_; 
lean_dec(v_next_3258_);
v_a_3295_ = lean_ctor_get(v___x_3268_, 0);
v_isSharedCheck_3302_ = !lean_is_exclusive(v___x_3268_);
if (v_isSharedCheck_3302_ == 0)
{
v___x_3297_ = v___x_3268_;
v_isShared_3298_ = v_isSharedCheck_3302_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_a_3295_);
lean_dec(v___x_3268_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3302_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
lean_object* v___x_3300_; 
if (v_isShared_3298_ == 0)
{
v___x_3300_ = v___x_3297_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v_a_3295_);
v___x_3300_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
return v___x_3300_;
}
}
}
}
else
{
lean_object* v___x_3303_; lean_object* v___x_3304_; 
lean_dec(v_next_3258_);
v___x_3303_ = lean_box(0);
v___x_3304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3304_, 0, v___x_3303_);
return v___x_3304_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg___boxed(lean_object* v_next_3305_, lean_object* v_rest_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_){
_start:
{
lean_object* v_res_3313_; 
v_res_3313_ = l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg(v_next_3305_, v_rest_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_);
lean_dec(v_a_3311_);
lean_dec_ref(v_a_3310_);
lean_dec(v_a_3309_);
lean_dec_ref(v_a_3308_);
lean_dec(v_a_3307_);
lean_dec(v_rest_3306_);
return v_res_3313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux(lean_object* v_00_u03b1_3314_, lean_object* v_next_3315_, lean_object* v_rest_3316_, lean_object* v_a_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_){
_start:
{
lean_object* v___x_3323_; 
v___x_3323_ = l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg(v_next_3315_, v_rest_3316_, v_a_3317_, v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_);
return v___x_3323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux___boxed(lean_object* v_00_u03b1_3324_, lean_object* v_next_3325_, lean_object* v_rest_3326_, lean_object* v_a_3327_, lean_object* v_a_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_, lean_object* v_a_3331_, lean_object* v_a_3332_){
_start:
{
lean_object* v_res_3333_; 
v_res_3333_ = l_Lean_Meta_LazyDiscrTree_dropKeyAux(v_00_u03b1_3324_, v_next_3325_, v_rest_3326_, v_a_3327_, v_a_3328_, v_a_3329_, v_a_3330_, v_a_3331_);
lean_dec(v_a_3331_);
lean_dec_ref(v_a_3330_);
lean_dec(v_a_3329_);
lean_dec_ref(v_a_3328_);
lean_dec(v_a_3327_);
lean_dec(v_rest_3326_);
return v_res_3333_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0(lean_object* v_00_u03b2_3334_, lean_object* v_m_3335_, lean_object* v_a_3336_, lean_object* v_fallback_3337_){
_start:
{
lean_object* v___x_3338_; 
v___x_3338_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_m_3335_, v_a_3336_, v_fallback_3337_);
return v___x_3338_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___boxed(lean_object* v_00_u03b2_3339_, lean_object* v_m_3340_, lean_object* v_a_3341_, lean_object* v_fallback_3342_){
_start:
{
lean_object* v_res_3343_; 
v_res_3343_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0(v_00_u03b2_3339_, v_m_3340_, v_a_3341_, v_fallback_3342_);
lean_dec(v_fallback_3342_);
lean_dec(v_a_3341_);
lean_dec_ref(v_m_3340_);
return v_res_3343_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0(lean_object* v_00_u03b2_3344_, lean_object* v_a_3345_, lean_object* v_fallback_3346_, lean_object* v_x_3347_){
_start:
{
lean_object* v___x_3348_; 
v___x_3348_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(v_a_3345_, v_fallback_3346_, v_x_3347_);
return v___x_3348_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3349_, lean_object* v_a_3350_, lean_object* v_fallback_3351_, lean_object* v_x_3352_){
_start:
{
lean_object* v_res_3353_; 
v_res_3353_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0(v_00_u03b2_3349_, v_a_3350_, v_fallback_3351_, v_x_3352_);
lean_dec(v_x_3352_);
lean_dec(v_fallback_3351_);
lean_dec(v_a_3350_);
return v_res_3353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey___redArg(lean_object* v_t_3354_, lean_object* v_path_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_){
_start:
{
if (lean_obj_tag(v_path_3355_) == 0)
{
lean_object* v___x_3361_; 
v___x_3361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3361_, 0, v_t_3354_);
return v___x_3361_;
}
else
{
lean_object* v_head_3362_; lean_object* v_tail_3363_; lean_object* v_roots_3364_; lean_object* v___x_3365_; lean_object* v_idx_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; 
v_head_3362_ = lean_ctor_get(v_path_3355_, 0);
lean_inc(v_head_3362_);
v_tail_3363_ = lean_ctor_get(v_path_3355_, 1);
lean_inc(v_tail_3363_);
lean_dec_ref_known(v_path_3355_, 2);
v_roots_3364_ = lean_ctor_get(v_t_3354_, 1);
v___x_3365_ = lean_unsigned_to_nat(0u);
v_idx_3366_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_roots_3364_, v_head_3362_, v___x_3365_);
lean_dec(v_head_3362_);
v___x_3367_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_dropKeyAux___boxed), 9, 3);
lean_closure_set(v___x_3367_, 0, lean_box(0));
lean_closure_set(v___x_3367_, 1, v_idx_3366_);
lean_closure_set(v___x_3367_, 2, v_tail_3363_);
v___x_3368_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_t_3354_, v___x_3367_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
if (lean_obj_tag(v___x_3368_) == 0)
{
lean_object* v_a_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3377_; 
v_a_3369_ = lean_ctor_get(v___x_3368_, 0);
v_isSharedCheck_3377_ = !lean_is_exclusive(v___x_3368_);
if (v_isSharedCheck_3377_ == 0)
{
v___x_3371_ = v___x_3368_;
v_isShared_3372_ = v_isSharedCheck_3377_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_a_3369_);
lean_dec(v___x_3368_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3377_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
lean_object* v_snd_3373_; lean_object* v___x_3375_; 
v_snd_3373_ = lean_ctor_get(v_a_3369_, 1);
lean_inc(v_snd_3373_);
lean_dec(v_a_3369_);
if (v_isShared_3372_ == 0)
{
lean_ctor_set(v___x_3371_, 0, v_snd_3373_);
v___x_3375_ = v___x_3371_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3376_; 
v_reuseFailAlloc_3376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3376_, 0, v_snd_3373_);
v___x_3375_ = v_reuseFailAlloc_3376_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
return v___x_3375_;
}
}
}
else
{
lean_object* v_a_3378_; lean_object* v___x_3380_; uint8_t v_isShared_3381_; uint8_t v_isSharedCheck_3385_; 
v_a_3378_ = lean_ctor_get(v___x_3368_, 0);
v_isSharedCheck_3385_ = !lean_is_exclusive(v___x_3368_);
if (v_isSharedCheck_3385_ == 0)
{
v___x_3380_ = v___x_3368_;
v_isShared_3381_ = v_isSharedCheck_3385_;
goto v_resetjp_3379_;
}
else
{
lean_inc(v_a_3378_);
lean_dec(v___x_3368_);
v___x_3380_ = lean_box(0);
v_isShared_3381_ = v_isSharedCheck_3385_;
goto v_resetjp_3379_;
}
v_resetjp_3379_:
{
lean_object* v___x_3383_; 
if (v_isShared_3381_ == 0)
{
v___x_3383_ = v___x_3380_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3384_; 
v_reuseFailAlloc_3384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3384_, 0, v_a_3378_);
v___x_3383_ = v_reuseFailAlloc_3384_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
return v___x_3383_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey___redArg___boxed(lean_object* v_t_3386_, lean_object* v_path_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_, lean_object* v_a_3392_){
_start:
{
lean_object* v_res_3393_; 
v_res_3393_ = l_Lean_Meta_LazyDiscrTree_dropKey___redArg(v_t_3386_, v_path_3387_, v_a_3388_, v_a_3389_, v_a_3390_, v_a_3391_);
lean_dec(v_a_3391_);
lean_dec_ref(v_a_3390_);
lean_dec(v_a_3389_);
lean_dec_ref(v_a_3388_);
return v_res_3393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey(lean_object* v_00_u03b1_3394_, lean_object* v_t_3395_, lean_object* v_path_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_){
_start:
{
lean_object* v___x_3402_; 
v___x_3402_ = l_Lean_Meta_LazyDiscrTree_dropKey___redArg(v_t_3395_, v_path_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_);
return v___x_3402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey___boxed(lean_object* v_00_u03b1_3403_, lean_object* v_t_3404_, lean_object* v_path_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_, lean_object* v_a_3408_, lean_object* v_a_3409_, lean_object* v_a_3410_){
_start:
{
lean_object* v_res_3411_; 
v_res_3411_ = l_Lean_Meta_LazyDiscrTree_dropKey(v_00_u03b1_3403_, v_t_3404_, v_path_3405_, v_a_3406_, v_a_3407_, v_a_3408_, v_a_3409_);
lean_dec(v_a_3409_);
lean_dec_ref(v_a_3408_);
lean_dec(v_a_3407_);
lean_dec_ref(v_a_3406_);
return v_res_3411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(lean_object* v_score_3414_, lean_object* v_e_3415_, lean_object* v_a_3416_){
_start:
{
lean_object* v___x_3417_; uint8_t v___x_3418_; 
v___x_3417_ = lean_array_get_size(v_a_3416_);
v___x_3418_ = lean_nat_dec_lt(v___x_3417_, v_score_3414_);
if (v___x_3418_ == 0)
{
lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; 
v___x_3419_ = lean_unsigned_to_nat(1u);
v___x_3420_ = lean_mk_empty_array_with_capacity(v___x_3419_);
v___x_3421_ = lean_array_push(v___x_3420_, v_e_3415_);
v___x_3422_ = lean_array_push(v_a_3416_, v___x_3421_);
return v___x_3422_;
}
else
{
lean_object* v___x_3423_; lean_object* v___x_3424_; 
v___x_3423_ = ((lean_object*)(l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg___closed__0));
v___x_3424_ = lean_array_push(v_a_3416_, v___x_3423_);
v_a_3416_ = v___x_3424_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg___boxed(lean_object* v_score_3426_, lean_object* v_e_3427_, lean_object* v_a_3428_){
_start:
{
lean_object* v_res_3429_; 
v_res_3429_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(v_score_3426_, v_e_3427_, v_a_3428_);
lean_dec(v_score_3426_);
return v_res_3429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop(lean_object* v_00_u03b1_3430_, lean_object* v_score_3431_, lean_object* v_e_3432_, lean_object* v_a_3433_){
_start:
{
lean_object* v___x_3434_; 
v___x_3434_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(v_score_3431_, v_e_3432_, v_a_3433_);
return v___x_3434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___boxed(lean_object* v_00_u03b1_3435_, lean_object* v_score_3436_, lean_object* v_e_3437_, lean_object* v_a_3438_){
_start:
{
lean_object* v_res_3439_; 
v_res_3439_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop(v_00_u03b1_3435_, v_score_3436_, v_e_3437_, v_a_3438_);
lean_dec(v_score_3436_);
return v_res_3439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(lean_object* v_r_3440_, lean_object* v_score_3441_, lean_object* v_e_3442_){
_start:
{
lean_object* v___x_3443_; lean_object* v___x_3444_; uint8_t v___x_3445_; 
v___x_3443_ = lean_array_get_size(v_e_3442_);
v___x_3444_ = lean_unsigned_to_nat(0u);
v___x_3445_ = lean_nat_dec_eq(v___x_3443_, v___x_3444_);
if (v___x_3445_ == 0)
{
lean_object* v___x_3446_; uint8_t v___x_3447_; 
v___x_3446_ = lean_array_get_size(v_r_3440_);
v___x_3447_ = lean_nat_dec_lt(v_score_3441_, v___x_3446_);
if (v___x_3447_ == 0)
{
lean_object* v___x_3448_; 
v___x_3448_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(v_score_3441_, v_e_3442_, v_r_3440_);
return v___x_3448_;
}
else
{
lean_object* v_v_3449_; lean_object* v___x_3450_; lean_object* v_xs_x27_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; 
v_v_3449_ = lean_array_fget(v_r_3440_, v_score_3441_);
v___x_3450_ = lean_box(0);
v_xs_x27_3451_ = lean_array_fset(v_r_3440_, v_score_3441_, v___x_3450_);
v___x_3452_ = lean_array_push(v_v_3449_, v_e_3442_);
v___x_3453_ = lean_array_fset(v_xs_x27_3451_, v_score_3441_, v___x_3452_);
return v___x_3453_;
}
}
else
{
lean_dec_ref(v_e_3442_);
return v_r_3440_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg___boxed(lean_object* v_r_3454_, lean_object* v_score_3455_, lean_object* v_e_3456_){
_start:
{
lean_object* v_res_3457_; 
v_res_3457_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v_r_3454_, v_score_3455_, v_e_3456_);
lean_dec(v_score_3455_);
return v_res_3457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push(lean_object* v_00_u03b1_3458_, lean_object* v_r_3459_, lean_object* v_score_3460_, lean_object* v_e_3461_){
_start:
{
lean_object* v___x_3462_; 
v___x_3462_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v_r_3459_, v_score_3460_, v_e_3461_);
return v___x_3462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push___boxed(lean_object* v_00_u03b1_3463_, lean_object* v_r_3464_, lean_object* v_score_3465_, lean_object* v_e_3466_){
_start:
{
lean_object* v_res_3467_; 
v_res_3467_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push(v_00_u03b1_3463_, v_r_3464_, v_score_3465_, v_e_3466_);
lean_dec(v_score_3465_);
return v_res_3467_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(lean_object* v_as_3468_, size_t v_i_3469_, size_t v_stop_3470_, lean_object* v_b_3471_){
_start:
{
uint8_t v___x_3472_; 
v___x_3472_ = lean_usize_dec_eq(v_i_3469_, v_stop_3470_);
if (v___x_3472_ == 0)
{
lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; size_t v___x_3476_; size_t v___x_3477_; 
v___x_3473_ = lean_array_uget_borrowed(v_as_3468_, v_i_3469_);
v___x_3474_ = lean_array_get_size(v___x_3473_);
v___x_3475_ = lean_nat_add(v_b_3471_, v___x_3474_);
lean_dec(v_b_3471_);
v___x_3476_ = ((size_t)1ULL);
v___x_3477_ = lean_usize_add(v_i_3469_, v___x_3476_);
v_i_3469_ = v___x_3477_;
v_b_3471_ = v___x_3475_;
goto _start;
}
else
{
return v_b_3471_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg___boxed(lean_object* v_as_3479_, lean_object* v_i_3480_, lean_object* v_stop_3481_, lean_object* v_b_3482_){
_start:
{
size_t v_i_boxed_3483_; size_t v_stop_boxed_3484_; lean_object* v_res_3485_; 
v_i_boxed_3483_ = lean_unbox_usize(v_i_3480_);
lean_dec(v_i_3480_);
v_stop_boxed_3484_ = lean_unbox_usize(v_stop_3481_);
lean_dec(v_stop_3481_);
v_res_3485_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v_as_3479_, v_i_boxed_3483_, v_stop_boxed_3484_, v_b_3482_);
lean_dec_ref(v_as_3479_);
return v_res_3485_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(lean_object* v_as_3486_, size_t v_i_3487_, size_t v_stop_3488_, lean_object* v_b_3489_){
_start:
{
lean_object* v___y_3491_; uint8_t v___x_3495_; 
v___x_3495_ = lean_usize_dec_eq(v_i_3487_, v_stop_3488_);
if (v___x_3495_ == 0)
{
lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; uint8_t v___x_3499_; 
v___x_3496_ = lean_array_uget_borrowed(v_as_3486_, v_i_3487_);
v___x_3497_ = lean_unsigned_to_nat(0u);
v___x_3498_ = lean_array_get_size(v___x_3496_);
v___x_3499_ = lean_nat_dec_lt(v___x_3497_, v___x_3498_);
if (v___x_3499_ == 0)
{
v___y_3491_ = v_b_3489_;
goto v___jp_3490_;
}
else
{
size_t v___x_3500_; size_t v___x_3501_; lean_object* v___x_3502_; 
v___x_3500_ = ((size_t)0ULL);
v___x_3501_ = lean_usize_of_nat(v___x_3498_);
v___x_3502_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v___x_3496_, v___x_3500_, v___x_3501_, v_b_3489_);
v___y_3491_ = v___x_3502_;
goto v___jp_3490_;
}
}
else
{
return v_b_3489_;
}
v___jp_3490_:
{
size_t v___x_3492_; size_t v___x_3493_; 
v___x_3492_ = ((size_t)1ULL);
v___x_3493_ = lean_usize_add(v_i_3487_, v___x_3492_);
v_i_3487_ = v___x_3493_;
v_b_3489_ = v___y_3491_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg___boxed(lean_object* v_as_3503_, lean_object* v_i_3504_, lean_object* v_stop_3505_, lean_object* v_b_3506_){
_start:
{
size_t v_i_boxed_3507_; size_t v_stop_boxed_3508_; lean_object* v_res_3509_; 
v_i_boxed_3507_ = lean_unbox_usize(v_i_3504_);
lean_dec(v_i_3504_);
v_stop_boxed_3508_ = lean_unbox_usize(v_stop_3505_);
lean_dec(v_stop_3505_);
v_res_3509_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_as_3503_, v_i_boxed_3507_, v_stop_boxed_3508_, v_b_3506_);
lean_dec_ref(v_as_3503_);
return v_res_3509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(lean_object* v_mr_3510_){
_start:
{
lean_object* v___x_3511_; lean_object* v___x_3512_; uint8_t v___x_3513_; 
v___x_3511_ = lean_unsigned_to_nat(0u);
v___x_3512_ = lean_array_get_size(v_mr_3510_);
v___x_3513_ = lean_nat_dec_lt(v___x_3511_, v___x_3512_);
if (v___x_3513_ == 0)
{
return v___x_3511_;
}
else
{
size_t v___x_3514_; size_t v___x_3515_; lean_object* v___x_3516_; 
v___x_3514_ = ((size_t)0ULL);
v___x_3515_ = lean_usize_of_nat(v___x_3512_);
v___x_3516_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_mr_3510_, v___x_3514_, v___x_3515_, v___x_3511_);
return v___x_3516_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg___boxed(lean_object* v_mr_3517_){
_start:
{
lean_object* v_res_3518_; 
v_res_3518_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_mr_3517_);
lean_dec_ref(v_mr_3517_);
return v_res_3518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size(lean_object* v_00_u03b1_3519_, lean_object* v_mr_3520_){
_start:
{
lean_object* v___x_3521_; 
v___x_3521_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_mr_3520_);
return v___x_3521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size___boxed(lean_object* v_00_u03b1_3522_, lean_object* v_mr_3523_){
_start:
{
lean_object* v_res_3524_; 
v_res_3524_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size(v_00_u03b1_3522_, v_mr_3523_);
lean_dec_ref(v_mr_3523_);
return v_res_3524_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0(lean_object* v_00_u03b1_3525_, lean_object* v_as_3526_, size_t v_i_3527_, size_t v_stop_3528_, lean_object* v_b_3529_){
_start:
{
lean_object* v___x_3530_; 
v___x_3530_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v_as_3526_, v_i_3527_, v_stop_3528_, v_b_3529_);
return v___x_3530_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___boxed(lean_object* v_00_u03b1_3531_, lean_object* v_as_3532_, lean_object* v_i_3533_, lean_object* v_stop_3534_, lean_object* v_b_3535_){
_start:
{
size_t v_i_boxed_3536_; size_t v_stop_boxed_3537_; lean_object* v_res_3538_; 
v_i_boxed_3536_ = lean_unbox_usize(v_i_3533_);
lean_dec(v_i_3533_);
v_stop_boxed_3537_ = lean_unbox_usize(v_stop_3534_);
lean_dec(v_stop_3534_);
v_res_3538_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0(v_00_u03b1_3531_, v_as_3532_, v_i_boxed_3536_, v_stop_boxed_3537_, v_b_3535_);
lean_dec_ref(v_as_3532_);
return v_res_3538_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1(lean_object* v_00_u03b1_3539_, lean_object* v_as_3540_, size_t v_i_3541_, size_t v_stop_3542_, lean_object* v_b_3543_){
_start:
{
lean_object* v___x_3544_; 
v___x_3544_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_as_3540_, v_i_3541_, v_stop_3542_, v_b_3543_);
return v___x_3544_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___boxed(lean_object* v_00_u03b1_3545_, lean_object* v_as_3546_, lean_object* v_i_3547_, lean_object* v_stop_3548_, lean_object* v_b_3549_){
_start:
{
size_t v_i_boxed_3550_; size_t v_stop_boxed_3551_; lean_object* v_res_3552_; 
v_i_boxed_3550_ = lean_unbox_usize(v_i_3547_);
lean_dec(v_i_3547_);
v_stop_boxed_3551_ = lean_unbox_usize(v_stop_3548_);
lean_dec(v_stop_3548_);
v_res_3552_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1(v_00_u03b1_3545_, v_as_3546_, v_i_boxed_3550_, v_stop_boxed_3551_, v_b_3549_);
lean_dec_ref(v_as_3546_);
return v_res_3552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__0(lean_object* v_f_3553_, lean_object* v_j_3554_, lean_object* v_x_3555_){
_start:
{
lean_object* v___x_3556_; 
v___x_3556_ = lean_apply_2(v_f_3553_, v_j_3554_, v_x_3555_);
return v___x_3556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1(lean_object* v___f_3576_, lean_object* v_x1_3577_, lean_object* v_x2_3578_){
_start:
{
lean_object* v___x_3579_; size_t v_sz_3580_; size_t v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; 
v___x_3579_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__9));
v_sz_3580_ = lean_array_size(v_x2_3578_);
v___x_3581_ = ((size_t)0ULL);
v___x_3582_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3579_, v___f_3576_, v_sz_3580_, v___x_3581_, v_x2_3578_);
v___x_3583_ = l_Array_append___redArg(v_x1_3577_, v___x_3582_);
lean_dec(v___x_3582_);
return v___x_3583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2(lean_object* v_n_3584_, lean_object* v_mr_3585_, lean_object* v_f_3586_, lean_object* v_i_3587_, lean_object* v_x_3588_, lean_object* v_r_3589_){
_start:
{
lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v_j_3592_; lean_object* v_b_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; uint8_t v___x_3597_; 
v___x_3590_ = lean_unsigned_to_nat(1u);
v___x_3591_ = lean_nat_sub(v_n_3584_, v___x_3590_);
v_j_3592_ = lean_nat_sub(v___x_3591_, v_i_3587_);
lean_dec(v___x_3591_);
v_b_3593_ = lean_array_fget_borrowed(v_mr_3585_, v_j_3592_);
v___x_3594_ = lean_unsigned_to_nat(0u);
v___x_3595_ = lean_array_get_size(v_b_3593_);
v___x_3596_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__9));
v___x_3597_ = lean_nat_dec_lt(v___x_3594_, v___x_3595_);
if (v___x_3597_ == 0)
{
lean_dec(v_j_3592_);
lean_dec(v_f_3586_);
return v_r_3589_;
}
else
{
lean_object* v___f_3598_; lean_object* v___f_3599_; size_t v___x_3600_; size_t v___x_3601_; lean_object* v___x_3602_; 
v___f_3598_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3598_, 0, v_f_3586_);
lean_closure_set(v___f_3598_, 1, v_j_3592_);
v___f_3599_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1), 3, 1);
lean_closure_set(v___f_3599_, 0, v___f_3598_);
v___x_3600_ = ((size_t)0ULL);
v___x_3601_ = lean_usize_of_nat(v___x_3595_);
lean_inc(v_b_3593_);
v___x_3602_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3596_, v___f_3599_, v_b_3593_, v___x_3600_, v___x_3601_, v_r_3589_);
return v___x_3602_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2___boxed(lean_object* v_n_3603_, lean_object* v_mr_3604_, lean_object* v_f_3605_, lean_object* v_i_3606_, lean_object* v_x_3607_, lean_object* v_r_3608_){
_start:
{
lean_object* v_res_3609_; 
v_res_3609_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2(v_n_3603_, v_mr_3604_, v_f_3605_, v_i_3606_, v_x_3607_, v_r_3608_);
lean_dec(v_i_3606_);
lean_dec_ref(v_mr_3604_);
lean_dec(v_n_3603_);
return v_res_3609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg(lean_object* v_mr_3610_, lean_object* v_a_3611_, lean_object* v_f_3612_){
_start:
{
lean_object* v_n_3613_; lean_object* v___f_3614_; lean_object* v___x_3615_; 
v_n_3613_ = lean_array_get_size(v_mr_3610_);
v___f_3614_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_3614_, 0, v_n_3613_);
lean_closure_set(v___f_3614_, 1, v_mr_3610_);
lean_closure_set(v___f_3614_, 2, v_f_3612_);
v___x_3615_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop(lean_box(0), v_n_3613_, v___f_3614_, v_n_3613_, lean_box(0), v_a_3611_);
return v___x_3615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux(lean_object* v_00_u03b1_3616_, lean_object* v_00_u03b2_3617_, lean_object* v_mr_3618_, lean_object* v_a_3619_, lean_object* v_f_3620_){
_start:
{
lean_object* v___x_3621_; 
v___x_3621_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg(v_mr_3618_, v_a_3619_, v_f_3620_);
return v___x_3621_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(size_t v_sz_3622_, size_t v_i_3623_, lean_object* v_bs_3624_){
_start:
{
uint8_t v___x_3625_; 
v___x_3625_ = lean_usize_dec_lt(v_i_3623_, v_sz_3622_);
if (v___x_3625_ == 0)
{
return v_bs_3624_;
}
else
{
lean_object* v_v_3626_; lean_object* v___x_3627_; lean_object* v_bs_x27_3628_; size_t v___x_3629_; size_t v___x_3630_; lean_object* v___x_3631_; 
v_v_3626_ = lean_array_uget(v_bs_3624_, v_i_3623_);
v___x_3627_ = lean_unsigned_to_nat(0u);
v_bs_x27_3628_ = lean_array_uset(v_bs_3624_, v_i_3623_, v___x_3627_);
v___x_3629_ = ((size_t)1ULL);
v___x_3630_ = lean_usize_add(v_i_3623_, v___x_3629_);
v___x_3631_ = lean_array_uset(v_bs_x27_3628_, v_i_3623_, v_v_3626_);
v_i_3623_ = v___x_3630_;
v_bs_3624_ = v___x_3631_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg___boxed(lean_object* v_sz_3633_, lean_object* v_i_3634_, lean_object* v_bs_3635_){
_start:
{
size_t v_sz_boxed_3636_; size_t v_i_boxed_3637_; lean_object* v_res_3638_; 
v_sz_boxed_3636_ = lean_unbox_usize(v_sz_3633_);
lean_dec(v_sz_3633_);
v_i_boxed_3637_ = lean_unbox_usize(v_i_3634_);
lean_dec(v_i_3634_);
v_res_3638_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(v_sz_boxed_3636_, v_i_boxed_3637_, v_bs_3635_);
return v_res_3638_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(lean_object* v_as_3639_, size_t v_i_3640_, size_t v_stop_3641_, lean_object* v_b_3642_){
_start:
{
uint8_t v___x_3643_; 
v___x_3643_ = lean_usize_dec_eq(v_i_3640_, v_stop_3641_);
if (v___x_3643_ == 0)
{
lean_object* v___x_3644_; size_t v_sz_3645_; size_t v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; size_t v___x_3649_; size_t v___x_3650_; 
v___x_3644_ = lean_array_uget_borrowed(v_as_3639_, v_i_3640_);
v_sz_3645_ = lean_array_size(v___x_3644_);
v___x_3646_ = ((size_t)0ULL);
lean_inc(v___x_3644_);
v___x_3647_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(v_sz_3645_, v___x_3646_, v___x_3644_);
v___x_3648_ = l_Array_append___redArg(v_b_3642_, v___x_3647_);
lean_dec_ref(v___x_3647_);
v___x_3649_ = ((size_t)1ULL);
v___x_3650_ = lean_usize_add(v_i_3640_, v___x_3649_);
v_i_3640_ = v___x_3650_;
v_b_3642_ = v___x_3648_;
goto _start;
}
else
{
return v_b_3642_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg___boxed(lean_object* v_as_3652_, lean_object* v_i_3653_, lean_object* v_stop_3654_, lean_object* v_b_3655_){
_start:
{
size_t v_i_boxed_3656_; size_t v_stop_boxed_3657_; lean_object* v_res_3658_; 
v_i_boxed_3656_ = lean_unbox_usize(v_i_3653_);
lean_dec(v_i_3653_);
v_stop_boxed_3657_ = lean_unbox_usize(v_stop_3654_);
lean_dec(v_stop_3654_);
v_res_3658_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(v_as_3652_, v_i_boxed_3656_, v_stop_boxed_3657_, v_b_3655_);
lean_dec_ref(v_as_3652_);
return v_res_3658_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(lean_object* v_n_3659_, lean_object* v_aa_3660_, lean_object* v_n_3661_, lean_object* v_j_3662_, lean_object* v_a_3663_){
_start:
{
lean_object* v_zero_3664_; uint8_t v_isZero_3665_; 
v_zero_3664_ = lean_unsigned_to_nat(0u);
v_isZero_3665_ = lean_nat_dec_eq(v_j_3662_, v_zero_3664_);
if (v_isZero_3665_ == 1)
{
lean_dec(v_j_3662_);
return v_a_3663_;
}
else
{
lean_object* v_one_3666_; lean_object* v_n_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v_j_3670_; lean_object* v_b_3671_; lean_object* v___x_3672_; uint8_t v___x_3673_; 
v_one_3666_ = lean_unsigned_to_nat(1u);
v_n_3667_ = lean_nat_sub(v_j_3662_, v_one_3666_);
v___x_3668_ = lean_nat_sub(v_n_3661_, v_j_3662_);
lean_dec(v_j_3662_);
v___x_3669_ = lean_nat_sub(v_n_3659_, v_one_3666_);
v_j_3670_ = lean_nat_sub(v___x_3669_, v___x_3668_);
lean_dec(v___x_3668_);
lean_dec(v___x_3669_);
v_b_3671_ = lean_array_fget_borrowed(v_aa_3660_, v_j_3670_);
lean_dec(v_j_3670_);
v___x_3672_ = lean_array_get_size(v_b_3671_);
v___x_3673_ = lean_nat_dec_lt(v_zero_3664_, v___x_3672_);
if (v___x_3673_ == 0)
{
v_j_3662_ = v_n_3667_;
goto _start;
}
else
{
size_t v___x_3675_; size_t v___x_3676_; lean_object* v___x_3677_; 
v___x_3675_ = ((size_t)0ULL);
v___x_3676_ = lean_usize_of_nat(v___x_3672_);
v___x_3677_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(v_b_3671_, v___x_3675_, v___x_3676_, v_a_3663_);
v_j_3662_ = v_n_3667_;
v_a_3663_ = v___x_3677_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg___boxed(lean_object* v_n_3679_, lean_object* v_aa_3680_, lean_object* v_n_3681_, lean_object* v_j_3682_, lean_object* v_a_3683_){
_start:
{
lean_object* v_res_3684_; 
v_res_3684_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(v_n_3679_, v_aa_3680_, v_n_3681_, v_j_3682_, v_a_3683_);
lean_dec(v_n_3681_);
lean_dec_ref(v_aa_3680_);
lean_dec(v_n_3679_);
return v_res_3684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(lean_object* v_mr_3685_, lean_object* v_a_3686_){
_start:
{
lean_object* v_n_3687_; lean_object* v___x_3688_; 
v_n_3687_ = lean_array_get_size(v_mr_3685_);
v___x_3688_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(v_n_3687_, v_mr_3685_, v_n_3687_, v_n_3687_, v_a_3686_);
return v___x_3688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg___boxed(lean_object* v_mr_3689_, lean_object* v_a_3690_){
_start:
{
lean_object* v_res_3691_; 
v_res_3691_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3689_, v_a_3690_);
lean_dec_ref(v_mr_3689_);
return v_res_3691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___redArg(lean_object* v_mr_3692_, lean_object* v_a_3693_){
_start:
{
lean_object* v___x_3694_; 
v___x_3694_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3692_, v_a_3693_);
return v___x_3694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___redArg___boxed(lean_object* v_mr_3695_, lean_object* v_a_3696_){
_start:
{
lean_object* v_res_3697_; 
v_res_3697_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___redArg(v_mr_3695_, v_a_3696_);
lean_dec_ref(v_mr_3695_);
return v_res_3697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults(lean_object* v_00_u03b1_3698_, lean_object* v_mr_3699_, lean_object* v_a_3700_){
_start:
{
lean_object* v___x_3701_; 
v___x_3701_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3699_, v_a_3700_);
return v___x_3701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___boxed(lean_object* v_00_u03b1_3702_, lean_object* v_mr_3703_, lean_object* v_a_3704_){
_start:
{
lean_object* v_res_3705_; 
v_res_3705_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults(v_00_u03b1_3702_, v_mr_3703_, v_a_3704_);
lean_dec_ref(v_mr_3703_);
return v_res_3705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0(lean_object* v_00_u03b1_3706_, lean_object* v_mr_3707_, lean_object* v_a_3708_){
_start:
{
lean_object* v___x_3709_; 
v___x_3709_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3707_, v_a_3708_);
return v___x_3709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___boxed(lean_object* v_00_u03b1_3710_, lean_object* v_mr_3711_, lean_object* v_a_3712_){
_start:
{
lean_object* v_res_3713_; 
v_res_3713_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0(v_00_u03b1_3710_, v_mr_3711_, v_a_3712_);
lean_dec_ref(v_mr_3711_);
return v_res_3713_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0(lean_object* v_00_u03b1_3714_, size_t v_sz_3715_, size_t v_i_3716_, lean_object* v_bs_3717_){
_start:
{
lean_object* v___x_3718_; 
v___x_3718_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(v_sz_3715_, v_i_3716_, v_bs_3717_);
return v___x_3718_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3719_, lean_object* v_sz_3720_, lean_object* v_i_3721_, lean_object* v_bs_3722_){
_start:
{
size_t v_sz_boxed_3723_; size_t v_i_boxed_3724_; lean_object* v_res_3725_; 
v_sz_boxed_3723_ = lean_unbox_usize(v_sz_3720_);
lean_dec(v_sz_3720_);
v_i_boxed_3724_ = lean_unbox_usize(v_i_3721_);
lean_dec(v_i_3721_);
v_res_3725_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0(v_00_u03b1_3719_, v_sz_boxed_3723_, v_i_boxed_3724_, v_bs_3722_);
return v_res_3725_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1(lean_object* v_00_u03b1_3726_, lean_object* v_as_3727_, size_t v_i_3728_, size_t v_stop_3729_, lean_object* v_b_3730_){
_start:
{
lean_object* v___x_3731_; 
v___x_3731_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(v_as_3727_, v_i_3728_, v_stop_3729_, v_b_3730_);
return v___x_3731_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3732_, lean_object* v_as_3733_, lean_object* v_i_3734_, lean_object* v_stop_3735_, lean_object* v_b_3736_){
_start:
{
size_t v_i_boxed_3737_; size_t v_stop_boxed_3738_; lean_object* v_res_3739_; 
v_i_boxed_3737_ = lean_unbox_usize(v_i_3734_);
lean_dec(v_i_3734_);
v_stop_boxed_3738_ = lean_unbox_usize(v_stop_3735_);
lean_dec(v_stop_3735_);
v_res_3739_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1(v_00_u03b1_3732_, v_as_3733_, v_i_boxed_3737_, v_stop_boxed_3738_, v_b_3736_);
lean_dec_ref(v_as_3733_);
return v_res_3739_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2(lean_object* v_00_u03b1_3740_, lean_object* v_n_3741_, lean_object* v_aa_3742_, lean_object* v_n_3743_, lean_object* v_j_3744_, lean_object* v_a_3745_, lean_object* v_a_3746_){
_start:
{
lean_object* v___x_3747_; 
v___x_3747_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(v_n_3741_, v_aa_3742_, v_n_3743_, v_j_3744_, v_a_3746_);
return v___x_3747_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___boxed(lean_object* v_00_u03b1_3748_, lean_object* v_n_3749_, lean_object* v_aa_3750_, lean_object* v_n_3751_, lean_object* v_j_3752_, lean_object* v_a_3753_, lean_object* v_a_3754_){
_start:
{
lean_object* v_res_3755_; 
v_res_3755_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2(v_00_u03b1_3748_, v_n_3749_, v_aa_3750_, v_n_3751_, v_j_3752_, v_a_3753_, v_a_3754_);
lean_dec(v_n_3751_);
lean_dec_ref(v_aa_3750_);
lean_dec(v_n_3749_);
return v_res_3755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0(lean_object* v_snd_3763_, lean_object* v___x_3764_, lean_object* v_score_3765_, lean_object* v___x_3766_, lean_object* v_k_3767_, lean_object* v_args_3768_, lean_object* v_cases_3769_){
_start:
{
lean_object* v___x_3770_; 
v___x_3770_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_snd_3763_, v_k_3767_);
if (lean_obj_tag(v___x_3770_) == 0)
{
lean_dec_ref(v___x_3764_);
return v_cases_3769_;
}
else
{
lean_object* v_val_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; 
v_val_3771_ = lean_ctor_get(v___x_3770_, 0);
lean_inc(v_val_3771_);
lean_dec_ref_known(v___x_3770_, 1);
v___x_3772_ = l_Array_append___redArg(v___x_3764_, v_args_3768_);
v___x_3773_ = lean_nat_add(v_score_3765_, v___x_3766_);
v___x_3774_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3774_, 0, v___x_3772_);
lean_ctor_set(v___x_3774_, 1, v___x_3773_);
lean_ctor_set(v___x_3774_, 2, v_val_3771_);
v___x_3775_ = lean_array_push(v_cases_3769_, v___x_3774_);
return v___x_3775_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0___boxed(lean_object* v_snd_3776_, lean_object* v___x_3777_, lean_object* v_score_3778_, lean_object* v___x_3779_, lean_object* v_k_3780_, lean_object* v_args_3781_, lean_object* v_cases_3782_){
_start:
{
lean_object* v_res_3783_; 
v_res_3783_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0(v_snd_3776_, v___x_3777_, v_score_3778_, v___x_3779_, v_k_3780_, v_args_3781_, v_cases_3782_);
lean_dec_ref(v_args_3781_);
lean_dec(v_k_3780_);
lean_dec(v___x_3779_);
lean_dec(v_score_3778_);
lean_dec_ref(v_snd_3776_);
return v_res_3783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(lean_object* v_cases_3784_, lean_object* v_result_3785_, lean_object* v_a_3786_, lean_object* v_a_3787_, lean_object* v_a_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_){
_start:
{
lean_object* v___x_3792_; lean_object* v___x_3793_; uint8_t v___x_3794_; 
v___x_3792_ = lean_array_get_size(v_cases_3784_);
v___x_3793_ = lean_unsigned_to_nat(0u);
v___x_3794_ = lean_nat_dec_eq(v___x_3792_, v___x_3793_);
if (v___x_3794_ == 0)
{
lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v_ca_3798_; lean_object* v_todo_3799_; lean_object* v_score_3800_; lean_object* v_c_3801_; lean_object* v___x_3803_; uint8_t v_isShared_3804_; uint8_t v_isSharedCheck_3867_; 
v___x_3795_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedPartialMatch_default));
v___x_3796_ = lean_unsigned_to_nat(1u);
v___x_3797_ = lean_nat_sub(v___x_3792_, v___x_3796_);
v_ca_3798_ = lean_array_get(v___x_3795_, v_cases_3784_, v___x_3797_);
lean_dec(v___x_3797_);
v_todo_3799_ = lean_ctor_get(v_ca_3798_, 0);
v_score_3800_ = lean_ctor_get(v_ca_3798_, 1);
v_c_3801_ = lean_ctor_get(v_ca_3798_, 2);
v_isSharedCheck_3867_ = !lean_is_exclusive(v_ca_3798_);
if (v_isSharedCheck_3867_ == 0)
{
v___x_3803_ = v_ca_3798_;
v_isShared_3804_ = v_isSharedCheck_3867_;
goto v_resetjp_3802_;
}
else
{
lean_inc(v_c_3801_);
lean_inc(v_score_3800_);
lean_inc(v_todo_3799_);
lean_dec(v_ca_3798_);
v___x_3803_ = lean_box(0);
v_isShared_3804_ = v_isSharedCheck_3867_;
goto v_resetjp_3802_;
}
v_resetjp_3802_:
{
lean_object* v___x_3805_; lean_object* v_cases_3806_; lean_object* v___x_3807_; 
v___x_3805_ = l_Lean_instInhabitedExpr;
v_cases_3806_ = lean_array_pop(v_cases_3784_);
v___x_3807_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_c_3801_, v_a_3786_, v_a_3787_, v_a_3788_, v_a_3789_, v_a_3790_);
lean_dec(v_c_3801_);
if (lean_obj_tag(v___x_3807_) == 0)
{
lean_object* v_a_3808_; lean_object* v___y_3810_; uint8_t v___y_3811_; lean_object* v___y_3812_; lean_object* v___y_3813_; lean_object* v_snd_3836_; lean_object* v_fst_3837_; lean_object* v_fst_3838_; lean_object* v_snd_3839_; lean_object* v___x_3840_; uint8_t v___y_3842_; uint8_t v___x_3852_; 
v_a_3808_ = lean_ctor_get(v___x_3807_, 0);
lean_inc(v_a_3808_);
lean_dec_ref_known(v___x_3807_, 1);
v_snd_3836_ = lean_ctor_get(v_a_3808_, 1);
lean_inc(v_snd_3836_);
v_fst_3837_ = lean_ctor_get(v_a_3808_, 0);
lean_inc(v_fst_3837_);
lean_dec(v_a_3808_);
v_fst_3838_ = lean_ctor_get(v_snd_3836_, 0);
lean_inc(v_fst_3838_);
v_snd_3839_ = lean_ctor_get(v_snd_3836_, 1);
lean_inc(v_snd_3839_);
lean_dec(v_snd_3836_);
v___x_3840_ = lean_array_get_size(v_todo_3799_);
v___x_3852_ = lean_nat_dec_eq(v___x_3840_, v___x_3793_);
if (v___x_3852_ == 0)
{
uint8_t v___x_3853_; 
lean_dec(v_fst_3837_);
v___x_3853_ = lean_nat_dec_eq(v_fst_3838_, v___x_3793_);
if (v___x_3853_ == 0)
{
v___y_3842_ = v___x_3852_;
goto v___jp_3841_;
}
else
{
lean_object* v_size_3854_; uint8_t v___x_3855_; 
v_size_3854_ = lean_ctor_get(v_snd_3839_, 0);
v___x_3855_ = lean_nat_dec_eq(v_size_3854_, v___x_3793_);
if (v___x_3855_ == 0)
{
v___y_3842_ = v___x_3855_;
goto v___jp_3841_;
}
else
{
lean_dec(v_snd_3839_);
lean_dec(v_fst_3838_);
lean_del_object(v___x_3803_);
lean_dec(v_score_3800_);
lean_dec_ref(v_todo_3799_);
v_cases_3784_ = v_cases_3806_;
goto _start;
}
}
}
else
{
lean_object* v___x_3857_; 
lean_dec(v_snd_3839_);
lean_dec(v_fst_3838_);
lean_del_object(v___x_3803_);
lean_dec_ref(v_todo_3799_);
v___x_3857_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v_result_3785_, v_score_3800_, v_fst_3837_);
lean_dec(v_score_3800_);
v_cases_3784_ = v_cases_3806_;
v_result_3785_ = v___x_3857_;
goto _start;
}
v___jp_3809_:
{
uint8_t v___x_3814_; lean_object* v___x_3815_; 
v___x_3814_ = 1;
v___x_3815_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v___y_3812_, v___x_3814_, v___y_3811_, v_a_3787_, v_a_3788_, v_a_3789_, v_a_3790_);
if (lean_obj_tag(v___x_3815_) == 0)
{
lean_object* v_a_3816_; lean_object* v_fst_3817_; 
v_a_3816_ = lean_ctor_get(v___x_3815_, 0);
lean_inc(v_a_3816_);
lean_dec_ref_known(v___x_3815_, 1);
v_fst_3817_ = lean_ctor_get(v_a_3816_, 0);
lean_inc(v_fst_3817_);
switch(lean_obj_tag(v_fst_3817_))
{
case 3:
{
lean_dec(v_a_3816_);
lean_dec_ref(v___y_3810_);
v_cases_3784_ = v___y_3813_;
goto _start;
}
case 5:
{
lean_object* v_snd_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; 
v_snd_3819_ = lean_ctor_get(v_a_3816_, 1);
lean_inc(v_snd_3819_);
lean_dec(v_a_3816_);
v___x_3820_ = lean_box(4);
v___x_3821_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
lean_inc_ref(v___y_3810_);
v___x_3822_ = lean_apply_3(v___y_3810_, v___x_3820_, v___x_3821_, v___y_3813_);
v___x_3823_ = lean_apply_3(v___y_3810_, v_fst_3817_, v_snd_3819_, v___x_3822_);
v_cases_3784_ = v___x_3823_;
goto _start;
}
default: 
{
lean_object* v_snd_3825_; lean_object* v___x_3826_; 
v_snd_3825_ = lean_ctor_get(v_a_3816_, 1);
lean_inc(v_snd_3825_);
lean_dec(v_a_3816_);
v___x_3826_ = lean_apply_3(v___y_3810_, v_fst_3817_, v_snd_3825_, v___y_3813_);
v_cases_3784_ = v___x_3826_;
goto _start;
}
}
}
else
{
lean_object* v_a_3828_; lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3835_; 
lean_dec_ref(v___y_3813_);
lean_dec_ref(v___y_3810_);
lean_dec_ref(v_result_3785_);
v_a_3828_ = lean_ctor_get(v___x_3815_, 0);
v_isSharedCheck_3835_ = !lean_is_exclusive(v___x_3815_);
if (v_isSharedCheck_3835_ == 0)
{
v___x_3830_ = v___x_3815_;
v_isShared_3831_ = v_isSharedCheck_3835_;
goto v_resetjp_3829_;
}
else
{
lean_inc(v_a_3828_);
lean_dec(v___x_3815_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3835_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
lean_object* v___x_3833_; 
if (v_isShared_3831_ == 0)
{
v___x_3833_ = v___x_3830_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3834_; 
v_reuseFailAlloc_3834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3834_, 0, v_a_3828_);
v___x_3833_ = v_reuseFailAlloc_3834_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
return v___x_3833_;
}
}
}
}
v___jp_3841_:
{
lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___f_3846_; uint8_t v___x_3847_; 
v___x_3843_ = lean_nat_sub(v___x_3840_, v___x_3796_);
v___x_3844_ = lean_array_get(v___x_3805_, v_todo_3799_, v___x_3843_);
lean_dec(v___x_3843_);
v___x_3845_ = lean_array_pop(v_todo_3799_);
lean_inc(v_score_3800_);
lean_inc_ref(v___x_3845_);
v___f_3846_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0___boxed), 7, 4);
lean_closure_set(v___f_3846_, 0, v_snd_3839_);
lean_closure_set(v___f_3846_, 1, v___x_3845_);
lean_closure_set(v___f_3846_, 2, v_score_3800_);
lean_closure_set(v___f_3846_, 3, v___x_3796_);
v___x_3847_ = lean_nat_dec_eq(v_fst_3838_, v___x_3793_);
if (v___x_3847_ == 0)
{
lean_object* v___x_3849_; 
if (v_isShared_3804_ == 0)
{
lean_ctor_set(v___x_3803_, 2, v_fst_3838_);
lean_ctor_set(v___x_3803_, 0, v___x_3845_);
v___x_3849_ = v___x_3803_;
goto v_reusejp_3848_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v___x_3845_);
lean_ctor_set(v_reuseFailAlloc_3851_, 1, v_score_3800_);
lean_ctor_set(v_reuseFailAlloc_3851_, 2, v_fst_3838_);
v___x_3849_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3848_;
}
v_reusejp_3848_:
{
lean_object* v___x_3850_; 
v___x_3850_ = lean_array_push(v_cases_3806_, v___x_3849_);
v___y_3810_ = v___f_3846_;
v___y_3811_ = v___y_3842_;
v___y_3812_ = v___x_3844_;
v___y_3813_ = v___x_3850_;
goto v___jp_3809_;
}
}
else
{
lean_dec_ref(v___x_3845_);
lean_dec(v_fst_3838_);
lean_del_object(v___x_3803_);
lean_dec(v_score_3800_);
v___y_3810_ = v___f_3846_;
v___y_3811_ = v___y_3842_;
v___y_3812_ = v___x_3844_;
v___y_3813_ = v_cases_3806_;
goto v___jp_3809_;
}
}
}
else
{
lean_object* v_a_3859_; lean_object* v___x_3861_; uint8_t v_isShared_3862_; uint8_t v_isSharedCheck_3866_; 
lean_dec_ref(v_cases_3806_);
lean_del_object(v___x_3803_);
lean_dec(v_score_3800_);
lean_dec_ref(v_todo_3799_);
lean_dec_ref(v_result_3785_);
v_a_3859_ = lean_ctor_get(v___x_3807_, 0);
v_isSharedCheck_3866_ = !lean_is_exclusive(v___x_3807_);
if (v_isSharedCheck_3866_ == 0)
{
v___x_3861_ = v___x_3807_;
v_isShared_3862_ = v_isSharedCheck_3866_;
goto v_resetjp_3860_;
}
else
{
lean_inc(v_a_3859_);
lean_dec(v___x_3807_);
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
lean_dec_ref(v_cases_3784_);
v___x_3868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3868_, 0, v_result_3785_);
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
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1(void){
_start:
{
lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; 
v___x_4112_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__0));
v___x_4113_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2);
v___x_4114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4114_, 0, v___x_4113_);
lean_ctor_set(v___x_4114_, 1, v___x_4112_);
return v___x_4114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg(){
_start:
{
lean_object* v___x_4116_; 
v___x_4116_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1);
return v___x_4116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___boxed(lean_object* v___dummy_4117_){
_start:
{
lean_object* v_res_4118_; 
v_res_4118_ = l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg();
return v_res_4118_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0(void){
_start:
{
lean_object* v___x_4119_; 
v___x_4119_ = l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg();
return v___x_4119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default(lean_object* v_00_u03b1_4120_){
_start:
{
lean_object* v___x_4121_; 
v___x_4121_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0);
return v___x_4121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___redArg(){
_start:
{
lean_object* v___x_4123_; 
v___x_4123_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0);
return v___x_4123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___redArg___boxed(lean_object* v___dummy_4124_){
_start:
{
lean_object* v_res_4125_; 
v_res_4125_ = l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___redArg();
return v_res_4125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree(lean_object* v_a_4126_){
_start:
{
lean_object* v___x_4127_; 
v___x_4127_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0);
return v___x_4127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(lean_object* v_d_4128_, lean_object* v_k_4129_, lean_object* v_f_4130_){
_start:
{
lean_object* v_roots_4131_; lean_object* v_tries_4132_; lean_object* v___x_4133_; 
v_roots_4131_ = lean_ctor_get(v_d_4128_, 0);
v_tries_4132_ = lean_ctor_get(v_d_4128_, 1);
v___x_4133_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_roots_4131_, v_k_4129_);
if (lean_obj_tag(v___x_4133_) == 0)
{
lean_object* v___x_4135_; uint8_t v_isShared_4136_; uint8_t v_isSharedCheck_4145_; 
lean_inc_ref(v_tries_4132_);
lean_inc_ref(v_roots_4131_);
v_isSharedCheck_4145_ = !lean_is_exclusive(v_d_4128_);
if (v_isSharedCheck_4145_ == 0)
{
lean_object* v_unused_4146_; lean_object* v_unused_4147_; 
v_unused_4146_ = lean_ctor_get(v_d_4128_, 1);
lean_dec(v_unused_4146_);
v_unused_4147_ = lean_ctor_get(v_d_4128_, 0);
lean_dec(v_unused_4147_);
v___x_4135_ = v_d_4128_;
v_isShared_4136_ = v_isSharedCheck_4145_;
goto v_resetjp_4134_;
}
else
{
lean_dec(v_d_4128_);
v___x_4135_ = lean_box(0);
v_isShared_4136_ = v_isSharedCheck_4145_;
goto v_resetjp_4134_;
}
v_resetjp_4134_:
{
lean_object* v___x_4137_; lean_object* v_roots_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4143_; 
v___x_4137_ = lean_array_get_size(v_tries_4132_);
v_roots_4138_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_roots_4131_, v_k_4129_, v___x_4137_);
v___x_4139_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__3));
v___x_4140_ = lean_apply_1(v_f_4130_, v___x_4139_);
v___x_4141_ = lean_array_push(v_tries_4132_, v___x_4140_);
if (v_isShared_4136_ == 0)
{
lean_ctor_set(v___x_4135_, 1, v___x_4141_);
lean_ctor_set(v___x_4135_, 0, v_roots_4138_);
v___x_4143_ = v___x_4135_;
goto v_reusejp_4142_;
}
else
{
lean_object* v_reuseFailAlloc_4144_; 
v_reuseFailAlloc_4144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4144_, 0, v_roots_4138_);
lean_ctor_set(v_reuseFailAlloc_4144_, 1, v___x_4141_);
v___x_4143_ = v_reuseFailAlloc_4144_;
goto v_reusejp_4142_;
}
v_reusejp_4142_:
{
return v___x_4143_;
}
}
}
else
{
lean_object* v_val_4148_; lean_object* v___x_4149_; uint8_t v___x_4150_; 
lean_dec(v_k_4129_);
v_val_4148_ = lean_ctor_get(v___x_4133_, 0);
lean_inc(v_val_4148_);
lean_dec_ref_known(v___x_4133_, 1);
v___x_4149_ = lean_array_get_size(v_tries_4132_);
v___x_4150_ = lean_nat_dec_lt(v_val_4148_, v___x_4149_);
if (v___x_4150_ == 0)
{
lean_dec(v_val_4148_);
lean_dec_ref(v_f_4130_);
return v_d_4128_;
}
else
{
lean_object* v___x_4152_; uint8_t v_isShared_4153_; uint8_t v_isSharedCheck_4162_; 
lean_inc_ref(v_tries_4132_);
lean_inc_ref(v_roots_4131_);
v_isSharedCheck_4162_ = !lean_is_exclusive(v_d_4128_);
if (v_isSharedCheck_4162_ == 0)
{
lean_object* v_unused_4163_; lean_object* v_unused_4164_; 
v_unused_4163_ = lean_ctor_get(v_d_4128_, 1);
lean_dec(v_unused_4163_);
v_unused_4164_ = lean_ctor_get(v_d_4128_, 0);
lean_dec(v_unused_4164_);
v___x_4152_ = v_d_4128_;
v_isShared_4153_ = v_isSharedCheck_4162_;
goto v_resetjp_4151_;
}
else
{
lean_dec(v_d_4128_);
v___x_4152_ = lean_box(0);
v_isShared_4153_ = v_isSharedCheck_4162_;
goto v_resetjp_4151_;
}
v_resetjp_4151_:
{
lean_object* v_v_4154_; lean_object* v___x_4155_; lean_object* v_xs_x27_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4160_; 
v_v_4154_ = lean_array_fget(v_tries_4132_, v_val_4148_);
v___x_4155_ = lean_box(0);
v_xs_x27_4156_ = lean_array_fset(v_tries_4132_, v_val_4148_, v___x_4155_);
v___x_4157_ = lean_apply_1(v_f_4130_, v_v_4154_);
v___x_4158_ = lean_array_fset(v_xs_x27_4156_, v_val_4148_, v___x_4157_);
lean_dec(v_val_4148_);
if (v_isShared_4153_ == 0)
{
lean_ctor_set(v___x_4152_, 1, v___x_4158_);
v___x_4160_ = v___x_4152_;
goto v_reusejp_4159_;
}
else
{
lean_object* v_reuseFailAlloc_4161_; 
v_reuseFailAlloc_4161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4161_, 0, v_roots_4131_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt(lean_object* v_00_u03b1_4165_, lean_object* v_d_4166_, lean_object* v_k_4167_, lean_object* v_f_4168_){
_start:
{
lean_object* v___x_4169_; 
v___x_4169_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(v_d_4166_, v_k_4167_, v_f_4168_);
return v___x_4169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg___lam__0(lean_object* v_e_4170_, lean_object* v_x_4171_){
_start:
{
lean_object* v___x_4172_; 
v___x_4172_ = lean_array_push(v_x_4171_, v_e_4170_);
return v___x_4172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg(lean_object* v_d_4173_, lean_object* v_k_4174_, lean_object* v_e_4175_){
_start:
{
lean_object* v___f_4176_; lean_object* v___x_4177_; 
v___f_4176_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4176_, 0, v_e_4175_);
v___x_4177_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(v_d_4173_, v_k_4174_, v___f_4176_);
return v___x_4177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push(lean_object* v_00_u03b1_4178_, lean_object* v_d_4179_, lean_object* v_k_4180_, lean_object* v_e_4181_){
_start:
{
lean_object* v___x_4182_; 
v___x_4182_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg(v_d_4179_, v_k_4180_, v_e_4181_);
return v___x_4182_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(size_t v_sz_4183_, size_t v_i_4184_, lean_object* v_bs_4185_){
_start:
{
uint8_t v___x_4186_; 
v___x_4186_ = lean_usize_dec_lt(v_i_4184_, v_sz_4183_);
if (v___x_4186_ == 0)
{
return v_bs_4185_;
}
else
{
lean_object* v_v_4187_; lean_object* v___x_4188_; lean_object* v_bs_x27_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; size_t v___x_4193_; size_t v___x_4194_; lean_object* v___x_4195_; 
v_v_4187_ = lean_array_uget(v_bs_4185_, v_i_4184_);
v___x_4188_ = lean_unsigned_to_nat(0u);
v_bs_x27_4189_ = lean_array_uset(v_bs_4185_, v_i_4184_, v___x_4188_);
v___x_4190_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__0));
v___x_4191_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2);
v___x_4192_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4192_, 0, v___x_4190_);
lean_ctor_set(v___x_4192_, 1, v___x_4188_);
lean_ctor_set(v___x_4192_, 2, v___x_4191_);
lean_ctor_set(v___x_4192_, 3, v_v_4187_);
v___x_4193_ = ((size_t)1ULL);
v___x_4194_ = lean_usize_add(v_i_4184_, v___x_4193_);
v___x_4195_ = lean_array_uset(v_bs_x27_4189_, v_i_4184_, v___x_4192_);
v_i_4184_ = v___x_4194_;
v_bs_4185_ = v___x_4195_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg___boxed(lean_object* v_sz_4197_, lean_object* v_i_4198_, lean_object* v_bs_4199_){
_start:
{
size_t v_sz_boxed_4200_; size_t v_i_boxed_4201_; lean_object* v_res_4202_; 
v_sz_boxed_4200_ = lean_unbox_usize(v_sz_4197_);
lean_dec(v_sz_4197_);
v_i_boxed_4201_ = lean_unbox_usize(v_i_4198_);
lean_dec(v_i_4198_);
v_res_4202_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(v_sz_boxed_4200_, v_i_boxed_4201_, v_bs_4199_);
return v_res_4202_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__1(lean_object* v_x_4203_, lean_object* v_x_4204_){
_start:
{
if (lean_obj_tag(v_x_4204_) == 0)
{
return v_x_4203_;
}
else
{
lean_object* v_key_4205_; lean_object* v_value_4206_; lean_object* v_tail_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; 
v_key_4205_ = lean_ctor_get(v_x_4204_, 0);
lean_inc(v_key_4205_);
v_value_4206_ = lean_ctor_get(v_x_4204_, 1);
lean_inc(v_value_4206_);
v_tail_4207_ = lean_ctor_get(v_x_4204_, 2);
lean_inc(v_tail_4207_);
lean_dec_ref_known(v_x_4204_, 3);
v___x_4208_ = lean_unsigned_to_nat(1u);
v___x_4209_ = lean_nat_add(v_value_4206_, v___x_4208_);
lean_dec(v_value_4206_);
v___x_4210_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_x_4203_, v_key_4205_, v___x_4209_);
v_x_4203_ = v___x_4210_;
v_x_4204_ = v_tail_4207_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(lean_object* v_as_4212_, size_t v_i_4213_, size_t v_stop_4214_, lean_object* v_b_4215_){
_start:
{
uint8_t v___x_4216_; 
v___x_4216_ = lean_usize_dec_eq(v_i_4213_, v_stop_4214_);
if (v___x_4216_ == 0)
{
lean_object* v___x_4217_; lean_object* v___x_4218_; size_t v___x_4219_; size_t v___x_4220_; 
v___x_4217_ = lean_array_uget_borrowed(v_as_4212_, v_i_4213_);
lean_inc(v___x_4217_);
v___x_4218_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__1(v_b_4215_, v___x_4217_);
v___x_4219_ = ((size_t)1ULL);
v___x_4220_ = lean_usize_add(v_i_4213_, v___x_4219_);
v_i_4213_ = v___x_4220_;
v_b_4215_ = v___x_4218_;
goto _start;
}
else
{
return v_b_4215_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2___boxed(lean_object* v_as_4222_, lean_object* v_i_4223_, lean_object* v_stop_4224_, lean_object* v_b_4225_){
_start:
{
size_t v_i_boxed_4226_; size_t v_stop_boxed_4227_; lean_object* v_res_4228_; 
v_i_boxed_4226_ = lean_unbox_usize(v_i_4223_);
lean_dec(v_i_4223_);
v_stop_boxed_4227_ = lean_unbox_usize(v_stop_4224_);
lean_dec(v_stop_4224_);
v_res_4228_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(v_as_4222_, v_i_boxed_4226_, v_stop_boxed_4227_, v_b_4225_);
lean_dec_ref(v_as_4222_);
return v_res_4228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(lean_object* v_d_4229_){
_start:
{
lean_object* v_roots_4230_; lean_object* v_tries_4231_; lean_object* v___x_4233_; uint8_t v_isShared_4234_; uint8_t v_isSharedCheck_4254_; 
v_roots_4230_ = lean_ctor_get(v_d_4229_, 0);
v_tries_4231_ = lean_ctor_get(v_d_4229_, 1);
v_isSharedCheck_4254_ = !lean_is_exclusive(v_d_4229_);
if (v_isSharedCheck_4254_ == 0)
{
v___x_4233_ = v_d_4229_;
v_isShared_4234_ = v_isSharedCheck_4254_;
goto v_resetjp_4232_;
}
else
{
lean_inc(v_tries_4231_);
lean_inc(v_roots_4230_);
lean_dec(v_d_4229_);
v___x_4233_ = lean_box(0);
v_isShared_4234_ = v_isSharedCheck_4254_;
goto v_resetjp_4232_;
}
v_resetjp_4232_:
{
lean_object* v___y_4236_; lean_object* v_buckets_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; uint8_t v___x_4250_; 
v_buckets_4247_ = lean_ctor_get(v_roots_4230_, 1);
v___x_4248_ = lean_unsigned_to_nat(0u);
v___x_4249_ = lean_array_get_size(v_buckets_4247_);
v___x_4250_ = lean_nat_dec_lt(v___x_4248_, v___x_4249_);
if (v___x_4250_ == 0)
{
v___y_4236_ = v_roots_4230_;
goto v___jp_4235_;
}
else
{
size_t v___x_4251_; size_t v___x_4252_; lean_object* v___x_4253_; 
lean_inc_ref(v_buckets_4247_);
v___x_4251_ = ((size_t)0ULL);
v___x_4252_ = lean_usize_of_nat(v___x_4249_);
v___x_4253_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(v_buckets_4247_, v___x_4251_, v___x_4252_, v_roots_4230_);
lean_dec_ref(v_buckets_4247_);
v___y_4236_ = v___x_4253_;
goto v___jp_4235_;
}
v___jp_4235_:
{
lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; size_t v_sz_4240_; size_t v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4245_; 
v___x_4237_ = lean_unsigned_to_nat(1u);
v___x_4238_ = lean_mk_empty_array_with_capacity(v___x_4237_);
lean_dec_ref(v___x_4238_);
v___x_4239_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__0);
v_sz_4240_ = lean_array_size(v_tries_4231_);
v___x_4241_ = ((size_t)0ULL);
v___x_4242_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(v_sz_4240_, v___x_4241_, v_tries_4231_);
v___x_4243_ = l_Array_append___redArg(v___x_4239_, v___x_4242_);
lean_dec_ref(v___x_4242_);
if (v_isShared_4234_ == 0)
{
lean_ctor_set(v___x_4233_, 1, v___y_4236_);
lean_ctor_set(v___x_4233_, 0, v___x_4243_);
v___x_4245_ = v___x_4233_;
goto v_reusejp_4244_;
}
else
{
lean_object* v_reuseFailAlloc_4246_; 
v_reuseFailAlloc_4246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4246_, 0, v___x_4243_);
lean_ctor_set(v_reuseFailAlloc_4246_, 1, v___y_4236_);
v___x_4245_ = v_reuseFailAlloc_4246_;
goto v_reusejp_4244_;
}
v_reusejp_4244_:
{
return v___x_4245_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy(lean_object* v_00_u03b1_4255_, lean_object* v_d_4256_){
_start:
{
lean_object* v___x_4257_; 
v___x_4257_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_d_4256_);
return v___x_4257_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0(lean_object* v_00_u03b1_4258_, size_t v_sz_4259_, size_t v_i_4260_, lean_object* v_bs_4261_){
_start:
{
lean_object* v___x_4262_; 
v___x_4262_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(v_sz_4259_, v_i_4260_, v_bs_4261_);
return v___x_4262_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___boxed(lean_object* v_00_u03b1_4263_, lean_object* v_sz_4264_, lean_object* v_i_4265_, lean_object* v_bs_4266_){
_start:
{
size_t v_sz_boxed_4267_; size_t v_i_boxed_4268_; lean_object* v_res_4269_; 
v_sz_boxed_4267_ = lean_unbox_usize(v_sz_4264_);
lean_dec(v_sz_4264_);
v_i_boxed_4268_ = lean_unbox_usize(v_i_4265_);
lean_dec(v_i_4265_);
v_res_4269_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0(v_00_u03b1_4263_, v_sz_boxed_4267_, v_i_boxed_4268_, v_bs_4266_);
return v_res_4269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___lam__0(lean_object* v_y_4270_, lean_object* v_x_4271_){
_start:
{
lean_object* v___x_4272_; 
v___x_4272_ = l_Array_append___redArg(v_x_4271_, v_y_4270_);
return v___x_4272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___lam__0___boxed(lean_object* v_y_4273_, lean_object* v_x_4274_){
_start:
{
lean_object* v_res_4275_; 
v_res_4275_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___lam__0(v_y_4273_, v_x_4274_);
lean_dec_ref(v_y_4273_);
return v_res_4275_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4276_; 
v___x_4276_ = l_Array_instInhabited___redArg();
return v___x_4276_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(lean_object* v_tries_4277_, lean_object* v_snd_4278_, lean_object* v_x_4279_, lean_object* v_x_4280_){
_start:
{
if (lean_obj_tag(v_x_4280_) == 0)
{
lean_dec_ref(v_snd_4278_);
return v_x_4279_;
}
else
{
lean_object* v_key_4281_; lean_object* v_value_4282_; lean_object* v_tail_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; 
v_key_4281_ = lean_ctor_get(v_x_4280_, 0);
lean_inc(v_key_4281_);
v_value_4282_ = lean_ctor_get(v_x_4280_, 1);
lean_inc(v_value_4282_);
v_tail_4283_ = lean_ctor_get(v_x_4280_, 2);
lean_inc(v_tail_4283_);
lean_dec_ref_known(v_x_4280_, 3);
v___x_4284_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0);
v___x_4285_ = lean_array_get_borrowed(v___x_4284_, v_tries_4277_, v_value_4282_);
lean_dec(v_value_4282_);
lean_inc_ref(v_snd_4278_);
lean_inc(v___x_4285_);
v___x_4286_ = lean_apply_1(v_snd_4278_, v___x_4285_);
v___x_4287_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(v_x_4279_, v_key_4281_, v___x_4286_);
v_x_4279_ = v___x_4287_;
v_x_4280_ = v_tail_4283_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___boxed(lean_object* v_tries_4289_, lean_object* v_snd_4290_, lean_object* v_x_4291_, lean_object* v_x_4292_){
_start:
{
lean_object* v_res_4293_; 
v_res_4293_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(v_tries_4289_, v_snd_4290_, v_x_4291_, v_x_4292_);
lean_dec_ref(v_tries_4289_);
return v_res_4293_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(lean_object* v_tries_4294_, lean_object* v_snd_4295_, lean_object* v_as_4296_, size_t v_i_4297_, size_t v_stop_4298_, lean_object* v_b_4299_){
_start:
{
uint8_t v___x_4300_; 
v___x_4300_ = lean_usize_dec_eq(v_i_4297_, v_stop_4298_);
if (v___x_4300_ == 0)
{
lean_object* v___x_4301_; lean_object* v___x_4302_; size_t v___x_4303_; size_t v___x_4304_; 
v___x_4301_ = lean_array_uget_borrowed(v_as_4296_, v_i_4297_);
lean_inc(v___x_4301_);
lean_inc_ref(v_snd_4295_);
v___x_4302_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(v_tries_4294_, v_snd_4295_, v_b_4299_, v___x_4301_);
v___x_4303_ = ((size_t)1ULL);
v___x_4304_ = lean_usize_add(v_i_4297_, v___x_4303_);
v_i_4297_ = v___x_4304_;
v_b_4299_ = v___x_4302_;
goto _start;
}
else
{
lean_dec_ref(v_snd_4295_);
return v_b_4299_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg___boxed(lean_object* v_tries_4306_, lean_object* v_snd_4307_, lean_object* v_as_4308_, lean_object* v_i_4309_, lean_object* v_stop_4310_, lean_object* v_b_4311_){
_start:
{
size_t v_i_boxed_4312_; size_t v_stop_boxed_4313_; lean_object* v_res_4314_; 
v_i_boxed_4312_ = lean_unbox_usize(v_i_4309_);
lean_dec(v_i_4309_);
v_stop_boxed_4313_ = lean_unbox_usize(v_stop_4310_);
lean_dec(v_stop_4310_);
v_res_4314_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(v_tries_4306_, v_snd_4307_, v_as_4308_, v_i_boxed_4312_, v_stop_boxed_4313_, v_b_4311_);
lean_dec_ref(v_as_4308_);
lean_dec_ref(v_tries_4306_);
return v_res_4314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg(lean_object* v_x_4317_, lean_object* v_y_4318_){
_start:
{
lean_object* v_fst_4320_; lean_object* v_buckets_4321_; lean_object* v_tries_4322_; lean_object* v_snd_4323_; lean_object* v_roots_4330_; lean_object* v_roots_4331_; lean_object* v_tries_4332_; lean_object* v_size_4333_; lean_object* v_buckets_4334_; lean_object* v_tries_4335_; lean_object* v_size_4336_; lean_object* v_buckets_4337_; uint8_t v___x_4338_; 
v_roots_4330_ = lean_ctor_get(v_y_4318_, 0);
v_roots_4331_ = lean_ctor_get(v_x_4317_, 0);
v_tries_4332_ = lean_ctor_get(v_y_4318_, 1);
v_size_4333_ = lean_ctor_get(v_roots_4330_, 0);
v_buckets_4334_ = lean_ctor_get(v_roots_4330_, 1);
v_tries_4335_ = lean_ctor_get(v_x_4317_, 1);
v_size_4336_ = lean_ctor_get(v_roots_4331_, 0);
v_buckets_4337_ = lean_ctor_get(v_roots_4331_, 1);
v___x_4338_ = lean_nat_dec_le(v_size_4333_, v_size_4336_);
if (v___x_4338_ == 0)
{
lean_object* v___f_4339_; 
lean_inc_ref(v_buckets_4337_);
lean_inc_ref(v_tries_4335_);
lean_dec_ref(v_x_4317_);
v___f_4339_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___closed__0));
v_fst_4320_ = v_y_4318_;
v_buckets_4321_ = v_buckets_4337_;
v_tries_4322_ = v_tries_4335_;
v_snd_4323_ = v___f_4339_;
goto v___jp_4319_;
}
else
{
lean_object* v___f_4340_; 
lean_inc_ref(v_buckets_4334_);
lean_inc_ref(v_tries_4332_);
lean_dec_ref(v_y_4318_);
v___f_4340_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___closed__1));
v_fst_4320_ = v_x_4317_;
v_buckets_4321_ = v_buckets_4334_;
v_tries_4322_ = v_tries_4332_;
v_snd_4323_ = v___f_4340_;
goto v___jp_4319_;
}
v___jp_4319_:
{
lean_object* v___x_4324_; lean_object* v___x_4325_; uint8_t v___x_4326_; 
v___x_4324_ = lean_unsigned_to_nat(0u);
v___x_4325_ = lean_array_get_size(v_buckets_4321_);
v___x_4326_ = lean_nat_dec_lt(v___x_4324_, v___x_4325_);
if (v___x_4326_ == 0)
{
lean_dec_ref(v_tries_4322_);
lean_dec_ref(v_buckets_4321_);
return v_fst_4320_;
}
else
{
size_t v___x_4327_; size_t v___x_4328_; lean_object* v___x_4329_; 
v___x_4327_ = ((size_t)0ULL);
v___x_4328_ = lean_usize_of_nat(v___x_4325_);
lean_inc_ref(v_snd_4323_);
v___x_4329_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(v_tries_4322_, v_snd_4323_, v_buckets_4321_, v___x_4327_, v___x_4328_, v_fst_4320_);
lean_dec_ref(v_buckets_4321_);
lean_dec_ref(v_tries_4322_);
return v___x_4329_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append(lean_object* v_00_u03b1_4341_, lean_object* v_x_4342_, lean_object* v_y_4343_){
_start:
{
lean_object* v___x_4344_; 
v___x_4344_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg(v_x_4342_, v_y_4343_);
return v___x_4344_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0(lean_object* v_00_u03b1_4345_, lean_object* v_tries_4346_, lean_object* v_snd_4347_, lean_object* v_x_4348_, lean_object* v_x_4349_){
_start:
{
lean_object* v___x_4350_; 
v___x_4350_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(v_tries_4346_, v_snd_4347_, v_x_4348_, v_x_4349_);
return v___x_4350_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___boxed(lean_object* v_00_u03b1_4351_, lean_object* v_tries_4352_, lean_object* v_snd_4353_, lean_object* v_x_4354_, lean_object* v_x_4355_){
_start:
{
lean_object* v_res_4356_; 
v_res_4356_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0(v_00_u03b1_4351_, v_tries_4352_, v_snd_4353_, v_x_4354_, v_x_4355_);
lean_dec_ref(v_tries_4352_);
return v_res_4356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1(lean_object* v_00_u03b1_4357_, lean_object* v_tries_4358_, lean_object* v_snd_4359_, lean_object* v_as_4360_, size_t v_i_4361_, size_t v_stop_4362_, lean_object* v_b_4363_){
_start:
{
lean_object* v___x_4364_; 
v___x_4364_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(v_tries_4358_, v_snd_4359_, v_as_4360_, v_i_4361_, v_stop_4362_, v_b_4363_);
return v___x_4364_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___boxed(lean_object* v_00_u03b1_4365_, lean_object* v_tries_4366_, lean_object* v_snd_4367_, lean_object* v_as_4368_, lean_object* v_i_4369_, lean_object* v_stop_4370_, lean_object* v_b_4371_){
_start:
{
size_t v_i_boxed_4372_; size_t v_stop_boxed_4373_; lean_object* v_res_4374_; 
v_i_boxed_4372_ = lean_unbox_usize(v_i_4369_);
lean_dec(v_i_4369_);
v_stop_boxed_4373_ = lean_unbox_usize(v_stop_4370_);
lean_dec(v_stop_4370_);
v_res_4374_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1(v_00_u03b1_4365_, v_tries_4366_, v_snd_4367_, v_as_4368_, v_i_boxed_4372_, v_stop_boxed_4373_, v_b_4371_);
lean_dec_ref(v_as_4368_);
lean_dec_ref(v_tries_4366_);
return v_res_4374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend___redArg(){
_start:
{
lean_object* v___x_4377_; 
v___x_4377_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend___redArg___closed__0));
return v___x_4377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend___redArg___boxed(lean_object* v___dummy_4378_){
_start:
{
lean_object* v_res_4379_; 
v_res_4379_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend___redArg();
return v_res_4379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend(lean_object* v_00_u03b1_4380_){
_start:
{
lean_object* v___x_4381_; 
v___x_4381_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend___redArg___closed__0));
return v___x_4381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(lean_object* v_expr_4382_, lean_object* v_value_4383_, lean_object* v_a_4384_, lean_object* v_a_4385_, lean_object* v_a_4386_, lean_object* v_a_4387_){
_start:
{
lean_object* v_lctx_4389_; lean_object* v_localInstances_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; 
v_lctx_4389_ = lean_ctor_get(v_a_4384_, 2);
v_localInstances_4390_ = lean_ctor_get(v_a_4384_, 3);
lean_inc_ref(v_localInstances_4390_);
lean_inc_ref(v_lctx_4389_);
v___x_4391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4391_, 0, v_lctx_4389_);
lean_ctor_set(v___x_4391_, 1, v_localInstances_4390_);
v___x_4392_ = l_Lean_Meta_LazyDiscrTree_rootKey(v_expr_4382_, v_a_4384_, v_a_4385_, v_a_4386_, v_a_4387_);
if (lean_obj_tag(v___x_4392_) == 0)
{
lean_object* v_a_4393_; lean_object* v___x_4395_; uint8_t v_isShared_4396_; uint8_t v_isSharedCheck_4411_; 
v_a_4393_ = lean_ctor_get(v___x_4392_, 0);
v_isSharedCheck_4411_ = !lean_is_exclusive(v___x_4392_);
if (v_isSharedCheck_4411_ == 0)
{
v___x_4395_ = v___x_4392_;
v_isShared_4396_ = v_isSharedCheck_4411_;
goto v_resetjp_4394_;
}
else
{
lean_inc(v_a_4393_);
lean_dec(v___x_4392_);
v___x_4395_ = lean_box(0);
v_isShared_4396_ = v_isSharedCheck_4411_;
goto v_resetjp_4394_;
}
v_resetjp_4394_:
{
lean_object* v_fst_4397_; lean_object* v_snd_4398_; lean_object* v___x_4400_; uint8_t v_isShared_4401_; uint8_t v_isSharedCheck_4410_; 
v_fst_4397_ = lean_ctor_get(v_a_4393_, 0);
v_snd_4398_ = lean_ctor_get(v_a_4393_, 1);
v_isSharedCheck_4410_ = !lean_is_exclusive(v_a_4393_);
if (v_isSharedCheck_4410_ == 0)
{
v___x_4400_ = v_a_4393_;
v_isShared_4401_ = v_isSharedCheck_4410_;
goto v_resetjp_4399_;
}
else
{
lean_inc(v_snd_4398_);
lean_inc(v_fst_4397_);
lean_dec(v_a_4393_);
v___x_4400_ = lean_box(0);
v_isShared_4401_ = v_isSharedCheck_4410_;
goto v_resetjp_4399_;
}
v_resetjp_4399_:
{
lean_object* v___x_4403_; 
if (v_isShared_4401_ == 0)
{
lean_ctor_set(v___x_4400_, 1, v_value_4383_);
lean_ctor_set(v___x_4400_, 0, v___x_4391_);
v___x_4403_ = v___x_4400_;
goto v_reusejp_4402_;
}
else
{
lean_object* v_reuseFailAlloc_4409_; 
v_reuseFailAlloc_4409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4409_, 0, v___x_4391_);
lean_ctor_set(v_reuseFailAlloc_4409_, 1, v_value_4383_);
v___x_4403_ = v_reuseFailAlloc_4409_;
goto v_reusejp_4402_;
}
v_reusejp_4402_:
{
lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4407_; 
v___x_4404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4404_, 0, v_snd_4398_);
lean_ctor_set(v___x_4404_, 1, v___x_4403_);
v___x_4405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4405_, 0, v_fst_4397_);
lean_ctor_set(v___x_4405_, 1, v___x_4404_);
if (v_isShared_4396_ == 0)
{
lean_ctor_set(v___x_4395_, 0, v___x_4405_);
v___x_4407_ = v___x_4395_;
goto v_reusejp_4406_;
}
else
{
lean_object* v_reuseFailAlloc_4408_; 
v_reuseFailAlloc_4408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4408_, 0, v___x_4405_);
v___x_4407_ = v_reuseFailAlloc_4408_;
goto v_reusejp_4406_;
}
v_reusejp_4406_:
{
return v___x_4407_;
}
}
}
}
}
else
{
lean_object* v_a_4412_; lean_object* v___x_4414_; uint8_t v_isShared_4415_; uint8_t v_isSharedCheck_4419_; 
lean_dec_ref_known(v___x_4391_, 2);
lean_dec(v_value_4383_);
v_a_4412_ = lean_ctor_get(v___x_4392_, 0);
v_isSharedCheck_4419_ = !lean_is_exclusive(v___x_4392_);
if (v_isSharedCheck_4419_ == 0)
{
v___x_4414_ = v___x_4392_;
v_isShared_4415_ = v_isSharedCheck_4419_;
goto v_resetjp_4413_;
}
else
{
lean_inc(v_a_4412_);
lean_dec(v___x_4392_);
v___x_4414_ = lean_box(0);
v_isShared_4415_ = v_isSharedCheck_4419_;
goto v_resetjp_4413_;
}
v_resetjp_4413_:
{
lean_object* v___x_4417_; 
if (v_isShared_4415_ == 0)
{
v___x_4417_ = v___x_4414_;
goto v_reusejp_4416_;
}
else
{
lean_object* v_reuseFailAlloc_4418_; 
v_reuseFailAlloc_4418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4418_, 0, v_a_4412_);
v___x_4417_ = v_reuseFailAlloc_4418_;
goto v_reusejp_4416_;
}
v_reusejp_4416_:
{
return v___x_4417_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg___boxed(lean_object* v_expr_4420_, lean_object* v_value_4421_, lean_object* v_a_4422_, lean_object* v_a_4423_, lean_object* v_a_4424_, lean_object* v_a_4425_, lean_object* v_a_4426_){
_start:
{
lean_object* v_res_4427_; 
v_res_4427_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(v_expr_4420_, v_value_4421_, v_a_4422_, v_a_4423_, v_a_4424_, v_a_4425_);
lean_dec(v_a_4425_);
lean_dec_ref(v_a_4424_);
lean_dec(v_a_4423_);
lean_dec_ref(v_a_4422_);
return v_res_4427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr(lean_object* v_00_u03b1_4428_, lean_object* v_expr_4429_, lean_object* v_value_4430_, lean_object* v_a_4431_, lean_object* v_a_4432_, lean_object* v_a_4433_, lean_object* v_a_4434_){
_start:
{
lean_object* v___x_4436_; 
v___x_4436_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(v_expr_4429_, v_value_4430_, v_a_4431_, v_a_4432_, v_a_4433_, v_a_4434_);
return v___x_4436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___boxed(lean_object* v_00_u03b1_4437_, lean_object* v_expr_4438_, lean_object* v_value_4439_, lean_object* v_a_4440_, lean_object* v_a_4441_, lean_object* v_a_4442_, lean_object* v_a_4443_, lean_object* v_a_4444_){
_start:
{
lean_object* v_res_4445_; 
v_res_4445_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr(v_00_u03b1_4437_, v_expr_4438_, v_value_4439_, v_a_4440_, v_a_4441_, v_a_4442_, v_a_4443_);
lean_dec(v_a_4443_);
lean_dec_ref(v_a_4442_);
lean_dec(v_a_4441_);
lean_dec_ref(v_a_4440_);
return v_res_4445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(lean_object* v_e_4446_, lean_object* v_idx_4447_, lean_object* v_value_4448_, lean_object* v_a_4449_, lean_object* v_a_4450_, lean_object* v_a_4451_, lean_object* v_a_4452_){
_start:
{
lean_object* v_entry_4454_; lean_object* v___x_4456_; uint8_t v_isShared_4457_; uint8_t v_isSharedCheck_4500_; 
v_entry_4454_ = lean_ctor_get(v_e_4446_, 1);
v_isSharedCheck_4500_ = !lean_is_exclusive(v_e_4446_);
if (v_isSharedCheck_4500_ == 0)
{
lean_object* v_unused_4501_; 
v_unused_4501_ = lean_ctor_get(v_e_4446_, 0);
lean_dec(v_unused_4501_);
v___x_4456_ = v_e_4446_;
v_isShared_4457_ = v_isSharedCheck_4500_;
goto v_resetjp_4455_;
}
else
{
lean_inc(v_entry_4454_);
lean_dec(v_e_4446_);
v___x_4456_ = lean_box(0);
v_isShared_4457_ = v_isSharedCheck_4500_;
goto v_resetjp_4455_;
}
v_resetjp_4455_:
{
lean_object* v_snd_4458_; lean_object* v_fst_4459_; lean_object* v_fst_4460_; lean_object* v___x_4462_; uint8_t v_isShared_4463_; uint8_t v_isSharedCheck_4498_; 
v_snd_4458_ = lean_ctor_get(v_entry_4454_, 1);
lean_inc(v_snd_4458_);
v_fst_4459_ = lean_ctor_get(v_entry_4454_, 0);
lean_inc(v_fst_4459_);
lean_dec_ref(v_entry_4454_);
v_fst_4460_ = lean_ctor_get(v_snd_4458_, 0);
v_isSharedCheck_4498_ = !lean_is_exclusive(v_snd_4458_);
if (v_isSharedCheck_4498_ == 0)
{
lean_object* v_unused_4499_; 
v_unused_4499_ = lean_ctor_get(v_snd_4458_, 1);
lean_dec(v_unused_4499_);
v___x_4462_ = v_snd_4458_;
v_isShared_4463_ = v_isSharedCheck_4498_;
goto v_resetjp_4461_;
}
else
{
lean_inc(v_fst_4460_);
lean_dec(v_snd_4458_);
v___x_4462_ = lean_box(0);
v_isShared_4463_ = v_isSharedCheck_4498_;
goto v_resetjp_4461_;
}
v_resetjp_4461_:
{
lean_object* v___x_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; 
v___x_4464_ = l_Lean_instInhabitedExpr;
v___x_4465_ = lean_array_get(v___x_4464_, v_fst_4459_, v_idx_4447_);
lean_dec(v_fst_4459_);
v___x_4466_ = l_Lean_Meta_LazyDiscrTree_rootKey(v___x_4465_, v_a_4449_, v_a_4450_, v_a_4451_, v_a_4452_);
if (lean_obj_tag(v___x_4466_) == 0)
{
lean_object* v_a_4467_; lean_object* v___x_4469_; uint8_t v_isShared_4470_; uint8_t v_isSharedCheck_4489_; 
v_a_4467_ = lean_ctor_get(v___x_4466_, 0);
v_isSharedCheck_4489_ = !lean_is_exclusive(v___x_4466_);
if (v_isSharedCheck_4489_ == 0)
{
v___x_4469_ = v___x_4466_;
v_isShared_4470_ = v_isSharedCheck_4489_;
goto v_resetjp_4468_;
}
else
{
lean_inc(v_a_4467_);
lean_dec(v___x_4466_);
v___x_4469_ = lean_box(0);
v_isShared_4470_ = v_isSharedCheck_4489_;
goto v_resetjp_4468_;
}
v_resetjp_4468_:
{
lean_object* v_fst_4471_; lean_object* v_snd_4472_; lean_object* v___x_4474_; uint8_t v_isShared_4475_; uint8_t v_isSharedCheck_4488_; 
v_fst_4471_ = lean_ctor_get(v_a_4467_, 0);
v_snd_4472_ = lean_ctor_get(v_a_4467_, 1);
v_isSharedCheck_4488_ = !lean_is_exclusive(v_a_4467_);
if (v_isSharedCheck_4488_ == 0)
{
v___x_4474_ = v_a_4467_;
v_isShared_4475_ = v_isSharedCheck_4488_;
goto v_resetjp_4473_;
}
else
{
lean_inc(v_snd_4472_);
lean_inc(v_fst_4471_);
lean_dec(v_a_4467_);
v___x_4474_ = lean_box(0);
v_isShared_4475_ = v_isSharedCheck_4488_;
goto v_resetjp_4473_;
}
v_resetjp_4473_:
{
lean_object* v___x_4477_; 
if (v_isShared_4475_ == 0)
{
lean_ctor_set(v___x_4474_, 1, v_value_4448_);
lean_ctor_set(v___x_4474_, 0, v_fst_4460_);
v___x_4477_ = v___x_4474_;
goto v_reusejp_4476_;
}
else
{
lean_object* v_reuseFailAlloc_4487_; 
v_reuseFailAlloc_4487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4487_, 0, v_fst_4460_);
lean_ctor_set(v_reuseFailAlloc_4487_, 1, v_value_4448_);
v___x_4477_ = v_reuseFailAlloc_4487_;
goto v_reusejp_4476_;
}
v_reusejp_4476_:
{
lean_object* v___x_4479_; 
if (v_isShared_4463_ == 0)
{
lean_ctor_set(v___x_4462_, 1, v___x_4477_);
lean_ctor_set(v___x_4462_, 0, v_snd_4472_);
v___x_4479_ = v___x_4462_;
goto v_reusejp_4478_;
}
else
{
lean_object* v_reuseFailAlloc_4486_; 
v_reuseFailAlloc_4486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4486_, 0, v_snd_4472_);
lean_ctor_set(v_reuseFailAlloc_4486_, 1, v___x_4477_);
v___x_4479_ = v_reuseFailAlloc_4486_;
goto v_reusejp_4478_;
}
v_reusejp_4478_:
{
lean_object* v___x_4481_; 
if (v_isShared_4457_ == 0)
{
lean_ctor_set(v___x_4456_, 1, v___x_4479_);
lean_ctor_set(v___x_4456_, 0, v_fst_4471_);
v___x_4481_ = v___x_4456_;
goto v_reusejp_4480_;
}
else
{
lean_object* v_reuseFailAlloc_4485_; 
v_reuseFailAlloc_4485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4485_, 0, v_fst_4471_);
lean_ctor_set(v_reuseFailAlloc_4485_, 1, v___x_4479_);
v___x_4481_ = v_reuseFailAlloc_4485_;
goto v_reusejp_4480_;
}
v_reusejp_4480_:
{
lean_object* v___x_4483_; 
if (v_isShared_4470_ == 0)
{
lean_ctor_set(v___x_4469_, 0, v___x_4481_);
v___x_4483_ = v___x_4469_;
goto v_reusejp_4482_;
}
else
{
lean_object* v_reuseFailAlloc_4484_; 
v_reuseFailAlloc_4484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4484_, 0, v___x_4481_);
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
else
{
lean_object* v_a_4490_; lean_object* v___x_4492_; uint8_t v_isShared_4493_; uint8_t v_isSharedCheck_4497_; 
lean_del_object(v___x_4462_);
lean_dec(v_fst_4460_);
lean_del_object(v___x_4456_);
lean_dec(v_value_4448_);
v_a_4490_ = lean_ctor_get(v___x_4466_, 0);
v_isSharedCheck_4497_ = !lean_is_exclusive(v___x_4466_);
if (v_isSharedCheck_4497_ == 0)
{
v___x_4492_ = v___x_4466_;
v_isShared_4493_ = v_isSharedCheck_4497_;
goto v_resetjp_4491_;
}
else
{
lean_inc(v_a_4490_);
lean_dec(v___x_4466_);
v___x_4492_ = lean_box(0);
v_isShared_4493_ = v_isSharedCheck_4497_;
goto v_resetjp_4491_;
}
v_resetjp_4491_:
{
lean_object* v___x_4495_; 
if (v_isShared_4493_ == 0)
{
v___x_4495_ = v___x_4492_;
goto v_reusejp_4494_;
}
else
{
lean_object* v_reuseFailAlloc_4496_; 
v_reuseFailAlloc_4496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4496_, 0, v_a_4490_);
v___x_4495_ = v_reuseFailAlloc_4496_;
goto v_reusejp_4494_;
}
v_reusejp_4494_:
{
return v___x_4495_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg___boxed(lean_object* v_e_4502_, lean_object* v_idx_4503_, lean_object* v_value_4504_, lean_object* v_a_4505_, lean_object* v_a_4506_, lean_object* v_a_4507_, lean_object* v_a_4508_, lean_object* v_a_4509_){
_start:
{
lean_object* v_res_4510_; 
v_res_4510_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(v_e_4502_, v_idx_4503_, v_value_4504_, v_a_4505_, v_a_4506_, v_a_4507_, v_a_4508_);
lean_dec(v_a_4508_);
lean_dec_ref(v_a_4507_);
lean_dec(v_a_4506_);
lean_dec_ref(v_a_4505_);
lean_dec(v_idx_4503_);
return v_res_4510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry(lean_object* v_00_u03b1_4511_, lean_object* v_e_4512_, lean_object* v_idx_4513_, lean_object* v_value_4514_, lean_object* v_a_4515_, lean_object* v_a_4516_, lean_object* v_a_4517_, lean_object* v_a_4518_){
_start:
{
lean_object* v___x_4520_; 
v___x_4520_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(v_e_4512_, v_idx_4513_, v_value_4514_, v_a_4515_, v_a_4516_, v_a_4517_, v_a_4518_);
return v___x_4520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___boxed(lean_object* v_00_u03b1_4521_, lean_object* v_e_4522_, lean_object* v_idx_4523_, lean_object* v_value_4524_, lean_object* v_a_4525_, lean_object* v_a_4526_, lean_object* v_a_4527_, lean_object* v_a_4528_, lean_object* v_a_4529_){
_start:
{
lean_object* v_res_4530_; 
v_res_4530_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry(v_00_u03b1_4521_, v_e_4522_, v_idx_4523_, v_value_4524_, v_a_4525_, v_a_4526_, v_a_4527_, v_a_4528_);
lean_dec(v_a_4528_);
lean_dec_ref(v_a_4527_);
lean_dec(v_a_4526_);
lean_dec_ref(v_a_4525_);
lean_dec(v_idx_4523_);
return v_res_4530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_ImportData_new(){
_start:
{
lean_object* v___x_4534_; lean_object* v___x_4535_; 
v___x_4534_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_ImportData_new___closed__0));
v___x_4535_ = lean_st_mk_ref(v___x_4534_);
return v___x_4535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_ImportData_new___boxed(lean_object* v_a_4536_){
_start:
{
lean_object* v_res_4537_; 
v_res_4537_ = l_Lean_Meta_LazyDiscrTree_ImportData_new();
return v_res_4537_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4538_; 
v___x_4538_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_4538_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_4539_; lean_object* v___x_4540_; 
v___x_4539_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0_spec__0___redArg___closed__0);
v___x_4540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4540_, 0, v___x_4539_);
return v___x_4540_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0_spec__0___redArg(){
_start:
{
lean_object* v___x_4542_; 
v___x_4542_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0_spec__0___redArg___closed__1);
return v___x_4542_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0_spec__0___redArg___boxed(lean_object* v___dummy_4543_){
_start:
{
lean_object* v_res_4544_; 
v_res_4544_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0_spec__0___redArg();
return v_res_4544_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0(void){
_start:
{
lean_object* v___x_4545_; lean_object* v___x_4546_; 
v___x_4545_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0_spec__0___redArg___closed__0);
v___x_4546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4546_, 0, v___x_4545_);
return v___x_4546_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1(void){
_start:
{
lean_object* v___x_4547_; lean_object* v___x_4548_; 
v___x_4547_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0);
v___x_4548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4548_, 0, v___x_4547_);
lean_ctor_set(v___x_4548_, 1, v___x_4547_);
return v___x_4548_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2(void){
_start:
{
lean_object* v___x_4549_; 
v___x_4549_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0_spec__0___redArg();
return v___x_4549_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3(void){
_start:
{
lean_object* v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; 
v___x_4550_ = lean_unsigned_to_nat(0u);
v___x_4551_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0);
v___x_4552_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4552_, 0, v___x_4551_);
lean_ctor_set(v___x_4552_, 1, v___x_4551_);
lean_ctor_set(v___x_4552_, 2, v___x_4550_);
return v___x_4552_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__4(void){
_start:
{
lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; 
v___x_4553_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3);
v___x_4554_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0);
v___x_4555_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2);
v___x_4556_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_4556_, 0, v___x_4555_);
lean_ctor_set(v___x_4556_, 1, v___x_4554_);
lean_ctor_set(v___x_4556_, 2, v___x_4554_);
lean_ctor_set(v___x_4556_, 3, v___x_4554_);
lean_ctor_set(v___x_4556_, 4, v___x_4554_);
lean_ctor_set(v___x_4556_, 5, v___x_4554_);
lean_ctor_set(v___x_4556_, 6, v___x_4554_);
lean_ctor_set(v___x_4556_, 7, v___x_4553_);
return v___x_4556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Cache_empty(lean_object* v_ngen_4557_){
_start:
{
lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; 
v___x_4558_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1);
v___x_4559_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__4, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__4);
v___x_4560_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4560_, 0, v_ngen_4557_);
lean_ctor_set(v___x_4560_, 1, v___x_4558_);
lean_ctor_set(v___x_4560_, 2, v___x_4559_);
return v___x_4560_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0_spec__0(lean_object* v_00_u03b2_4561_){
_start:
{
lean_object* v___x_4562_; 
v___x_4562_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2);
return v___x_4562_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0___redArg(){
_start:
{
lean_object* v___x_4564_; 
v___x_4564_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2);
return v___x_4564_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0___redArg___boxed(lean_object* v___dummy_4565_){
_start:
{
lean_object* v_res_4566_; 
v_res_4566_ = l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0___redArg();
return v_res_4566_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0(lean_object* v_00_u03b2_4567_){
_start:
{
lean_object* v___x_4568_; 
v___x_4568_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2);
return v___x_4568_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName(lean_object* v_env_4569_, lean_object* v_declName_4570_){
_start:
{
uint8_t v___x_4571_; 
v___x_4571_ = l_Lean_isPrivateName(v_declName_4570_);
if (v___x_4571_ == 0)
{
return v___x_4571_;
}
else
{
lean_object* v___x_4572_; 
v___x_4572_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4569_, v_declName_4570_);
if (lean_obj_tag(v___x_4572_) == 0)
{
return v___x_4571_;
}
else
{
lean_object* v_val_4573_; lean_object* v___x_4574_; uint8_t v_isModule_4575_; lean_object* v_modules_4576_; uint8_t v___x_4577_; 
v_val_4573_ = lean_ctor_get(v___x_4572_, 0);
lean_inc(v_val_4573_);
lean_dec_ref_known(v___x_4572_, 1);
v___x_4574_ = l_Lean_Environment_header(v_env_4569_);
v_isModule_4575_ = lean_ctor_get_uint8(v___x_4574_, sizeof(void*)*8 + 4);
v_modules_4576_ = lean_ctor_get(v___x_4574_, 3);
lean_inc_ref(v_modules_4576_);
lean_dec_ref(v___x_4574_);
v___x_4577_ = 0;
if (v_isModule_4575_ == 0)
{
lean_dec_ref(v_modules_4576_);
lean_dec(v_val_4573_);
return v___x_4577_;
}
else
{
lean_object* v___x_4578_; uint8_t v___x_4579_; 
v___x_4578_ = lean_array_get_size(v_modules_4576_);
v___x_4579_ = lean_nat_dec_lt(v_val_4573_, v___x_4578_);
if (v___x_4579_ == 0)
{
lean_dec_ref(v_modules_4576_);
lean_dec(v_val_4573_);
return v___x_4577_;
}
else
{
lean_object* v___x_4580_; lean_object* v_toImport_4581_; uint8_t v_importAll_4582_; 
v___x_4580_ = lean_array_fget(v_modules_4576_, v_val_4573_);
lean_dec(v_val_4573_);
lean_dec_ref(v_modules_4576_);
v_toImport_4581_ = lean_ctor_get(v___x_4580_, 0);
lean_inc_ref(v_toImport_4581_);
lean_dec(v___x_4580_);
v_importAll_4582_ = lean_ctor_get_uint8(v_toImport_4581_, sizeof(void*)*1);
lean_dec_ref(v_toImport_4581_);
return v_importAll_4582_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName___boxed(lean_object* v_env_4583_, lean_object* v_declName_4584_){
_start:
{
uint8_t v_res_4585_; lean_object* v_r_4586_; 
v_res_4585_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName(v_env_4583_, v_declName_4584_);
lean_dec(v_declName_4584_);
lean_dec_ref(v_env_4583_);
v_r_4586_ = lean_box(v_res_4585_);
return v_r_4586_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_LazyDiscrTree_blacklistInsertion(lean_object* v_env_4592_, lean_object* v_declName_4593_){
_start:
{
uint8_t v___x_4594_; 
lean_inc(v_declName_4593_);
lean_inc_ref(v_env_4592_);
v___x_4594_ = l_Lean_Meta_allowCompletion(v_env_4592_, v_declName_4593_);
if (v___x_4594_ == 0)
{
uint8_t v___x_4595_; 
lean_dec(v_declName_4593_);
lean_dec_ref(v_env_4592_);
v___x_4595_ = 1;
return v___x_4595_;
}
else
{
lean_object* v___x_4596_; uint8_t v___x_4597_; 
v___x_4596_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__1));
v___x_4597_ = lean_name_eq(v_declName_4593_, v___x_4596_);
if (v___x_4597_ == 0)
{
uint8_t v___x_4606_; 
lean_inc(v_declName_4593_);
v___x_4606_ = l_Lean_Name_isInternalDetail(v_declName_4593_);
if (v___x_4606_ == 0)
{
lean_dec_ref(v_env_4592_);
goto v___jp_4602_;
}
else
{
uint8_t v___x_4607_; 
v___x_4607_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName(v_env_4592_, v_declName_4593_);
lean_dec_ref(v_env_4592_);
if (v___x_4607_ == 0)
{
lean_dec(v_declName_4593_);
return v___x_4606_;
}
else
{
goto v___jp_4602_;
}
}
}
else
{
lean_dec(v_declName_4593_);
lean_dec_ref(v_env_4592_);
return v___x_4597_;
}
v___jp_4598_:
{
if (lean_obj_tag(v_declName_4593_) == 1)
{
lean_object* v_str_4599_; lean_object* v___x_4600_; uint8_t v___x_4601_; 
v_str_4599_ = lean_ctor_get(v_declName_4593_, 1);
lean_inc_ref(v_str_4599_);
lean_dec_ref_known(v_declName_4593_, 2);
v___x_4600_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__2));
v___x_4601_ = lean_string_dec_eq(v_str_4599_, v___x_4600_);
lean_dec_ref(v_str_4599_);
return v___x_4601_;
}
else
{
lean_dec(v_declName_4593_);
return v___x_4597_;
}
}
v___jp_4602_:
{
if (lean_obj_tag(v_declName_4593_) == 1)
{
lean_object* v_str_4603_; lean_object* v___x_4604_; uint8_t v___x_4605_; 
v_str_4603_ = lean_ctor_get(v_declName_4593_, 1);
v___x_4604_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__3));
v___x_4605_ = lean_string_dec_eq(v_str_4603_, v___x_4604_);
if (v___x_4605_ == 0)
{
goto v___jp_4598_;
}
else
{
lean_dec_ref_known(v_declName_4593_, 2);
return v___x_4605_;
}
}
else
{
goto v___jp_4598_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_blacklistInsertion___boxed(lean_object* v_env_4608_, lean_object* v_declName_4609_){
_start:
{
uint8_t v_res_4610_; lean_object* v_r_4611_; 
v_res_4610_ = l_Lean_Meta_LazyDiscrTree_blacklistInsertion(v_env_4608_, v_declName_4609_);
v_r_4611_ = lean_box(v_res_4610_);
return v_r_4611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(lean_object* v_opts_4612_, lean_object* v_opt_4613_){
_start:
{
lean_object* v_name_4614_; lean_object* v_defValue_4615_; lean_object* v_map_4616_; lean_object* v___x_4617_; 
v_name_4614_ = lean_ctor_get(v_opt_4613_, 0);
v_defValue_4615_ = lean_ctor_get(v_opt_4613_, 1);
v_map_4616_ = lean_ctor_get(v_opts_4612_, 0);
v___x_4617_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4616_, v_name_4614_);
if (lean_obj_tag(v___x_4617_) == 0)
{
lean_inc(v_defValue_4615_);
return v_defValue_4615_;
}
else
{
lean_object* v_val_4618_; 
v_val_4618_ = lean_ctor_get(v___x_4617_, 0);
lean_inc(v_val_4618_);
lean_dec_ref_known(v___x_4617_, 1);
if (lean_obj_tag(v_val_4618_) == 3)
{
lean_object* v_v_4619_; 
v_v_4619_ = lean_ctor_get(v_val_4618_, 0);
lean_inc(v_v_4619_);
lean_dec_ref_known(v_val_4618_, 1);
return v_v_4619_;
}
else
{
lean_dec(v_val_4618_);
lean_inc(v_defValue_4615_);
return v_defValue_4615_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0___boxed(lean_object* v_opts_4620_, lean_object* v_opt_4621_){
_start:
{
lean_object* v_res_4622_; 
v_res_4622_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(v_opts_4620_, v_opt_4621_);
lean_dec_ref(v_opt_4621_);
lean_dec_ref(v_opts_4620_);
return v_res_4622_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1___redArg(lean_object* v_as_4623_, size_t v_i_4624_, size_t v_stop_4625_, lean_object* v_b_4626_){
_start:
{
uint8_t v___x_4627_; 
v___x_4627_ = lean_usize_dec_eq(v_i_4624_, v_stop_4625_);
if (v___x_4627_ == 0)
{
lean_object* v___x_4628_; lean_object* v_key_4629_; lean_object* v_entry_4630_; lean_object* v___x_4631_; size_t v___x_4632_; size_t v___x_4633_; 
v___x_4628_ = lean_array_uget_borrowed(v_as_4623_, v_i_4624_);
v_key_4629_ = lean_ctor_get(v___x_4628_, 0);
v_entry_4630_ = lean_ctor_get(v___x_4628_, 1);
lean_inc_ref(v_entry_4630_);
lean_inc(v_key_4629_);
v___x_4631_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg(v_b_4626_, v_key_4629_, v_entry_4630_);
v___x_4632_ = ((size_t)1ULL);
v___x_4633_ = lean_usize_add(v_i_4624_, v___x_4632_);
v_i_4624_ = v___x_4633_;
v_b_4626_ = v___x_4631_;
goto _start;
}
else
{
return v_b_4626_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1___redArg___boxed(lean_object* v_as_4635_, lean_object* v_i_4636_, lean_object* v_stop_4637_, lean_object* v_b_4638_){
_start:
{
size_t v_i_boxed_4639_; size_t v_stop_boxed_4640_; lean_object* v_res_4641_; 
v_i_boxed_4639_ = lean_unbox_usize(v_i_4636_);
lean_dec(v_i_4636_);
v_stop_boxed_4640_ = lean_unbox_usize(v_stop_4637_);
lean_dec(v_stop_4637_);
v_res_4641_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1___redArg(v_as_4635_, v_i_boxed_4639_, v_stop_boxed_4640_, v_b_4638_);
lean_dec_ref(v_as_4635_);
return v_res_4641_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0(void){
_start:
{
lean_object* v___x_4642_; lean_object* v___x_4643_; 
v___x_4642_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0_spec__0___redArg___closed__0);
v___x_4643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4643_, 0, v___x_4642_);
return v___x_4643_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1(void){
_start:
{
lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; 
v___x_4644_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_4645_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0);
v___x_4646_ = lean_unsigned_to_nat(0u);
v___x_4647_ = lean_alloc_ctor(0, 12, 0);
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
lean_ctor_set(v___x_4647_, 11, v___x_4644_);
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
lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; lean_object* v___x_4678_; 
v___x_4675_ = lean_unsigned_to_nat(0u);
v___x_4676_ = l_Lean_Options_empty;
v___x_4677_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6));
v___x_4678_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4678_, 0, v___x_4677_);
lean_ctor_set(v___x_4678_, 1, v___x_4676_);
lean_ctor_set(v___x_4678_, 2, v___x_4677_);
lean_ctor_set(v___x_4678_, 3, v___x_4675_);
lean_ctor_set(v___x_4678_, 4, v___x_4675_);
lean_ctor_set(v___x_4678_, 5, v___x_4675_);
return v___x_4678_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11(void){
_start:
{
lean_object* v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; 
v___x_4679_ = l_Lean_NameSet_empty;
v___x_4680_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3);
v___x_4681_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4681_, 0, v___x_4680_);
lean_ctor_set(v___x_4681_, 1, v___x_4680_);
lean_ctor_set(v___x_4681_, 2, v___x_4679_);
return v___x_4681_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12(void){
_start:
{
lean_object* v___x_4682_; lean_object* v___x_4683_; uint8_t v___x_4684_; lean_object* v___x_4685_; 
v___x_4682_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3);
v___x_4683_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0);
v___x_4684_ = 1;
v___x_4685_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4685_, 0, v___x_4683_);
lean_ctor_set(v___x_4685_, 1, v___x_4683_);
lean_ctor_set(v___x_4685_, 2, v___x_4682_);
lean_ctor_set_uint8(v___x_4685_, sizeof(void*)*3, v___x_4684_);
return v___x_4685_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13(void){
_start:
{
lean_object* v___x_4686_; lean_object* v___x_4687_; 
v___x_4686_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0);
v___x_4687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4687_, 0, v___x_4686_);
lean_ctor_set(v___x_4687_, 1, v___x_4686_);
return v___x_4687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(lean_object* v_cctx_4688_, lean_object* v_env_4689_, lean_object* v_modName_4690_, lean_object* v_d_4691_, lean_object* v_cacheRef_4692_, lean_object* v_tree_4693_, lean_object* v_act_4694_, lean_object* v_c_4695_){
_start:
{
uint8_t v___x_4697_; 
lean_inc_ref(v_c_4695_);
v___x_4697_ = l_Lean_AsyncConstantInfo_isUnsafe(v_c_4695_);
if (v___x_4697_ == 0)
{
lean_object* v_name_4698_; uint8_t v___x_4699_; 
v_name_4698_ = lean_ctor_get(v_c_4695_, 0);
lean_inc_n(v_name_4698_, 2);
lean_inc_ref(v_env_4689_);
v___x_4699_ = l_Lean_Meta_LazyDiscrTree_blacklistInsertion(v_env_4689_, v_name_4698_);
if (v___x_4699_ == 0)
{
lean_object* v___x_4700_; uint8_t v___x_4701_; lean_object* v___x_4702_; lean_object* v_ngen_4703_; lean_object* v_core_4704_; lean_object* v_meta_4705_; lean_object* v___x_4707_; uint8_t v_isShared_4708_; uint8_t v_isSharedCheck_4831_; 
v___x_4700_ = lean_box(1);
v___x_4701_ = 1;
v___x_4702_ = lean_st_ref_get(v_cacheRef_4692_);
v_ngen_4703_ = lean_ctor_get(v___x_4702_, 0);
v_core_4704_ = lean_ctor_get(v___x_4702_, 1);
v_meta_4705_ = lean_ctor_get(v___x_4702_, 2);
v_isSharedCheck_4831_ = !lean_is_exclusive(v___x_4702_);
if (v_isSharedCheck_4831_ == 0)
{
v___x_4707_ = v___x_4702_;
v_isShared_4708_ = v_isSharedCheck_4831_;
goto v_resetjp_4706_;
}
else
{
lean_inc(v_meta_4705_);
lean_inc(v_core_4704_);
lean_inc(v_ngen_4703_);
lean_dec(v___x_4702_);
v___x_4707_ = lean_box(0);
v_isShared_4708_ = v_isSharedCheck_4831_;
goto v_resetjp_4706_;
}
v_resetjp_4706_:
{
lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; uint8_t v___x_4716_; uint8_t v___x_4717_; uint8_t v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; lean_object* v___x_4731_; lean_object* v___x_4732_; uint16_t v___y_4734_; lean_object* v___y_4735_; lean_object* v_fileName_4736_; lean_object* v_fileMap_4737_; lean_object* v_currNamespace_4738_; lean_object* v_openDecls_4739_; lean_object* v_initHeartbeats_4740_; lean_object* v_maxHeartbeats_4741_; lean_object* v_quotContext_4742_; lean_object* v_currMacroScope_4743_; lean_object* v_cancelTk_x3f_4744_; lean_object* v_inheritedTraceOptions_4745_; lean_object* v_currRecDepth_4746_; lean_object* v_ref_4747_; uint8_t v_suppressElabErrors_4748_; uint8_t v_checkDeprecated_4749_; uint8_t v_isRecordingDeps_4750_; lean_object* v___x_4777_; lean_object* v___x_4778_; lean_object* v_toCold_4779_; lean_object* v_currRecDepth_4780_; lean_object* v_ref_4781_; uint8_t v_suppressElabErrors_4782_; uint8_t v_checkDeprecated_4783_; uint8_t v_isRecordingDeps_4784_; lean_object* v_fileName_4785_; lean_object* v_fileMap_4786_; lean_object* v_options_4787_; lean_object* v_currNamespace_4788_; lean_object* v_openDecls_4789_; lean_object* v_initHeartbeats_4790_; lean_object* v_maxHeartbeats_4791_; lean_object* v_quotContext_4792_; lean_object* v_currMacroScope_4793_; lean_object* v_cancelTk_x3f_4794_; uint8_t v___y_4796_; uint16_t v___y_4797_; lean_object* v___y_4798_; lean_object* v___y_4821_; 
v___x_4709_ = lean_unsigned_to_nat(0u);
v___x_4710_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4711_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3);
v___x_4712_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4713_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4713_, 0, v___x_4710_);
lean_ctor_set(v___x_4713_, 1, v_meta_4705_);
lean_ctor_set(v___x_4713_, 2, v___x_4700_);
lean_ctor_set(v___x_4713_, 3, v___x_4711_);
lean_ctor_set(v___x_4713_, 4, v___x_4712_);
lean_inc_ref(v_ngen_4703_);
v___x_4714_ = l_Lean_Meta_LazyDiscrTree_Cache_empty(v_ngen_4703_);
v___x_4715_ = lean_st_ref_swap(v_cacheRef_4692_, v___x_4714_);
lean_dec(v___x_4715_);
v___x_4716_ = 2;
v___x_4717_ = 0;
v___x_4718_ = 2;
v___x_4719_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_4719_, 0, v___x_4699_);
lean_ctor_set_uint8(v___x_4719_, 1, v___x_4699_);
lean_ctor_set_uint8(v___x_4719_, 2, v___x_4699_);
lean_ctor_set_uint8(v___x_4719_, 3, v___x_4699_);
lean_ctor_set_uint8(v___x_4719_, 4, v___x_4699_);
lean_ctor_set_uint8(v___x_4719_, 5, v___x_4701_);
lean_ctor_set_uint8(v___x_4719_, 6, v___x_4701_);
lean_ctor_set_uint8(v___x_4719_, 7, v___x_4699_);
lean_ctor_set_uint8(v___x_4719_, 8, v___x_4701_);
lean_ctor_set_uint8(v___x_4719_, 9, v___x_4716_);
lean_ctor_set_uint8(v___x_4719_, 10, v___x_4717_);
lean_ctor_set_uint8(v___x_4719_, 11, v___x_4701_);
lean_ctor_set_uint8(v___x_4719_, 12, v___x_4701_);
lean_ctor_set_uint8(v___x_4719_, 13, v___x_4701_);
lean_ctor_set_uint8(v___x_4719_, 14, v___x_4718_);
lean_ctor_set_uint8(v___x_4719_, 15, v___x_4701_);
lean_ctor_set_uint8(v___x_4719_, 16, v___x_4701_);
lean_ctor_set_uint8(v___x_4719_, 17, v___x_4701_);
lean_ctor_set_uint8(v___x_4719_, 18, v___x_4701_);
lean_ctor_set_uint8(v___x_4719_, 19, v___x_4699_);
v___x_4720_ = l_Lean_Meta_Config_toConfigWithKey(v___x_4719_);
v___x_4721_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5);
v___x_4722_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6));
v___x_4723_ = lean_box(0);
v___x_4724_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4724_, 0, v___x_4720_);
lean_ctor_set(v___x_4724_, 1, v___x_4700_);
lean_ctor_set(v___x_4724_, 2, v___x_4721_);
lean_ctor_set(v___x_4724_, 3, v___x_4722_);
lean_ctor_set(v___x_4724_, 4, v___x_4723_);
lean_ctor_set(v___x_4724_, 5, v___x_4709_);
lean_ctor_set(v___x_4724_, 6, v___x_4723_);
lean_ctor_set_uint8(v___x_4724_, sizeof(void*)*7, v___x_4699_);
lean_ctor_set_uint8(v___x_4724_, sizeof(void*)*7 + 1, v___x_4699_);
lean_ctor_set_uint8(v___x_4724_, sizeof(void*)*7 + 2, v___x_4699_);
lean_ctor_set_uint8(v___x_4724_, sizeof(void*)*7 + 3, v___x_4701_);
v___x_4725_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__7, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__7_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__7);
v___x_4726_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__8));
v___x_4727_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__9, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__9_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__9);
v___x_4728_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10);
v___x_4729_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11);
v___x_4730_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12);
v___x_4731_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4731_, 0, v_env_4689_);
lean_ctor_set(v___x_4731_, 1, v___x_4725_);
lean_ctor_set(v___x_4731_, 2, v_ngen_4703_);
lean_ctor_set(v___x_4731_, 3, v___x_4726_);
lean_ctor_set(v___x_4731_, 4, v___x_4727_);
lean_ctor_set(v___x_4731_, 5, v_core_4704_);
lean_ctor_set(v___x_4731_, 6, v___x_4728_);
lean_ctor_set(v___x_4731_, 7, v___x_4729_);
lean_ctor_set(v___x_4731_, 8, v___x_4730_);
lean_ctor_set(v___x_4731_, 9, v___x_4722_);
v___x_4732_ = lean_st_mk_ref(v___x_4731_);
v___x_4777_ = l_Lean_inheritedTraceOptions;
v___x_4778_ = lean_st_ref_get(v___x_4777_);
v_toCold_4779_ = lean_ctor_get(v_cctx_4688_, 0);
lean_inc_ref(v_toCold_4779_);
v_currRecDepth_4780_ = lean_ctor_get(v_cctx_4688_, 1);
lean_inc(v_currRecDepth_4780_);
v_ref_4781_ = lean_ctor_get(v_cctx_4688_, 2);
lean_inc(v_ref_4781_);
v_suppressElabErrors_4782_ = lean_ctor_get_uint8(v_cctx_4688_, sizeof(void*)*3 + 2);
v_checkDeprecated_4783_ = lean_ctor_get_uint8(v_cctx_4688_, sizeof(void*)*3 + 3);
v_isRecordingDeps_4784_ = lean_ctor_get_uint8(v_cctx_4688_, sizeof(void*)*3 + 4);
lean_dec_ref(v_cctx_4688_);
v_fileName_4785_ = lean_ctor_get(v_toCold_4779_, 0);
lean_inc_ref(v_fileName_4785_);
v_fileMap_4786_ = lean_ctor_get(v_toCold_4779_, 1);
lean_inc_ref(v_fileMap_4786_);
v_options_4787_ = lean_ctor_get(v_toCold_4779_, 2);
lean_inc_ref(v_options_4787_);
v_currNamespace_4788_ = lean_ctor_get(v_toCold_4779_, 4);
lean_inc(v_currNamespace_4788_);
v_openDecls_4789_ = lean_ctor_get(v_toCold_4779_, 5);
lean_inc(v_openDecls_4789_);
v_initHeartbeats_4790_ = lean_ctor_get(v_toCold_4779_, 6);
lean_inc(v_initHeartbeats_4790_);
v_maxHeartbeats_4791_ = lean_ctor_get(v_toCold_4779_, 7);
lean_inc(v_maxHeartbeats_4791_);
v_quotContext_4792_ = lean_ctor_get(v_toCold_4779_, 8);
lean_inc(v_quotContext_4792_);
v_currMacroScope_4793_ = lean_ctor_get(v_toCold_4779_, 9);
lean_inc(v_currMacroScope_4793_);
v_cancelTk_x3f_4794_ = lean_ctor_get(v_toCold_4779_, 10);
lean_inc(v_cancelTk_x3f_4794_);
lean_dec_ref(v_toCold_4779_);
if (v_isRecordingDeps_4784_ == 0)
{
v___y_4821_ = v_options_4787_;
goto v___jp_4820_;
}
else
{
lean_object* v___x_4830_; 
v___x_4830_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_4787_);
v___y_4821_ = v___x_4830_;
goto v___jp_4820_;
}
v___jp_4733_:
{
lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; lean_object* v___x_4755_; lean_object* v___x_4756_; 
v___x_4751_ = l_Lean_maxRecDepth;
v___x_4752_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(v___y_4735_, v___x_4751_);
v___x_4753_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_4753_, 0, v_fileName_4736_);
lean_ctor_set(v___x_4753_, 1, v_fileMap_4737_);
lean_ctor_set(v___x_4753_, 2, v___y_4735_);
lean_ctor_set(v___x_4753_, 3, v___x_4752_);
lean_ctor_set(v___x_4753_, 4, v_currNamespace_4738_);
lean_ctor_set(v___x_4753_, 5, v_openDecls_4739_);
lean_ctor_set(v___x_4753_, 6, v_initHeartbeats_4740_);
lean_ctor_set(v___x_4753_, 7, v_maxHeartbeats_4741_);
lean_ctor_set(v___x_4753_, 8, v_quotContext_4742_);
lean_ctor_set(v___x_4753_, 9, v_currMacroScope_4743_);
lean_ctor_set(v___x_4753_, 10, v_cancelTk_x3f_4744_);
lean_ctor_set(v___x_4753_, 11, v_inheritedTraceOptions_4745_);
v___x_4754_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_4754_, 0, v___x_4753_);
lean_ctor_set(v___x_4754_, 1, v_currRecDepth_4746_);
lean_ctor_set(v___x_4754_, 2, v_ref_4747_);
lean_ctor_set_uint16(v___x_4754_, sizeof(void*)*3, v___y_4734_);
lean_ctor_set_uint8(v___x_4754_, sizeof(void*)*3 + 2, v_suppressElabErrors_4748_);
lean_ctor_set_uint8(v___x_4754_, sizeof(void*)*3 + 3, v_checkDeprecated_4749_);
lean_ctor_set_uint8(v___x_4754_, sizeof(void*)*3 + 4, v_isRecordingDeps_4750_);
v___x_4755_ = lean_st_mk_ref(v___x_4713_);
lean_inc(v___x_4732_);
lean_inc(v___x_4755_);
lean_inc(v_name_4698_);
v___x_4756_ = lean_apply_7(v_act_4694_, v_name_4698_, v_c_4695_, v___x_4724_, v___x_4755_, v___x_4754_, v___x_4732_, lean_box(0));
if (lean_obj_tag(v___x_4756_) == 0)
{
lean_object* v_a_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; lean_object* v_ngen_4760_; lean_object* v_cache_4761_; lean_object* v_cache_4762_; lean_object* v___x_4764_; 
lean_dec(v_name_4698_);
lean_dec(v_modName_4690_);
v_a_4757_ = lean_ctor_get(v___x_4756_, 0);
lean_inc(v_a_4757_);
lean_dec_ref_known(v___x_4756_, 1);
v___x_4758_ = lean_st_ref_get(v___x_4755_);
lean_dec(v___x_4755_);
v___x_4759_ = lean_st_ref_get(v___x_4732_);
lean_dec(v___x_4732_);
v_ngen_4760_ = lean_ctor_get(v___x_4759_, 2);
lean_inc_ref(v_ngen_4760_);
v_cache_4761_ = lean_ctor_get(v___x_4759_, 5);
lean_inc_ref(v_cache_4761_);
lean_dec(v___x_4759_);
v_cache_4762_ = lean_ctor_get(v___x_4758_, 1);
lean_inc_ref(v_cache_4762_);
lean_dec(v___x_4758_);
if (v_isShared_4708_ == 0)
{
lean_ctor_set(v___x_4707_, 2, v_cache_4762_);
lean_ctor_set(v___x_4707_, 1, v_cache_4761_);
lean_ctor_set(v___x_4707_, 0, v_ngen_4760_);
v___x_4764_ = v___x_4707_;
goto v_reusejp_4763_;
}
else
{
lean_object* v_reuseFailAlloc_4771_; 
v_reuseFailAlloc_4771_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4771_, 0, v_ngen_4760_);
lean_ctor_set(v_reuseFailAlloc_4771_, 1, v_cache_4761_);
lean_ctor_set(v_reuseFailAlloc_4771_, 2, v_cache_4762_);
v___x_4764_ = v_reuseFailAlloc_4771_;
goto v_reusejp_4763_;
}
v_reusejp_4763_:
{
lean_object* v___x_4765_; lean_object* v___x_4766_; uint8_t v___x_4767_; 
v___x_4765_ = lean_st_ref_swap(v_cacheRef_4692_, v___x_4764_);
lean_dec(v___x_4765_);
v___x_4766_ = lean_array_get_size(v_a_4757_);
v___x_4767_ = lean_nat_dec_lt(v___x_4709_, v___x_4766_);
if (v___x_4767_ == 0)
{
lean_dec(v_a_4757_);
return v_tree_4693_;
}
else
{
size_t v___x_4768_; size_t v___x_4769_; lean_object* v___x_4770_; 
v___x_4768_ = ((size_t)0ULL);
v___x_4769_ = lean_usize_of_nat(v___x_4766_);
v___x_4770_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1___redArg(v_a_4757_, v___x_4768_, v___x_4769_, v_tree_4693_);
lean_dec(v_a_4757_);
return v___x_4770_;
}
}
}
else
{
lean_object* v_a_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; 
lean_dec(v___x_4755_);
lean_dec(v___x_4732_);
lean_del_object(v___x_4707_);
v_a_4772_ = lean_ctor_get(v___x_4756_, 0);
lean_inc(v_a_4772_);
lean_dec_ref_known(v___x_4756_, 1);
v___x_4773_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4773_, 0, v_modName_4690_);
lean_ctor_set(v___x_4773_, 1, v_name_4698_);
lean_ctor_set(v___x_4773_, 2, v_a_4772_);
v___x_4774_ = lean_st_ref_take(v_d_4691_);
v___x_4775_ = lean_array_push(v___x_4774_, v___x_4773_);
v___x_4776_ = lean_st_ref_put(v_d_4691_, v___x_4775_);
return v_tree_4693_;
}
}
v___jp_4795_:
{
lean_object* v___x_4799_; lean_object* v_env_4800_; lean_object* v_nextMacroScope_4801_; lean_object* v_ngen_4802_; lean_object* v_auxDeclNGen_4803_; lean_object* v_traceState_4804_; lean_object* v_recordedDeps_4805_; lean_object* v_messages_4806_; lean_object* v_infoState_4807_; lean_object* v_snapshotTasks_4808_; lean_object* v___x_4810_; uint8_t v_isShared_4811_; uint8_t v_isSharedCheck_4818_; 
v___x_4799_ = lean_st_ref_take(v___x_4732_);
v_env_4800_ = lean_ctor_get(v___x_4799_, 0);
v_nextMacroScope_4801_ = lean_ctor_get(v___x_4799_, 1);
v_ngen_4802_ = lean_ctor_get(v___x_4799_, 2);
v_auxDeclNGen_4803_ = lean_ctor_get(v___x_4799_, 3);
v_traceState_4804_ = lean_ctor_get(v___x_4799_, 4);
v_recordedDeps_4805_ = lean_ctor_get(v___x_4799_, 6);
v_messages_4806_ = lean_ctor_get(v___x_4799_, 7);
v_infoState_4807_ = lean_ctor_get(v___x_4799_, 8);
v_snapshotTasks_4808_ = lean_ctor_get(v___x_4799_, 9);
v_isSharedCheck_4818_ = !lean_is_exclusive(v___x_4799_);
if (v_isSharedCheck_4818_ == 0)
{
lean_object* v_unused_4819_; 
v_unused_4819_ = lean_ctor_get(v___x_4799_, 5);
lean_dec(v_unused_4819_);
v___x_4810_ = v___x_4799_;
v_isShared_4811_ = v_isSharedCheck_4818_;
goto v_resetjp_4809_;
}
else
{
lean_inc(v_snapshotTasks_4808_);
lean_inc(v_infoState_4807_);
lean_inc(v_messages_4806_);
lean_inc(v_recordedDeps_4805_);
lean_inc(v_traceState_4804_);
lean_inc(v_auxDeclNGen_4803_);
lean_inc(v_ngen_4802_);
lean_inc(v_nextMacroScope_4801_);
lean_inc(v_env_4800_);
lean_dec(v___x_4799_);
v___x_4810_ = lean_box(0);
v_isShared_4811_ = v_isSharedCheck_4818_;
goto v_resetjp_4809_;
}
v_resetjp_4809_:
{
lean_object* v___x_4812_; lean_object* v___x_4813_; lean_object* v___x_4815_; 
v___x_4812_ = l_Lean_Kernel_enableDiag(v_env_4800_, v___y_4796_);
v___x_4813_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13);
if (v_isShared_4811_ == 0)
{
lean_ctor_set(v___x_4810_, 5, v___x_4813_);
lean_ctor_set(v___x_4810_, 0, v___x_4812_);
v___x_4815_ = v___x_4810_;
goto v_reusejp_4814_;
}
else
{
lean_object* v_reuseFailAlloc_4817_; 
v_reuseFailAlloc_4817_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4817_, 0, v___x_4812_);
lean_ctor_set(v_reuseFailAlloc_4817_, 1, v_nextMacroScope_4801_);
lean_ctor_set(v_reuseFailAlloc_4817_, 2, v_ngen_4802_);
lean_ctor_set(v_reuseFailAlloc_4817_, 3, v_auxDeclNGen_4803_);
lean_ctor_set(v_reuseFailAlloc_4817_, 4, v_traceState_4804_);
lean_ctor_set(v_reuseFailAlloc_4817_, 5, v___x_4813_);
lean_ctor_set(v_reuseFailAlloc_4817_, 6, v_recordedDeps_4805_);
lean_ctor_set(v_reuseFailAlloc_4817_, 7, v_messages_4806_);
lean_ctor_set(v_reuseFailAlloc_4817_, 8, v_infoState_4807_);
lean_ctor_set(v_reuseFailAlloc_4817_, 9, v_snapshotTasks_4808_);
v___x_4815_ = v_reuseFailAlloc_4817_;
goto v_reusejp_4814_;
}
v_reusejp_4814_:
{
lean_object* v___x_4816_; 
v___x_4816_ = lean_st_ref_put(v___x_4732_, v___x_4815_);
v___y_4734_ = v___y_4797_;
v___y_4735_ = v___y_4798_;
v_fileName_4736_ = v_fileName_4785_;
v_fileMap_4737_ = v_fileMap_4786_;
v_currNamespace_4738_ = v_currNamespace_4788_;
v_openDecls_4739_ = v_openDecls_4789_;
v_initHeartbeats_4740_ = v_initHeartbeats_4790_;
v_maxHeartbeats_4741_ = v_maxHeartbeats_4791_;
v_quotContext_4742_ = v_quotContext_4792_;
v_currMacroScope_4743_ = v_currMacroScope_4793_;
v_cancelTk_x3f_4744_ = v_cancelTk_x3f_4794_;
v_inheritedTraceOptions_4745_ = v___x_4778_;
v_currRecDepth_4746_ = v_currRecDepth_4780_;
v_ref_4747_ = v_ref_4781_;
v_suppressElabErrors_4748_ = v_suppressElabErrors_4782_;
v_checkDeprecated_4749_ = v_checkDeprecated_4783_;
v_isRecordingDeps_4750_ = v_isRecordingDeps_4784_;
goto v___jp_4733_;
}
}
}
v___jp_4820_:
{
uint16_t v___x_4822_; lean_object* v___x_4823_; lean_object* v_env_4824_; uint8_t v___x_4825_; uint16_t v___x_4826_; uint16_t v___x_4827_; uint16_t v___x_4828_; uint8_t v___x_4829_; 
v___x_4822_ = l_Lean_OptionFlags_ofOptions(v___y_4821_);
v___x_4823_ = lean_st_ref_get(v___x_4732_);
v_env_4824_ = lean_ctor_get(v___x_4823_, 0);
lean_inc_ref(v_env_4824_);
lean_dec(v___x_4823_);
v___x_4825_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4824_);
lean_dec_ref(v_env_4824_);
v___x_4826_ = 512;
v___x_4827_ = lean_uint16_land(v___x_4822_, v___x_4826_);
v___x_4828_ = 0;
v___x_4829_ = lean_uint16_dec_eq(v___x_4827_, v___x_4828_);
if (v___x_4829_ == 0)
{
if (v___x_4825_ == 0)
{
v___y_4796_ = v___x_4701_;
v___y_4797_ = v___x_4822_;
v___y_4798_ = v___y_4821_;
goto v___jp_4795_;
}
else
{
v___y_4734_ = v___x_4822_;
v___y_4735_ = v___y_4821_;
v_fileName_4736_ = v_fileName_4785_;
v_fileMap_4737_ = v_fileMap_4786_;
v_currNamespace_4738_ = v_currNamespace_4788_;
v_openDecls_4739_ = v_openDecls_4789_;
v_initHeartbeats_4740_ = v_initHeartbeats_4790_;
v_maxHeartbeats_4741_ = v_maxHeartbeats_4791_;
v_quotContext_4742_ = v_quotContext_4792_;
v_currMacroScope_4743_ = v_currMacroScope_4793_;
v_cancelTk_x3f_4744_ = v_cancelTk_x3f_4794_;
v_inheritedTraceOptions_4745_ = v___x_4778_;
v_currRecDepth_4746_ = v_currRecDepth_4780_;
v_ref_4747_ = v_ref_4781_;
v_suppressElabErrors_4748_ = v_suppressElabErrors_4782_;
v_checkDeprecated_4749_ = v_checkDeprecated_4783_;
v_isRecordingDeps_4750_ = v_isRecordingDeps_4784_;
goto v___jp_4733_;
}
}
else
{
if (v___x_4825_ == 0)
{
v___y_4734_ = v___x_4822_;
v___y_4735_ = v___y_4821_;
v_fileName_4736_ = v_fileName_4785_;
v_fileMap_4737_ = v_fileMap_4786_;
v_currNamespace_4738_ = v_currNamespace_4788_;
v_openDecls_4739_ = v_openDecls_4789_;
v_initHeartbeats_4740_ = v_initHeartbeats_4790_;
v_maxHeartbeats_4741_ = v_maxHeartbeats_4791_;
v_quotContext_4742_ = v_quotContext_4792_;
v_currMacroScope_4743_ = v_currMacroScope_4793_;
v_cancelTk_x3f_4744_ = v_cancelTk_x3f_4794_;
v_inheritedTraceOptions_4745_ = v___x_4778_;
v_currRecDepth_4746_ = v_currRecDepth_4780_;
v_ref_4747_ = v_ref_4781_;
v_suppressElabErrors_4748_ = v_suppressElabErrors_4782_;
v_checkDeprecated_4749_ = v_checkDeprecated_4783_;
v_isRecordingDeps_4750_ = v_isRecordingDeps_4784_;
goto v___jp_4733_;
}
else
{
v___y_4796_ = v___x_4699_;
v___y_4797_ = v___x_4822_;
v___y_4798_ = v___y_4821_;
goto v___jp_4795_;
}
}
}
}
}
else
{
lean_dec(v_name_4698_);
lean_dec_ref(v_c_4695_);
lean_dec_ref(v_act_4694_);
lean_dec(v_modName_4690_);
lean_dec_ref(v_env_4689_);
lean_dec_ref(v_cctx_4688_);
return v_tree_4693_;
}
}
else
{
lean_dec_ref(v_c_4695_);
lean_dec_ref(v_act_4694_);
lean_dec(v_modName_4690_);
lean_dec_ref(v_env_4689_);
lean_dec_ref(v_cctx_4688_);
return v_tree_4693_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___boxed(lean_object* v_cctx_4832_, lean_object* v_env_4833_, lean_object* v_modName_4834_, lean_object* v_d_4835_, lean_object* v_cacheRef_4836_, lean_object* v_tree_4837_, lean_object* v_act_4838_, lean_object* v_c_4839_, lean_object* v_a_4840_){
_start:
{
lean_object* v_res_4841_; 
v_res_4841_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_4832_, v_env_4833_, v_modName_4834_, v_d_4835_, v_cacheRef_4836_, v_tree_4837_, v_act_4838_, v_c_4839_);
lean_dec(v_cacheRef_4836_);
lean_dec(v_d_4835_);
return v_res_4841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData(lean_object* v_00_u03b1_4842_, lean_object* v_cctx_4843_, lean_object* v_env_4844_, lean_object* v_modName_4845_, lean_object* v_d_4846_, lean_object* v_cacheRef_4847_, lean_object* v_tree_4848_, lean_object* v_act_4849_, lean_object* v_c_4850_){
_start:
{
lean_object* v___x_4852_; 
v___x_4852_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_4843_, v_env_4844_, v_modName_4845_, v_d_4846_, v_cacheRef_4847_, v_tree_4848_, v_act_4849_, v_c_4850_);
return v___x_4852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___boxed(lean_object* v_00_u03b1_4853_, lean_object* v_cctx_4854_, lean_object* v_env_4855_, lean_object* v_modName_4856_, lean_object* v_d_4857_, lean_object* v_cacheRef_4858_, lean_object* v_tree_4859_, lean_object* v_act_4860_, lean_object* v_c_4861_, lean_object* v_a_4862_){
_start:
{
lean_object* v_res_4863_; 
v_res_4863_ = l_Lean_Meta_LazyDiscrTree_addConstImportData(v_00_u03b1_4853_, v_cctx_4854_, v_env_4855_, v_modName_4856_, v_d_4857_, v_cacheRef_4858_, v_tree_4859_, v_act_4860_, v_c_4861_);
lean_dec(v_cacheRef_4858_);
lean_dec(v_d_4857_);
return v_res_4863_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1(lean_object* v_00_u03b1_4864_, lean_object* v_as_4865_, size_t v_i_4866_, size_t v_stop_4867_, lean_object* v_b_4868_){
_start:
{
lean_object* v___x_4869_; 
v___x_4869_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1___redArg(v_as_4865_, v_i_4866_, v_stop_4867_, v_b_4868_);
return v___x_4869_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1___boxed(lean_object* v_00_u03b1_4870_, lean_object* v_as_4871_, lean_object* v_i_4872_, lean_object* v_stop_4873_, lean_object* v_b_4874_){
_start:
{
size_t v_i_boxed_4875_; size_t v_stop_boxed_4876_; lean_object* v_res_4877_; 
v_i_boxed_4875_ = lean_unbox_usize(v_i_4872_);
lean_dec(v_i_4872_);
v_stop_boxed_4876_ = lean_unbox_usize(v_stop_4873_);
lean_dec(v_stop_4873_);
v_res_4877_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1(v_00_u03b1_4870_, v_as_4871_, v_i_boxed_4875_, v_stop_boxed_4876_, v_b_4874_);
lean_dec_ref(v_as_4871_);
return v_res_4877_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___redArg___closed__0(void){
_start:
{
lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; 
v___x_4878_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__0));
v___x_4879_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1);
v___x_4880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4880_, 0, v___x_4879_);
lean_ctor_set(v___x_4880_, 1, v___x_4878_);
return v___x_4880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___redArg(){
_start:
{
lean_object* v___x_4882_; 
v___x_4882_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___redArg___closed__0);
return v___x_4882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___redArg___boxed(lean_object* v___dummy_4883_){
_start:
{
lean_object* v_res_4884_; 
v_res_4884_ = l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___redArg();
return v_res_4884_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0(void){
_start:
{
lean_object* v___x_4885_; 
v___x_4885_ = l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___redArg();
return v___x_4885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults(lean_object* v_00_u03b1_4886_){
_start:
{
lean_object* v___x_4887_; 
v___x_4887_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0);
return v___x_4887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_append___redArg(lean_object* v_x_4888_, lean_object* v_y_4889_){
_start:
{
lean_object* v_tree_4890_; lean_object* v_errors_4891_; lean_object* v_tree_4892_; lean_object* v_errors_4893_; lean_object* v___x_4895_; uint8_t v_isShared_4896_; uint8_t v_isSharedCheck_4902_; 
v_tree_4890_ = lean_ctor_get(v_x_4888_, 0);
lean_inc_ref(v_tree_4890_);
v_errors_4891_ = lean_ctor_get(v_x_4888_, 1);
lean_inc_ref(v_errors_4891_);
lean_dec_ref(v_x_4888_);
v_tree_4892_ = lean_ctor_get(v_y_4889_, 0);
v_errors_4893_ = lean_ctor_get(v_y_4889_, 1);
v_isSharedCheck_4902_ = !lean_is_exclusive(v_y_4889_);
if (v_isSharedCheck_4902_ == 0)
{
v___x_4895_ = v_y_4889_;
v_isShared_4896_ = v_isSharedCheck_4902_;
goto v_resetjp_4894_;
}
else
{
lean_inc(v_errors_4893_);
lean_inc(v_tree_4892_);
lean_dec(v_y_4889_);
v___x_4895_ = lean_box(0);
v_isShared_4896_ = v_isSharedCheck_4902_;
goto v_resetjp_4894_;
}
v_resetjp_4894_:
{
lean_object* v___x_4897_; lean_object* v___x_4898_; lean_object* v___x_4900_; 
v___x_4897_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg(v_tree_4890_, v_tree_4892_);
v___x_4898_ = l_Array_append___redArg(v_errors_4891_, v_errors_4893_);
lean_dec_ref(v_errors_4893_);
if (v_isShared_4896_ == 0)
{
lean_ctor_set(v___x_4895_, 1, v___x_4898_);
lean_ctor_set(v___x_4895_, 0, v___x_4897_);
v___x_4900_ = v___x_4895_;
goto v_reusejp_4899_;
}
else
{
lean_object* v_reuseFailAlloc_4901_; 
v_reuseFailAlloc_4901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4901_, 0, v___x_4897_);
lean_ctor_set(v_reuseFailAlloc_4901_, 1, v___x_4898_);
v___x_4900_ = v_reuseFailAlloc_4901_;
goto v_reusejp_4899_;
}
v_reusejp_4899_:
{
return v___x_4900_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_append(lean_object* v_00_u03b1_4903_, lean_object* v_x_4904_, lean_object* v_y_4905_){
_start:
{
lean_object* v___x_4906_; 
v___x_4906_ = l_Lean_Meta_LazyDiscrTree_InitResults_append___redArg(v_x_4904_, v_y_4905_);
return v___x_4906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___redArg(){
_start:
{
lean_object* v___x_4909_; 
v___x_4909_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___redArg___closed__0));
return v___x_4909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___redArg___boxed(lean_object* v___dummy_4910_){
_start:
{
lean_object* v_res_4911_; 
v_res_4911_ = l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___redArg();
return v_res_4911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_instAppend(lean_object* v_00_u03b1_4912_){
_start:
{
lean_object* v___x_4913_; 
v___x_4913_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___redArg___closed__0));
return v___x_4913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat___redArg(lean_object* v_d_4914_, lean_object* v_tree_4915_){
_start:
{
lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4919_; 
v___x_4917_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_ImportData_new___closed__0));
v___x_4918_ = lean_st_ref_swap(v_d_4914_, v___x_4917_);
v___x_4919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4919_, 0, v_tree_4915_);
lean_ctor_set(v___x_4919_, 1, v___x_4918_);
return v___x_4919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat___redArg___boxed(lean_object* v_d_4920_, lean_object* v_tree_4921_, lean_object* v_a_4922_){
_start:
{
lean_object* v_res_4923_; 
v_res_4923_ = l_Lean_Meta_LazyDiscrTree_toFlat___redArg(v_d_4920_, v_tree_4921_);
lean_dec(v_d_4920_);
return v_res_4923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat(lean_object* v_00_u03b1_4924_, lean_object* v_d_4925_, lean_object* v_tree_4926_){
_start:
{
lean_object* v___x_4928_; 
v___x_4928_ = l_Lean_Meta_LazyDiscrTree_toFlat___redArg(v_d_4925_, v_tree_4926_);
return v___x_4928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat___boxed(lean_object* v_00_u03b1_4929_, lean_object* v_d_4930_, lean_object* v_tree_4931_, lean_object* v_a_4932_){
_start:
{
lean_object* v_res_4933_; 
v_res_4933_ = l_Lean_Meta_LazyDiscrTree_toFlat(v_00_u03b1_4929_, v_d_4930_, v_tree_4931_);
lean_dec(v_d_4930_);
return v_res_4933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(lean_object* v_cctx_4934_, lean_object* v_env_4935_, lean_object* v_act_4936_, lean_object* v_d_4937_, lean_object* v_cacheRef_4938_, lean_object* v_tree_4939_, lean_object* v_mname_4940_, lean_object* v_mdata_4941_, lean_object* v_i_4942_){
_start:
{
lean_object* v_constants_4944_; lean_object* v___x_4945_; uint8_t v___x_4946_; 
v_constants_4944_ = lean_ctor_get(v_mdata_4941_, 2);
v___x_4945_ = lean_array_get_size(v_constants_4944_);
v___x_4946_ = lean_nat_dec_lt(v_i_4942_, v___x_4945_);
if (v___x_4946_ == 0)
{
lean_dec(v_i_4942_);
lean_dec(v_mname_4940_);
lean_dec_ref(v_act_4936_);
lean_dec_ref(v_env_4935_);
lean_dec_ref(v_cctx_4934_);
return v_tree_4939_;
}
else
{
lean_object* v___x_4947_; lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; 
v___x_4947_ = lean_array_fget_borrowed(v_constants_4944_, v_i_4942_);
lean_inc(v___x_4947_);
v___x_4948_ = l_Lean_AsyncConstantInfo_ofConstantInfo(v___x_4947_);
lean_inc_ref(v_act_4936_);
lean_inc(v_mname_4940_);
lean_inc_ref(v_env_4935_);
lean_inc_ref(v_cctx_4934_);
v___x_4949_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_4934_, v_env_4935_, v_mname_4940_, v_d_4937_, v_cacheRef_4938_, v_tree_4939_, v_act_4936_, v___x_4948_);
v___x_4950_ = lean_unsigned_to_nat(1u);
v___x_4951_ = lean_nat_add(v_i_4942_, v___x_4950_);
lean_dec(v_i_4942_);
v_tree_4939_ = v___x_4949_;
v_i_4942_ = v___x_4951_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg___boxed(lean_object* v_cctx_4953_, lean_object* v_env_4954_, lean_object* v_act_4955_, lean_object* v_d_4956_, lean_object* v_cacheRef_4957_, lean_object* v_tree_4958_, lean_object* v_mname_4959_, lean_object* v_mdata_4960_, lean_object* v_i_4961_, lean_object* v_a_4962_){
_start:
{
lean_object* v_res_4963_; 
v_res_4963_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(v_cctx_4953_, v_env_4954_, v_act_4955_, v_d_4956_, v_cacheRef_4957_, v_tree_4958_, v_mname_4959_, v_mdata_4960_, v_i_4961_);
lean_dec_ref(v_mdata_4960_);
lean_dec(v_cacheRef_4957_);
lean_dec(v_d_4956_);
return v_res_4963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule(lean_object* v_00_u03b1_4964_, lean_object* v_cctx_4965_, lean_object* v_env_4966_, lean_object* v_act_4967_, lean_object* v_d_4968_, lean_object* v_cacheRef_4969_, lean_object* v_tree_4970_, lean_object* v_mname_4971_, lean_object* v_mdata_4972_, lean_object* v_i_4973_){
_start:
{
lean_object* v___x_4975_; 
v___x_4975_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(v_cctx_4965_, v_env_4966_, v_act_4967_, v_d_4968_, v_cacheRef_4969_, v_tree_4970_, v_mname_4971_, v_mdata_4972_, v_i_4973_);
return v___x_4975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule___boxed(lean_object* v_00_u03b1_4976_, lean_object* v_cctx_4977_, lean_object* v_env_4978_, lean_object* v_act_4979_, lean_object* v_d_4980_, lean_object* v_cacheRef_4981_, lean_object* v_tree_4982_, lean_object* v_mname_4983_, lean_object* v_mdata_4984_, lean_object* v_i_4985_, lean_object* v_a_4986_){
_start:
{
lean_object* v_res_4987_; 
v_res_4987_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule(v_00_u03b1_4976_, v_cctx_4977_, v_env_4978_, v_act_4979_, v_d_4980_, v_cacheRef_4981_, v_tree_4982_, v_mname_4983_, v_mdata_4984_, v_i_4985_);
lean_dec_ref(v_mdata_4984_);
lean_dec(v_cacheRef_4981_);
lean_dec(v_d_4980_);
return v_res_4987_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg(lean_object* v_cctx_4988_, lean_object* v_env_4989_, lean_object* v_act_4990_, lean_object* v_d_4991_, lean_object* v_cacheRef_4992_, lean_object* v_tree_4993_, lean_object* v_start_4994_, lean_object* v_stop_4995_){
_start:
{
uint8_t v___x_4997_; 
v___x_4997_ = lean_nat_dec_lt(v_start_4994_, v_stop_4995_);
if (v___x_4997_ == 0)
{
lean_object* v___x_4998_; 
lean_dec(v_start_4994_);
lean_dec_ref(v_act_4990_);
lean_dec_ref(v_env_4989_);
lean_dec_ref(v_cctx_4988_);
v___x_4998_ = l_Lean_Meta_LazyDiscrTree_toFlat___redArg(v_d_4991_, v_tree_4993_);
return v___x_4998_;
}
else
{
lean_object* v___x_4999_; lean_object* v_moduleNames_5000_; lean_object* v_moduleData_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; lean_object* v_mname_5004_; lean_object* v_mdata_5005_; lean_object* v___x_5006_; lean_object* v___x_5007_; lean_object* v___x_5008_; lean_object* v___x_5009_; 
v___x_4999_ = l_Lean_Environment_header(v_env_4989_);
v_moduleNames_5000_ = lean_ctor_get(v___x_4999_, 4);
lean_inc_ref(v_moduleNames_5000_);
v_moduleData_5001_ = lean_ctor_get(v___x_4999_, 7);
lean_inc_ref(v_moduleData_5001_);
lean_dec_ref(v___x_4999_);
v___x_5002_ = lean_box(0);
v___x_5003_ = l_Lean_instInhabitedModuleData_default;
v_mname_5004_ = lean_array_get(v___x_5002_, v_moduleNames_5000_, v_start_4994_);
lean_dec_ref(v_moduleNames_5000_);
v_mdata_5005_ = lean_array_get(v___x_5003_, v_moduleData_5001_, v_start_4994_);
lean_dec_ref(v_moduleData_5001_);
v___x_5006_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_act_4990_);
lean_inc_ref(v_env_4989_);
lean_inc_ref(v_cctx_4988_);
v___x_5007_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(v_cctx_4988_, v_env_4989_, v_act_4990_, v_d_4991_, v_cacheRef_4992_, v_tree_4993_, v_mname_5004_, v_mdata_5005_, v___x_5006_);
lean_dec(v_mdata_5005_);
v___x_5008_ = lean_unsigned_to_nat(1u);
v___x_5009_ = lean_nat_add(v_start_4994_, v___x_5008_);
lean_dec(v_start_4994_);
v_tree_4993_ = v___x_5007_;
v_start_4994_ = v___x_5009_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg___boxed(lean_object* v_cctx_5011_, lean_object* v_env_5012_, lean_object* v_act_5013_, lean_object* v_d_5014_, lean_object* v_cacheRef_5015_, lean_object* v_tree_5016_, lean_object* v_start_5017_, lean_object* v_stop_5018_, lean_object* v_a_5019_){
_start:
{
lean_object* v_res_5020_; 
v_res_5020_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg(v_cctx_5011_, v_env_5012_, v_act_5013_, v_d_5014_, v_cacheRef_5015_, v_tree_5016_, v_start_5017_, v_stop_5018_);
lean_dec(v_stop_5018_);
lean_dec(v_cacheRef_5015_);
lean_dec(v_d_5014_);
return v_res_5020_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go(lean_object* v_00_u03b1_5021_, lean_object* v_cctx_5022_, lean_object* v_env_5023_, lean_object* v_act_5024_, lean_object* v_d_5025_, lean_object* v_cacheRef_5026_, lean_object* v_tree_5027_, lean_object* v_start_5028_, lean_object* v_stop_5029_){
_start:
{
lean_object* v___x_5031_; 
v___x_5031_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg(v_cctx_5022_, v_env_5023_, v_act_5024_, v_d_5025_, v_cacheRef_5026_, v_tree_5027_, v_start_5028_, v_stop_5029_);
return v___x_5031_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___boxed(lean_object* v_00_u03b1_5032_, lean_object* v_cctx_5033_, lean_object* v_env_5034_, lean_object* v_act_5035_, lean_object* v_d_5036_, lean_object* v_cacheRef_5037_, lean_object* v_tree_5038_, lean_object* v_start_5039_, lean_object* v_stop_5040_, lean_object* v_a_5041_){
_start:
{
lean_object* v_res_5042_; 
v_res_5042_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go(v_00_u03b1_5032_, v_cctx_5033_, v_env_5034_, v_act_5035_, v_d_5036_, v_cacheRef_5037_, v_tree_5038_, v_start_5039_, v_stop_5040_);
lean_dec(v_stop_5040_);
lean_dec(v_cacheRef_5037_);
lean_dec(v_d_5036_);
return v_res_5042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___redArg(lean_object* v_cctx_5043_, lean_object* v_ngen_5044_, lean_object* v_env_5045_, lean_object* v_act_5046_, lean_object* v_start_5047_, lean_object* v_stop_5048_){
_start:
{
lean_object* v___x_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; 
v___x_5050_ = l_Lean_Meta_LazyDiscrTree_Cache_empty(v_ngen_5044_);
v___x_5051_ = lean_st_mk_ref(v___x_5050_);
v___x_5052_ = l_Lean_Meta_LazyDiscrTree_ImportData_new();
v___x_5053_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1);
v___x_5054_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg(v_cctx_5043_, v_env_5045_, v_act_5046_, v___x_5052_, v___x_5051_, v___x_5053_, v_start_5047_, v_stop_5048_);
lean_dec(v___x_5051_);
lean_dec(v___x_5052_);
return v___x_5054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___redArg___boxed(lean_object* v_cctx_5055_, lean_object* v_ngen_5056_, lean_object* v_env_5057_, lean_object* v_act_5058_, lean_object* v_start_5059_, lean_object* v_stop_5060_, lean_object* v_a_5061_){
_start:
{
lean_object* v_res_5062_; 
v_res_5062_ = l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___redArg(v_cctx_5055_, v_ngen_5056_, v_env_5057_, v_act_5058_, v_start_5059_, v_stop_5060_);
lean_dec(v_stop_5060_);
return v_res_5062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq(lean_object* v_00_u03b1_5063_, lean_object* v_cctx_5064_, lean_object* v_ngen_5065_, lean_object* v_env_5066_, lean_object* v_act_5067_, lean_object* v_start_5068_, lean_object* v_stop_5069_){
_start:
{
lean_object* v___x_5071_; 
v___x_5071_ = l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___redArg(v_cctx_5064_, v_ngen_5065_, v_env_5066_, v_act_5067_, v_start_5068_, v_stop_5069_);
return v___x_5071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed(lean_object* v_00_u03b1_5072_, lean_object* v_cctx_5073_, lean_object* v_ngen_5074_, lean_object* v_env_5075_, lean_object* v_act_5076_, lean_object* v_start_5077_, lean_object* v_stop_5078_, lean_object* v_a_5079_){
_start:
{
lean_object* v_res_5080_; 
v_res_5080_ = l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq(v_00_u03b1_5072_, v_cctx_5073_, v_ngen_5074_, v_env_5075_, v_act_5076_, v_start_5077_, v_stop_5078_);
lean_dec(v_stop_5078_);
return v_res_5080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___redArg___lam__0(lean_object* v_inst_5081_, lean_object* v_x1_5082_, lean_object* v_x2_5083_){
_start:
{
lean_object* v___x_5084_; lean_object* v___x_5085_; 
v___x_5084_ = lean_task_get_own(v_x2_5083_);
v___x_5085_ = lean_apply_2(v_inst_5081_, v_x1_5082_, v___x_5084_);
return v___x_5085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___redArg(lean_object* v_inst_5086_, lean_object* v_z_5087_, lean_object* v_tasks_5088_){
_start:
{
lean_object* v___x_5089_; lean_object* v___x_5090_; lean_object* v___x_5091_; uint8_t v___x_5092_; 
v___x_5089_ = lean_unsigned_to_nat(0u);
v___x_5090_ = lean_array_get_size(v_tasks_5088_);
v___x_5091_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__9));
v___x_5092_ = lean_nat_dec_lt(v___x_5089_, v___x_5090_);
if (v___x_5092_ == 0)
{
lean_dec_ref(v_tasks_5088_);
lean_dec(v_inst_5086_);
return v_z_5087_;
}
else
{
lean_object* v___f_5093_; size_t v___x_5094_; size_t v___x_5095_; lean_object* v___x_5096_; 
v___f_5093_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_combineGet___redArg___lam__0), 3, 1);
lean_closure_set(v___f_5093_, 0, v_inst_5086_);
v___x_5094_ = ((size_t)0ULL);
v___x_5095_ = lean_usize_of_nat(v___x_5090_);
v___x_5096_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_5091_, v___f_5093_, v_tasks_5088_, v___x_5094_, v___x_5095_, v_z_5087_);
return v___x_5096_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet(lean_object* v_00_u03b1_5097_, lean_object* v_inst_5098_, lean_object* v_z_5099_, lean_object* v_tasks_5100_){
_start:
{
lean_object* v___x_5101_; 
v___x_5101_ = l_Lean_Meta_LazyDiscrTree_combineGet___redArg(v_inst_5098_, v_z_5099_, v_tasks_5100_);
return v___x_5101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg___lam__0(lean_object* v_toPure_5102_, lean_object* v___x_5103_, lean_object* v_____r_5104_){
_start:
{
lean_object* v___x_5105_; 
v___x_5105_ = lean_apply_2(v_toPure_5102_, lean_box(0), v___x_5103_);
return v___x_5105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg___lam__1(lean_object* v_toPure_5106_, lean_object* v_setNGen_5107_, lean_object* v_toBind_5108_, lean_object* v_ngen_5109_){
_start:
{
lean_object* v_namePrefix_5110_; lean_object* v_idx_5111_; lean_object* v___x_5113_; uint8_t v_isShared_5114_; uint8_t v_isSharedCheck_5125_; 
v_namePrefix_5110_ = lean_ctor_get(v_ngen_5109_, 0);
v_idx_5111_ = lean_ctor_get(v_ngen_5109_, 1);
v_isSharedCheck_5125_ = !lean_is_exclusive(v_ngen_5109_);
if (v_isSharedCheck_5125_ == 0)
{
v___x_5113_ = v_ngen_5109_;
v_isShared_5114_ = v_isSharedCheck_5125_;
goto v_resetjp_5112_;
}
else
{
lean_inc(v_idx_5111_);
lean_inc(v_namePrefix_5110_);
lean_dec(v_ngen_5109_);
v___x_5113_ = lean_box(0);
v_isShared_5114_ = v_isSharedCheck_5125_;
goto v_resetjp_5112_;
}
v_resetjp_5112_:
{
lean_object* v___x_5115_; lean_object* v___x_5116_; lean_object* v___x_5118_; 
lean_inc(v_idx_5111_);
lean_inc(v_namePrefix_5110_);
v___x_5115_ = l_Lean_Name_num___override(v_namePrefix_5110_, v_idx_5111_);
v___x_5116_ = lean_unsigned_to_nat(1u);
if (v_isShared_5114_ == 0)
{
lean_ctor_set(v___x_5113_, 1, v___x_5116_);
lean_ctor_set(v___x_5113_, 0, v___x_5115_);
v___x_5118_ = v___x_5113_;
goto v_reusejp_5117_;
}
else
{
lean_object* v_reuseFailAlloc_5124_; 
v_reuseFailAlloc_5124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5124_, 0, v___x_5115_);
lean_ctor_set(v_reuseFailAlloc_5124_, 1, v___x_5116_);
v___x_5118_ = v_reuseFailAlloc_5124_;
goto v_reusejp_5117_;
}
v_reusejp_5117_:
{
lean_object* v___f_5119_; lean_object* v___x_5120_; lean_object* v___x_5121_; lean_object* v___x_5122_; lean_object* v___x_5123_; 
v___f_5119_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5119_, 0, v_toPure_5106_);
lean_closure_set(v___f_5119_, 1, v___x_5118_);
v___x_5120_ = lean_nat_add(v_idx_5111_, v___x_5116_);
lean_dec(v_idx_5111_);
v___x_5121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5121_, 0, v_namePrefix_5110_);
lean_ctor_set(v___x_5121_, 1, v___x_5120_);
v___x_5122_ = lean_apply_1(v_setNGen_5107_, v___x_5121_);
v___x_5123_ = lean_apply_4(v_toBind_5108_, lean_box(0), lean_box(0), v___x_5122_, v___f_5119_);
return v___x_5123_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg(lean_object* v_inst_5126_, lean_object* v_inst_5127_){
_start:
{
lean_object* v_toApplicative_5128_; lean_object* v_toBind_5129_; lean_object* v_getNGen_5130_; lean_object* v_setNGen_5131_; lean_object* v_toPure_5132_; lean_object* v___f_5133_; lean_object* v___x_5134_; 
v_toApplicative_5128_ = lean_ctor_get(v_inst_5126_, 0);
lean_inc_ref(v_toApplicative_5128_);
v_toBind_5129_ = lean_ctor_get(v_inst_5126_, 1);
lean_inc_n(v_toBind_5129_, 2);
lean_dec_ref(v_inst_5126_);
v_getNGen_5130_ = lean_ctor_get(v_inst_5127_, 0);
lean_inc(v_getNGen_5130_);
v_setNGen_5131_ = lean_ctor_get(v_inst_5127_, 1);
lean_inc(v_setNGen_5131_);
lean_dec_ref(v_inst_5127_);
v_toPure_5132_ = lean_ctor_get(v_toApplicative_5128_, 1);
lean_inc(v_toPure_5132_);
lean_dec_ref(v_toApplicative_5128_);
v___f_5133_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg___lam__1), 4, 3);
lean_closure_set(v___f_5133_, 0, v_toPure_5132_);
lean_closure_set(v___f_5133_, 1, v_setNGen_5131_);
lean_closure_set(v___f_5133_, 2, v_toBind_5129_);
v___x_5134_ = lean_apply_4(v_toBind_5129_, lean_box(0), lean_box(0), v_getNGen_5130_, v___f_5133_);
return v___x_5134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen(lean_object* v_M_5135_, lean_object* v_inst_5136_, lean_object* v_inst_5137_){
_start:
{
lean_object* v___x_5138_; 
v___x_5138_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg(v_inst_5136_, v_inst_5137_);
return v___x_5138_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg(lean_object* v_cctx_5139_, lean_object* v_env_5140_, lean_object* v_modName_5141_, lean_object* v_d_5142_, lean_object* v_val_5143_, lean_object* v_act_5144_, lean_object* v_as_5145_, size_t v_sz_5146_, size_t v_i_5147_, lean_object* v_b_5148_){
_start:
{
uint8_t v___x_5150_; 
v___x_5150_ = lean_usize_dec_lt(v_i_5147_, v_sz_5146_);
if (v___x_5150_ == 0)
{
lean_dec_ref(v_act_5144_);
lean_dec(v_modName_5141_);
lean_dec_ref(v_env_5140_);
lean_dec_ref(v_cctx_5139_);
return v_b_5148_;
}
else
{
lean_object* v_a_5151_; lean_object* v___x_5152_; size_t v___x_5153_; size_t v___x_5154_; 
v_a_5151_ = lean_array_uget_borrowed(v_as_5145_, v_i_5147_);
lean_inc(v_a_5151_);
lean_inc_ref(v_act_5144_);
lean_inc(v_modName_5141_);
lean_inc_ref(v_env_5140_);
lean_inc_ref(v_cctx_5139_);
v___x_5152_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_5139_, v_env_5140_, v_modName_5141_, v_d_5142_, v_val_5143_, v_b_5148_, v_act_5144_, v_a_5151_);
v___x_5153_ = ((size_t)1ULL);
v___x_5154_ = lean_usize_add(v_i_5147_, v___x_5153_);
v_i_5147_ = v___x_5154_;
v_b_5148_ = v___x_5152_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg___boxed(lean_object* v_cctx_5156_, lean_object* v_env_5157_, lean_object* v_modName_5158_, lean_object* v_d_5159_, lean_object* v_val_5160_, lean_object* v_act_5161_, lean_object* v_as_5162_, lean_object* v_sz_5163_, lean_object* v_i_5164_, lean_object* v_b_5165_, lean_object* v___y_5166_){
_start:
{
size_t v_sz_boxed_5167_; size_t v_i_boxed_5168_; lean_object* v_res_5169_; 
v_sz_boxed_5167_ = lean_unbox_usize(v_sz_5163_);
lean_dec(v_sz_5163_);
v_i_boxed_5168_ = lean_unbox_usize(v_i_5164_);
lean_dec(v_i_5164_);
v_res_5169_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg(v_cctx_5156_, v_env_5157_, v_modName_5158_, v_d_5159_, v_val_5160_, v_act_5161_, v_as_5162_, v_sz_boxed_5167_, v_i_boxed_5168_, v_b_5165_);
lean_dec_ref(v_as_5162_);
lean_dec(v_val_5160_);
lean_dec(v_d_5159_);
return v_res_5169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(lean_object* v_cctx_5170_, lean_object* v_ngen_5171_, lean_object* v_env_5172_, lean_object* v_d_5173_, lean_object* v_act_5174_){
_start:
{
lean_object* v___x_5176_; lean_object* v_mainModule_5177_; lean_object* v___x_5178_; lean_object* v___x_5179_; lean_object* v___x_5180_; uint8_t v___x_5181_; lean_object* v___x_5182_; size_t v_sz_5183_; size_t v___x_5184_; lean_object* v___x_5185_; 
v___x_5176_ = l_Lean_Environment_header(v_env_5172_);
v_mainModule_5177_ = lean_ctor_get(v___x_5176_, 0);
lean_inc(v_mainModule_5177_);
lean_dec_ref(v___x_5176_);
v___x_5178_ = l_Lean_Meta_LazyDiscrTree_Cache_empty(v_ngen_5171_);
v___x_5179_ = lean_st_mk_ref(v___x_5178_);
v___x_5180_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1);
v___x_5181_ = 1;
v___x_5182_ = l_Lean_Environment_getLocalConstantInfos(v_env_5172_, v___x_5181_);
v_sz_5183_ = lean_array_size(v___x_5182_);
v___x_5184_ = ((size_t)0ULL);
v___x_5185_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg(v_cctx_5170_, v_env_5172_, v_mainModule_5177_, v_d_5173_, v___x_5179_, v_act_5174_, v___x_5182_, v_sz_5183_, v___x_5184_, v___x_5180_);
lean_dec_ref(v___x_5182_);
lean_dec(v___x_5179_);
return v___x_5185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg___boxed(lean_object* v_cctx_5186_, lean_object* v_ngen_5187_, lean_object* v_env_5188_, lean_object* v_d_5189_, lean_object* v_act_5190_, lean_object* v_a_5191_){
_start:
{
lean_object* v_res_5192_; 
v_res_5192_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(v_cctx_5186_, v_ngen_5187_, v_env_5188_, v_d_5189_, v_act_5190_);
lean_dec(v_d_5189_);
return v_res_5192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree(lean_object* v_00_u03b1_5193_, lean_object* v_cctx_5194_, lean_object* v_ngen_5195_, lean_object* v_env_5196_, lean_object* v_d_5197_, lean_object* v_act_5198_){
_start:
{
lean_object* v___x_5200_; 
v___x_5200_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(v_cctx_5194_, v_ngen_5195_, v_env_5196_, v_d_5197_, v_act_5198_);
return v___x_5200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___boxed(lean_object* v_00_u03b1_5201_, lean_object* v_cctx_5202_, lean_object* v_ngen_5203_, lean_object* v_env_5204_, lean_object* v_d_5205_, lean_object* v_act_5206_, lean_object* v_a_5207_){
_start:
{
lean_object* v_res_5208_; 
v_res_5208_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree(v_00_u03b1_5201_, v_cctx_5202_, v_ngen_5203_, v_env_5204_, v_d_5205_, v_act_5206_);
lean_dec(v_d_5205_);
return v_res_5208_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0(lean_object* v_00_u03b1_5209_, lean_object* v_cctx_5210_, lean_object* v_env_5211_, lean_object* v_modName_5212_, lean_object* v_d_5213_, lean_object* v_val_5214_, lean_object* v_act_5215_, lean_object* v_as_5216_, size_t v_sz_5217_, size_t v_i_5218_, lean_object* v_b_5219_){
_start:
{
lean_object* v___x_5221_; 
v___x_5221_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg(v_cctx_5210_, v_env_5211_, v_modName_5212_, v_d_5213_, v_val_5214_, v_act_5215_, v_as_5216_, v_sz_5217_, v_i_5218_, v_b_5219_);
return v___x_5221_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___boxed(lean_object* v_00_u03b1_5222_, lean_object* v_cctx_5223_, lean_object* v_env_5224_, lean_object* v_modName_5225_, lean_object* v_d_5226_, lean_object* v_val_5227_, lean_object* v_act_5228_, lean_object* v_as_5229_, lean_object* v_sz_5230_, lean_object* v_i_5231_, lean_object* v_b_5232_, lean_object* v___y_5233_){
_start:
{
size_t v_sz_boxed_5234_; size_t v_i_boxed_5235_; lean_object* v_res_5236_; 
v_sz_boxed_5234_ = lean_unbox_usize(v_sz_5230_);
lean_dec(v_sz_5230_);
v_i_boxed_5235_ = lean_unbox_usize(v_i_5231_);
lean_dec(v_i_5231_);
v_res_5236_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0(v_00_u03b1_5222_, v_cctx_5223_, v_env_5224_, v_modName_5225_, v_d_5226_, v_val_5227_, v_act_5228_, v_as_5229_, v_sz_boxed_5234_, v_i_boxed_5235_, v_b_5232_);
lean_dec_ref(v_as_5229_);
lean_dec(v_val_5227_);
lean_dec(v_d_5226_);
return v_res_5236_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(lean_object* v_x_5237_, lean_object* v_x_5238_, lean_object* v___y_5239_, lean_object* v___y_5240_, lean_object* v___y_5241_, lean_object* v___y_5242_){
_start:
{
if (lean_obj_tag(v_x_5238_) == 0)
{
lean_object* v___x_5244_; 
v___x_5244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5244_, 0, v_x_5237_);
return v___x_5244_;
}
else
{
lean_object* v_head_5245_; lean_object* v_tail_5246_; lean_object* v___x_5247_; 
v_head_5245_ = lean_ctor_get(v_x_5238_, 0);
lean_inc(v_head_5245_);
v_tail_5246_ = lean_ctor_get(v_x_5238_, 1);
lean_inc(v_tail_5246_);
lean_dec_ref_known(v_x_5238_, 2);
v___x_5247_ = l_Lean_Meta_LazyDiscrTree_dropKey___redArg(v_x_5237_, v_head_5245_, v___y_5239_, v___y_5240_, v___y_5241_, v___y_5242_);
if (lean_obj_tag(v___x_5247_) == 0)
{
lean_object* v_a_5248_; 
v_a_5248_ = lean_ctor_get(v___x_5247_, 0);
lean_inc(v_a_5248_);
lean_dec_ref_known(v___x_5247_, 1);
v_x_5237_ = v_a_5248_;
v_x_5238_ = v_tail_5246_;
goto _start;
}
else
{
lean_dec(v_tail_5246_);
return v___x_5247_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg___boxed(lean_object* v_x_5250_, lean_object* v_x_5251_, lean_object* v___y_5252_, lean_object* v___y_5253_, lean_object* v___y_5254_, lean_object* v___y_5255_, lean_object* v___y_5256_){
_start:
{
lean_object* v_res_5257_; 
v_res_5257_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_x_5250_, v_x_5251_, v___y_5252_, v___y_5253_, v___y_5254_, v___y_5255_);
lean_dec(v___y_5255_);
lean_dec_ref(v___y_5254_);
lean_dec(v___y_5253_);
lean_dec_ref(v___y_5252_);
return v_res_5257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys___redArg(lean_object* v_t_5258_, lean_object* v_keys_5259_, lean_object* v_a_5260_, lean_object* v_a_5261_, lean_object* v_a_5262_, lean_object* v_a_5263_){
_start:
{
lean_object* v___x_5265_; 
v___x_5265_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_t_5258_, v_keys_5259_, v_a_5260_, v_a_5261_, v_a_5262_, v_a_5263_);
return v___x_5265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys___redArg___boxed(lean_object* v_t_5266_, lean_object* v_keys_5267_, lean_object* v_a_5268_, lean_object* v_a_5269_, lean_object* v_a_5270_, lean_object* v_a_5271_, lean_object* v_a_5272_){
_start:
{
lean_object* v_res_5273_; 
v_res_5273_ = l_Lean_Meta_LazyDiscrTree_dropKeys___redArg(v_t_5266_, v_keys_5267_, v_a_5268_, v_a_5269_, v_a_5270_, v_a_5271_);
lean_dec(v_a_5271_);
lean_dec_ref(v_a_5270_);
lean_dec(v_a_5269_);
lean_dec_ref(v_a_5268_);
return v_res_5273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys(lean_object* v_00_u03b1_5274_, lean_object* v_t_5275_, lean_object* v_keys_5276_, lean_object* v_a_5277_, lean_object* v_a_5278_, lean_object* v_a_5279_, lean_object* v_a_5280_){
_start:
{
lean_object* v___x_5282_; 
v___x_5282_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_t_5275_, v_keys_5276_, v_a_5277_, v_a_5278_, v_a_5279_, v_a_5280_);
return v___x_5282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys___boxed(lean_object* v_00_u03b1_5283_, lean_object* v_t_5284_, lean_object* v_keys_5285_, lean_object* v_a_5286_, lean_object* v_a_5287_, lean_object* v_a_5288_, lean_object* v_a_5289_, lean_object* v_a_5290_){
_start:
{
lean_object* v_res_5291_; 
v_res_5291_ = l_Lean_Meta_LazyDiscrTree_dropKeys(v_00_u03b1_5283_, v_t_5284_, v_keys_5285_, v_a_5286_, v_a_5287_, v_a_5288_, v_a_5289_);
lean_dec(v_a_5289_);
lean_dec_ref(v_a_5288_);
lean_dec(v_a_5287_);
lean_dec_ref(v_a_5286_);
return v_res_5291_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0(lean_object* v_00_u03b1_5292_, lean_object* v_x_5293_, lean_object* v_x_5294_, lean_object* v___y_5295_, lean_object* v___y_5296_, lean_object* v___y_5297_, lean_object* v___y_5298_){
_start:
{
lean_object* v___x_5300_; 
v___x_5300_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_x_5293_, v_x_5294_, v___y_5295_, v___y_5296_, v___y_5297_, v___y_5298_);
return v___x_5300_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___boxed(lean_object* v_00_u03b1_5301_, lean_object* v_x_5302_, lean_object* v_x_5303_, lean_object* v___y_5304_, lean_object* v___y_5305_, lean_object* v___y_5306_, lean_object* v___y_5307_, lean_object* v___y_5308_){
_start:
{
lean_object* v_res_5309_; 
v_res_5309_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0(v_00_u03b1_5301_, v_x_5302_, v_x_5303_, v___y_5304_, v___y_5305_, v___y_5306_, v___y_5307_);
lean_dec(v___y_5307_);
lean_dec_ref(v___y_5306_);
lean_dec(v___y_5305_);
lean_dec_ref(v___y_5304_);
return v_res_5309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(lean_object* v_as_5310_, size_t v_sz_5311_, size_t v_i_5312_, lean_object* v_b_5313_, lean_object* v___y_5314_, lean_object* v___y_5315_, lean_object* v___y_5316_, lean_object* v___y_5317_, lean_object* v___y_5318_){
_start:
{
uint8_t v___x_5320_; 
v___x_5320_ = lean_usize_dec_lt(v_i_5312_, v_sz_5311_);
if (v___x_5320_ == 0)
{
lean_object* v___x_5321_; 
v___x_5321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5321_, 0, v_b_5313_);
return v___x_5321_;
}
else
{
lean_object* v_a_5322_; lean_object* v___x_5323_; 
v_a_5322_ = lean_array_uget_borrowed(v_as_5310_, v_i_5312_);
v___x_5323_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(v_a_5322_, v_b_5313_, v___y_5314_, v___y_5315_, v___y_5316_, v___y_5317_, v___y_5318_);
if (lean_obj_tag(v___x_5323_) == 0)
{
lean_object* v_a_5324_; lean_object* v___x_5326_; uint8_t v_isShared_5327_; uint8_t v_isSharedCheck_5336_; 
v_a_5324_ = lean_ctor_get(v___x_5323_, 0);
v_isSharedCheck_5336_ = !lean_is_exclusive(v___x_5323_);
if (v_isSharedCheck_5336_ == 0)
{
v___x_5326_ = v___x_5323_;
v_isShared_5327_ = v_isSharedCheck_5336_;
goto v_resetjp_5325_;
}
else
{
lean_inc(v_a_5324_);
lean_dec(v___x_5323_);
v___x_5326_ = lean_box(0);
v_isShared_5327_ = v_isSharedCheck_5336_;
goto v_resetjp_5325_;
}
v_resetjp_5325_:
{
if (lean_obj_tag(v_a_5324_) == 0)
{
lean_object* v_a_5328_; lean_object* v___x_5330_; 
v_a_5328_ = lean_ctor_get(v_a_5324_, 0);
lean_inc(v_a_5328_);
lean_dec_ref_known(v_a_5324_, 1);
if (v_isShared_5327_ == 0)
{
lean_ctor_set(v___x_5326_, 0, v_a_5328_);
v___x_5330_ = v___x_5326_;
goto v_reusejp_5329_;
}
else
{
lean_object* v_reuseFailAlloc_5331_; 
v_reuseFailAlloc_5331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5331_, 0, v_a_5328_);
v___x_5330_ = v_reuseFailAlloc_5331_;
goto v_reusejp_5329_;
}
v_reusejp_5329_:
{
return v___x_5330_;
}
}
else
{
lean_object* v_a_5332_; size_t v___x_5333_; size_t v___x_5334_; 
lean_del_object(v___x_5326_);
v_a_5332_ = lean_ctor_get(v_a_5324_, 0);
lean_inc(v_a_5332_);
lean_dec_ref_known(v_a_5324_, 1);
v___x_5333_ = ((size_t)1ULL);
v___x_5334_ = lean_usize_add(v_i_5312_, v___x_5333_);
v_i_5312_ = v___x_5334_;
v_b_5313_ = v_a_5332_;
goto _start;
}
}
}
else
{
lean_object* v_a_5337_; lean_object* v___x_5339_; uint8_t v_isShared_5340_; uint8_t v_isSharedCheck_5344_; 
v_a_5337_ = lean_ctor_get(v___x_5323_, 0);
v_isSharedCheck_5344_ = !lean_is_exclusive(v___x_5323_);
if (v_isSharedCheck_5344_ == 0)
{
v___x_5339_ = v___x_5323_;
v_isShared_5340_ = v_isSharedCheck_5344_;
goto v_resetjp_5338_;
}
else
{
lean_inc(v_a_5337_);
lean_dec(v___x_5323_);
v___x_5339_ = lean_box(0);
v_isShared_5340_ = v_isSharedCheck_5344_;
goto v_resetjp_5338_;
}
v_resetjp_5338_:
{
lean_object* v___x_5342_; 
if (v_isShared_5340_ == 0)
{
v___x_5342_ = v___x_5339_;
goto v_reusejp_5341_;
}
else
{
lean_object* v_reuseFailAlloc_5343_; 
v_reuseFailAlloc_5343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5343_, 0, v_a_5337_);
v___x_5342_ = v_reuseFailAlloc_5343_;
goto v_reusejp_5341_;
}
v_reusejp_5341_:
{
return v___x_5342_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(lean_object* v_next_5345_, lean_object* v_a_5346_, lean_object* v_a_5347_, lean_object* v_a_5348_, lean_object* v_a_5349_, lean_object* v_a_5350_){
_start:
{
lean_object* v___x_5352_; uint8_t v___x_5353_; 
v___x_5352_ = lean_unsigned_to_nat(0u);
v___x_5353_ = lean_nat_dec_eq(v_next_5345_, v___x_5352_);
if (v___x_5353_ == 0)
{
lean_object* v___x_5354_; 
v___x_5354_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_next_5345_, v_a_5346_, v_a_5347_, v_a_5348_, v_a_5349_, v_a_5350_);
if (lean_obj_tag(v___x_5354_) == 0)
{
lean_object* v_a_5355_; lean_object* v_snd_5356_; lean_object* v_fst_5357_; lean_object* v_fst_5358_; lean_object* v_snd_5359_; lean_object* v___x_5360_; 
v_a_5355_ = lean_ctor_get(v___x_5354_, 0);
lean_inc(v_a_5355_);
lean_dec_ref_known(v___x_5354_, 1);
v_snd_5356_ = lean_ctor_get(v_a_5355_, 1);
lean_inc(v_snd_5356_);
v_fst_5357_ = lean_ctor_get(v_a_5355_, 0);
lean_inc(v_fst_5357_);
lean_dec(v_a_5355_);
v_fst_5358_ = lean_ctor_get(v_snd_5356_, 0);
lean_inc(v_fst_5358_);
v_snd_5359_ = lean_ctor_get(v_snd_5356_, 1);
lean_inc(v_snd_5359_);
lean_dec(v_snd_5356_);
v___x_5360_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_fst_5358_, v_a_5346_, v_a_5347_, v_a_5348_, v_a_5349_, v_a_5350_);
if (lean_obj_tag(v___x_5360_) == 0)
{
lean_object* v_a_5361_; lean_object* v_buckets_5362_; lean_object* v___x_5363_; size_t v_sz_5364_; size_t v___x_5365_; lean_object* v___x_5366_; 
v_a_5361_ = lean_ctor_get(v___x_5360_, 0);
lean_inc(v_a_5361_);
lean_dec_ref_known(v___x_5360_, 1);
v_buckets_5362_ = lean_ctor_get(v_snd_5359_, 1);
v___x_5363_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v_sz_5364_ = lean_array_size(v_buckets_5362_);
v___x_5365_ = ((size_t)0ULL);
v___x_5366_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(v_buckets_5362_, v_sz_5364_, v___x_5365_, v___x_5363_, v_a_5346_, v_a_5347_, v_a_5348_, v_a_5349_, v_a_5350_);
if (lean_obj_tag(v___x_5366_) == 0)
{
lean_object* v_a_5367_; lean_object* v___x_5369_; uint8_t v_isShared_5370_; uint8_t v_isSharedCheck_5380_; 
v_a_5367_ = lean_ctor_get(v___x_5366_, 0);
v_isSharedCheck_5380_ = !lean_is_exclusive(v___x_5366_);
if (v_isSharedCheck_5380_ == 0)
{
v___x_5369_ = v___x_5366_;
v_isShared_5370_ = v_isSharedCheck_5380_;
goto v_resetjp_5368_;
}
else
{
lean_inc(v_a_5367_);
lean_dec(v___x_5366_);
v___x_5369_ = lean_box(0);
v_isShared_5370_ = v_isSharedCheck_5380_;
goto v_resetjp_5368_;
}
v_resetjp_5368_:
{
lean_object* v___x_5371_; lean_object* v___x_5372_; lean_object* v___x_5373_; lean_object* v___x_5374_; lean_object* v___x_5375_; lean_object* v___x_5376_; lean_object* v___x_5378_; 
v___x_5371_ = lean_st_ref_take(v_a_5346_);
v___x_5372_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5372_, 0, v___x_5363_);
lean_ctor_set(v___x_5372_, 1, v_fst_5358_);
lean_ctor_set(v___x_5372_, 2, v_snd_5359_);
lean_ctor_set(v___x_5372_, 3, v___x_5363_);
v___x_5373_ = lean_array_set(v___x_5371_, v_next_5345_, v___x_5372_);
v___x_5374_ = lean_st_ref_put(v_a_5346_, v___x_5373_);
v___x_5375_ = l_Array_append___redArg(v_fst_5357_, v_a_5361_);
lean_dec(v_a_5361_);
v___x_5376_ = l_Array_append___redArg(v___x_5375_, v_a_5367_);
lean_dec(v_a_5367_);
if (v_isShared_5370_ == 0)
{
lean_ctor_set(v___x_5369_, 0, v___x_5376_);
v___x_5378_ = v___x_5369_;
goto v_reusejp_5377_;
}
else
{
lean_object* v_reuseFailAlloc_5379_; 
v_reuseFailAlloc_5379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5379_, 0, v___x_5376_);
v___x_5378_ = v_reuseFailAlloc_5379_;
goto v_reusejp_5377_;
}
v_reusejp_5377_:
{
return v___x_5378_;
}
}
}
else
{
lean_dec(v_a_5361_);
lean_dec(v_snd_5359_);
lean_dec(v_fst_5358_);
lean_dec(v_fst_5357_);
return v___x_5366_;
}
}
else
{
lean_dec(v_snd_5359_);
lean_dec(v_fst_5358_);
lean_dec(v_fst_5357_);
return v___x_5360_;
}
}
else
{
lean_object* v_a_5381_; lean_object* v___x_5383_; uint8_t v_isShared_5384_; uint8_t v_isSharedCheck_5388_; 
v_a_5381_ = lean_ctor_get(v___x_5354_, 0);
v_isSharedCheck_5388_ = !lean_is_exclusive(v___x_5354_);
if (v_isSharedCheck_5388_ == 0)
{
v___x_5383_ = v___x_5354_;
v_isShared_5384_ = v_isSharedCheck_5388_;
goto v_resetjp_5382_;
}
else
{
lean_inc(v_a_5381_);
lean_dec(v___x_5354_);
v___x_5383_ = lean_box(0);
v_isShared_5384_ = v_isSharedCheck_5388_;
goto v_resetjp_5382_;
}
v_resetjp_5382_:
{
lean_object* v___x_5386_; 
if (v_isShared_5384_ == 0)
{
v___x_5386_ = v___x_5383_;
goto v_reusejp_5385_;
}
else
{
lean_object* v_reuseFailAlloc_5387_; 
v_reuseFailAlloc_5387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5387_, 0, v_a_5381_);
v___x_5386_ = v_reuseFailAlloc_5387_;
goto v_reusejp_5385_;
}
v_reusejp_5385_:
{
return v___x_5386_;
}
}
}
}
else
{
lean_object* v___x_5389_; lean_object* v___x_5390_; 
v___x_5389_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___x_5390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5390_, 0, v___x_5389_);
return v___x_5390_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(lean_object* v_a_5391_, lean_object* v_a_5392_, lean_object* v___y_5393_, lean_object* v___y_5394_, lean_object* v___y_5395_, lean_object* v___y_5396_, lean_object* v___y_5397_){
_start:
{
if (lean_obj_tag(v_a_5391_) == 0)
{
lean_object* v___x_5399_; lean_object* v___x_5400_; 
v___x_5399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5399_, 0, v_a_5392_);
v___x_5400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5400_, 0, v___x_5399_);
return v___x_5400_;
}
else
{
lean_object* v_value_5401_; lean_object* v_tail_5402_; lean_object* v___x_5403_; 
v_value_5401_ = lean_ctor_get(v_a_5391_, 1);
v_tail_5402_ = lean_ctor_get(v_a_5391_, 2);
v___x_5403_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_value_5401_, v___y_5393_, v___y_5394_, v___y_5395_, v___y_5396_, v___y_5397_);
if (lean_obj_tag(v___x_5403_) == 0)
{
lean_object* v_a_5404_; lean_object* v___x_5405_; 
v_a_5404_ = lean_ctor_get(v___x_5403_, 0);
lean_inc(v_a_5404_);
lean_dec_ref_known(v___x_5403_, 1);
v___x_5405_ = l_Array_append___redArg(v_a_5392_, v_a_5404_);
lean_dec(v_a_5404_);
v_a_5391_ = v_tail_5402_;
v_a_5392_ = v___x_5405_;
goto _start;
}
else
{
lean_object* v_a_5407_; lean_object* v___x_5409_; uint8_t v_isShared_5410_; uint8_t v_isSharedCheck_5414_; 
lean_dec_ref(v_a_5392_);
v_a_5407_ = lean_ctor_get(v___x_5403_, 0);
v_isSharedCheck_5414_ = !lean_is_exclusive(v___x_5403_);
if (v_isSharedCheck_5414_ == 0)
{
v___x_5409_ = v___x_5403_;
v_isShared_5410_ = v_isSharedCheck_5414_;
goto v_resetjp_5408_;
}
else
{
lean_inc(v_a_5407_);
lean_dec(v___x_5403_);
v___x_5409_ = lean_box(0);
v_isShared_5410_ = v_isSharedCheck_5414_;
goto v_resetjp_5408_;
}
v_resetjp_5408_:
{
lean_object* v___x_5412_; 
if (v_isShared_5410_ == 0)
{
v___x_5412_ = v___x_5409_;
goto v_reusejp_5411_;
}
else
{
lean_object* v_reuseFailAlloc_5413_; 
v_reuseFailAlloc_5413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5413_, 0, v_a_5407_);
v___x_5412_ = v_reuseFailAlloc_5413_;
goto v_reusejp_5411_;
}
v_reusejp_5411_:
{
return v___x_5412_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg___boxed(lean_object* v_a_5415_, lean_object* v_a_5416_, lean_object* v___y_5417_, lean_object* v___y_5418_, lean_object* v___y_5419_, lean_object* v___y_5420_, lean_object* v___y_5421_, lean_object* v___y_5422_){
_start:
{
lean_object* v_res_5423_; 
v_res_5423_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(v_a_5415_, v_a_5416_, v___y_5417_, v___y_5418_, v___y_5419_, v___y_5420_, v___y_5421_);
lean_dec(v___y_5421_);
lean_dec_ref(v___y_5420_);
lean_dec(v___y_5419_);
lean_dec_ref(v___y_5418_);
lean_dec(v___y_5417_);
lean_dec(v_a_5415_);
return v_res_5423_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg___boxed(lean_object* v_as_5424_, lean_object* v_sz_5425_, lean_object* v_i_5426_, lean_object* v_b_5427_, lean_object* v___y_5428_, lean_object* v___y_5429_, lean_object* v___y_5430_, lean_object* v___y_5431_, lean_object* v___y_5432_, lean_object* v___y_5433_){
_start:
{
size_t v_sz_boxed_5434_; size_t v_i_boxed_5435_; lean_object* v_res_5436_; 
v_sz_boxed_5434_ = lean_unbox_usize(v_sz_5425_);
lean_dec(v_sz_5425_);
v_i_boxed_5435_ = lean_unbox_usize(v_i_5426_);
lean_dec(v_i_5426_);
v_res_5436_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(v_as_5424_, v_sz_boxed_5434_, v_i_boxed_5435_, v_b_5427_, v___y_5428_, v___y_5429_, v___y_5430_, v___y_5431_, v___y_5432_);
lean_dec(v___y_5432_);
lean_dec_ref(v___y_5431_);
lean_dec(v___y_5430_);
lean_dec_ref(v___y_5429_);
lean_dec(v___y_5428_);
lean_dec_ref(v_as_5424_);
return v_res_5436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg___boxed(lean_object* v_next_5437_, lean_object* v_a_5438_, lean_object* v_a_5439_, lean_object* v_a_5440_, lean_object* v_a_5441_, lean_object* v_a_5442_, lean_object* v_a_5443_){
_start:
{
lean_object* v_res_5444_; 
v_res_5444_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_next_5437_, v_a_5438_, v_a_5439_, v_a_5440_, v_a_5441_, v_a_5442_);
lean_dec(v_a_5442_);
lean_dec_ref(v_a_5441_);
lean_dec(v_a_5440_);
lean_dec_ref(v_a_5439_);
lean_dec(v_a_5438_);
lean_dec(v_next_5437_);
return v_res_5444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux(lean_object* v_00_u03b1_5445_, lean_object* v_next_5446_, lean_object* v_a_5447_, lean_object* v_a_5448_, lean_object* v_a_5449_, lean_object* v_a_5450_, lean_object* v_a_5451_){
_start:
{
lean_object* v___x_5453_; 
v___x_5453_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_next_5446_, v_a_5447_, v_a_5448_, v_a_5449_, v_a_5450_, v_a_5451_);
return v___x_5453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___boxed(lean_object* v_00_u03b1_5454_, lean_object* v_next_5455_, lean_object* v_a_5456_, lean_object* v_a_5457_, lean_object* v_a_5458_, lean_object* v_a_5459_, lean_object* v_a_5460_, lean_object* v_a_5461_){
_start:
{
lean_object* v_res_5462_; 
v_res_5462_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux(v_00_u03b1_5454_, v_next_5455_, v_a_5456_, v_a_5457_, v_a_5458_, v_a_5459_, v_a_5460_);
lean_dec(v_a_5460_);
lean_dec_ref(v_a_5459_);
lean_dec(v_a_5458_);
lean_dec_ref(v_a_5457_);
lean_dec(v_a_5456_);
lean_dec(v_next_5455_);
return v_res_5462_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0(lean_object* v_00_u03b1_5463_, lean_object* v_a_5464_, lean_object* v_a_5465_, lean_object* v___y_5466_, lean_object* v___y_5467_, lean_object* v___y_5468_, lean_object* v___y_5469_, lean_object* v___y_5470_){
_start:
{
lean_object* v___x_5472_; 
v___x_5472_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(v_a_5464_, v_a_5465_, v___y_5466_, v___y_5467_, v___y_5468_, v___y_5469_, v___y_5470_);
return v___x_5472_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___boxed(lean_object* v_00_u03b1_5473_, lean_object* v_a_5474_, lean_object* v_a_5475_, lean_object* v___y_5476_, lean_object* v___y_5477_, lean_object* v___y_5478_, lean_object* v___y_5479_, lean_object* v___y_5480_, lean_object* v___y_5481_){
_start:
{
lean_object* v_res_5482_; 
v_res_5482_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0(v_00_u03b1_5473_, v_a_5474_, v_a_5475_, v___y_5476_, v___y_5477_, v___y_5478_, v___y_5479_, v___y_5480_);
lean_dec(v___y_5480_);
lean_dec_ref(v___y_5479_);
lean_dec(v___y_5478_);
lean_dec_ref(v___y_5477_);
lean_dec(v___y_5476_);
lean_dec(v_a_5474_);
return v_res_5482_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1(lean_object* v_00_u03b1_5483_, lean_object* v_as_5484_, size_t v_sz_5485_, size_t v_i_5486_, lean_object* v_b_5487_, lean_object* v___y_5488_, lean_object* v___y_5489_, lean_object* v___y_5490_, lean_object* v___y_5491_, lean_object* v___y_5492_){
_start:
{
lean_object* v___x_5494_; 
v___x_5494_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(v_as_5484_, v_sz_5485_, v_i_5486_, v_b_5487_, v___y_5488_, v___y_5489_, v___y_5490_, v___y_5491_, v___y_5492_);
return v___x_5494_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___boxed(lean_object* v_00_u03b1_5495_, lean_object* v_as_5496_, lean_object* v_sz_5497_, lean_object* v_i_5498_, lean_object* v_b_5499_, lean_object* v___y_5500_, lean_object* v___y_5501_, lean_object* v___y_5502_, lean_object* v___y_5503_, lean_object* v___y_5504_, lean_object* v___y_5505_){
_start:
{
size_t v_sz_boxed_5506_; size_t v_i_boxed_5507_; lean_object* v_res_5508_; 
v_sz_boxed_5506_ = lean_unbox_usize(v_sz_5497_);
lean_dec(v_sz_5497_);
v_i_boxed_5507_ = lean_unbox_usize(v_i_5498_);
lean_dec(v_i_5498_);
v_res_5508_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1(v_00_u03b1_5495_, v_as_5496_, v_sz_boxed_5506_, v_i_boxed_5507_, v_b_5499_, v___y_5500_, v___y_5501_, v___y_5502_, v___y_5503_, v___y_5504_);
lean_dec(v___y_5504_);
lean_dec_ref(v___y_5503_);
lean_dec(v___y_5502_);
lean_dec_ref(v___y_5501_);
lean_dec(v___y_5500_);
lean_dec_ref(v_as_5496_);
return v_res_5508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg(lean_object* v_next_5509_, lean_object* v_rest_5510_, lean_object* v_a_5511_, lean_object* v_a_5512_, lean_object* v_a_5513_, lean_object* v_a_5514_, lean_object* v_a_5515_){
_start:
{
lean_object* v___x_5517_; uint8_t v___x_5518_; 
v___x_5517_ = lean_unsigned_to_nat(0u);
v___x_5518_ = lean_nat_dec_eq(v_next_5509_, v___x_5517_);
if (v___x_5518_ == 0)
{
lean_object* v___x_5519_; 
v___x_5519_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_next_5509_, v_a_5511_, v_a_5512_, v_a_5513_, v_a_5514_, v_a_5515_);
if (lean_obj_tag(v___x_5519_) == 0)
{
lean_object* v_a_5520_; lean_object* v_snd_5521_; 
v_a_5520_ = lean_ctor_get(v___x_5519_, 0);
lean_inc(v_a_5520_);
lean_dec_ref_known(v___x_5519_, 1);
v_snd_5521_ = lean_ctor_get(v_a_5520_, 1);
lean_inc(v_snd_5521_);
lean_dec(v_a_5520_);
if (lean_obj_tag(v_rest_5510_) == 0)
{
lean_object* v___x_5522_; 
lean_dec(v_snd_5521_);
v___x_5522_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_next_5509_, v_a_5511_, v_a_5512_, v_a_5513_, v_a_5514_, v_a_5515_);
lean_dec(v_next_5509_);
return v___x_5522_;
}
else
{
lean_object* v_fst_5523_; lean_object* v_snd_5524_; lean_object* v_head_5525_; lean_object* v_tail_5526_; lean_object* v___x_5527_; uint8_t v___x_5528_; 
lean_dec(v_next_5509_);
v_fst_5523_ = lean_ctor_get(v_snd_5521_, 0);
lean_inc(v_fst_5523_);
v_snd_5524_ = lean_ctor_get(v_snd_5521_, 1);
lean_inc(v_snd_5524_);
lean_dec(v_snd_5521_);
v_head_5525_ = lean_ctor_get(v_rest_5510_, 0);
v_tail_5526_ = lean_ctor_get(v_rest_5510_, 1);
v___x_5527_ = lean_box(3);
v___x_5528_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_head_5525_, v___x_5527_);
if (v___x_5528_ == 0)
{
lean_object* v___x_5529_; 
lean_dec(v_fst_5523_);
v___x_5529_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_snd_5524_, v_head_5525_, v___x_5517_);
lean_dec(v_snd_5524_);
v_next_5509_ = v___x_5529_;
v_rest_5510_ = v_tail_5526_;
goto _start;
}
else
{
lean_dec(v_snd_5524_);
v_next_5509_ = v_fst_5523_;
v_rest_5510_ = v_tail_5526_;
goto _start;
}
}
}
else
{
lean_object* v_a_5532_; lean_object* v___x_5534_; uint8_t v_isShared_5535_; uint8_t v_isSharedCheck_5539_; 
lean_dec(v_next_5509_);
v_a_5532_ = lean_ctor_get(v___x_5519_, 0);
v_isSharedCheck_5539_ = !lean_is_exclusive(v___x_5519_);
if (v_isSharedCheck_5539_ == 0)
{
v___x_5534_ = v___x_5519_;
v_isShared_5535_ = v_isSharedCheck_5539_;
goto v_resetjp_5533_;
}
else
{
lean_inc(v_a_5532_);
lean_dec(v___x_5519_);
v___x_5534_ = lean_box(0);
v_isShared_5535_ = v_isSharedCheck_5539_;
goto v_resetjp_5533_;
}
v_resetjp_5533_:
{
lean_object* v___x_5537_; 
if (v_isShared_5535_ == 0)
{
v___x_5537_ = v___x_5534_;
goto v_reusejp_5536_;
}
else
{
lean_object* v_reuseFailAlloc_5538_; 
v_reuseFailAlloc_5538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5538_, 0, v_a_5532_);
v___x_5537_ = v_reuseFailAlloc_5538_;
goto v_reusejp_5536_;
}
v_reusejp_5536_:
{
return v___x_5537_;
}
}
}
}
else
{
lean_object* v___x_5540_; lean_object* v___x_5541_; 
lean_dec(v_next_5509_);
v___x_5540_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___x_5541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5541_, 0, v___x_5540_);
return v___x_5541_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg___boxed(lean_object* v_next_5542_, lean_object* v_rest_5543_, lean_object* v_a_5544_, lean_object* v_a_5545_, lean_object* v_a_5546_, lean_object* v_a_5547_, lean_object* v_a_5548_, lean_object* v_a_5549_){
_start:
{
lean_object* v_res_5550_; 
v_res_5550_ = l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg(v_next_5542_, v_rest_5543_, v_a_5544_, v_a_5545_, v_a_5546_, v_a_5547_, v_a_5548_);
lean_dec(v_a_5548_);
lean_dec_ref(v_a_5547_);
lean_dec(v_a_5546_);
lean_dec_ref(v_a_5545_);
lean_dec(v_a_5544_);
lean_dec(v_rest_5543_);
return v_res_5550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux(lean_object* v_00_u03b1_5551_, lean_object* v_next_5552_, lean_object* v_rest_5553_, lean_object* v_a_5554_, lean_object* v_a_5555_, lean_object* v_a_5556_, lean_object* v_a_5557_, lean_object* v_a_5558_){
_start:
{
lean_object* v___x_5560_; 
v___x_5560_ = l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg(v_next_5552_, v_rest_5553_, v_a_5554_, v_a_5555_, v_a_5556_, v_a_5557_, v_a_5558_);
return v___x_5560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux___boxed(lean_object* v_00_u03b1_5561_, lean_object* v_next_5562_, lean_object* v_rest_5563_, lean_object* v_a_5564_, lean_object* v_a_5565_, lean_object* v_a_5566_, lean_object* v_a_5567_, lean_object* v_a_5568_, lean_object* v_a_5569_){
_start:
{
lean_object* v_res_5570_; 
v_res_5570_ = l_Lean_Meta_LazyDiscrTree_extractKeyAux(v_00_u03b1_5561_, v_next_5562_, v_rest_5563_, v_a_5564_, v_a_5565_, v_a_5566_, v_a_5567_, v_a_5568_);
lean_dec(v_a_5568_);
lean_dec_ref(v_a_5567_);
lean_dec(v_a_5566_);
lean_dec_ref(v_a_5565_);
lean_dec(v_a_5564_);
lean_dec(v_rest_5563_);
return v_res_5570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey___redArg(lean_object* v_t_5571_, lean_object* v_path_5572_, lean_object* v_a_5573_, lean_object* v_a_5574_, lean_object* v_a_5575_, lean_object* v_a_5576_){
_start:
{
if (lean_obj_tag(v_path_5572_) == 0)
{
lean_object* v___x_5578_; lean_object* v___x_5579_; lean_object* v___x_5580_; 
v___x_5578_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___x_5579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5579_, 0, v___x_5578_);
lean_ctor_set(v___x_5579_, 1, v_t_5571_);
v___x_5580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5580_, 0, v___x_5579_);
return v___x_5580_;
}
else
{
lean_object* v_head_5581_; lean_object* v_tail_5582_; lean_object* v_roots_5583_; lean_object* v___x_5584_; lean_object* v_idx_5585_; lean_object* v___x_5586_; lean_object* v___x_5587_; 
v_head_5581_ = lean_ctor_get(v_path_5572_, 0);
lean_inc(v_head_5581_);
v_tail_5582_ = lean_ctor_get(v_path_5572_, 1);
lean_inc(v_tail_5582_);
lean_dec_ref_known(v_path_5572_, 2);
v_roots_5583_ = lean_ctor_get(v_t_5571_, 1);
v___x_5584_ = lean_unsigned_to_nat(0u);
v_idx_5585_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_roots_5583_, v_head_5581_, v___x_5584_);
lean_dec(v_head_5581_);
v___x_5586_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_extractKeyAux___boxed), 9, 3);
lean_closure_set(v___x_5586_, 0, lean_box(0));
lean_closure_set(v___x_5586_, 1, v_idx_5585_);
lean_closure_set(v___x_5586_, 2, v_tail_5582_);
v___x_5587_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_t_5571_, v___x_5586_, v_a_5573_, v_a_5574_, v_a_5575_, v_a_5576_);
return v___x_5587_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey___redArg___boxed(lean_object* v_t_5588_, lean_object* v_path_5589_, lean_object* v_a_5590_, lean_object* v_a_5591_, lean_object* v_a_5592_, lean_object* v_a_5593_, lean_object* v_a_5594_){
_start:
{
lean_object* v_res_5595_; 
v_res_5595_ = l_Lean_Meta_LazyDiscrTree_extractKey___redArg(v_t_5588_, v_path_5589_, v_a_5590_, v_a_5591_, v_a_5592_, v_a_5593_);
lean_dec(v_a_5593_);
lean_dec_ref(v_a_5592_);
lean_dec(v_a_5591_);
lean_dec_ref(v_a_5590_);
return v_res_5595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey(lean_object* v_00_u03b1_5596_, lean_object* v_t_5597_, lean_object* v_path_5598_, lean_object* v_a_5599_, lean_object* v_a_5600_, lean_object* v_a_5601_, lean_object* v_a_5602_){
_start:
{
lean_object* v___x_5604_; 
v___x_5604_ = l_Lean_Meta_LazyDiscrTree_extractKey___redArg(v_t_5597_, v_path_5598_, v_a_5599_, v_a_5600_, v_a_5601_, v_a_5602_);
return v___x_5604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey___boxed(lean_object* v_00_u03b1_5605_, lean_object* v_t_5606_, lean_object* v_path_5607_, lean_object* v_a_5608_, lean_object* v_a_5609_, lean_object* v_a_5610_, lean_object* v_a_5611_, lean_object* v_a_5612_){
_start:
{
lean_object* v_res_5613_; 
v_res_5613_ = l_Lean_Meta_LazyDiscrTree_extractKey(v_00_u03b1_5605_, v_t_5606_, v_path_5607_, v_a_5608_, v_a_5609_, v_a_5610_, v_a_5611_);
lean_dec(v_a_5611_);
lean_dec_ref(v_a_5610_);
lean_dec(v_a_5609_);
lean_dec_ref(v_a_5608_);
return v_res_5613_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(lean_object* v_as_x27_5614_, lean_object* v_b_5615_, lean_object* v___y_5616_, lean_object* v___y_5617_, lean_object* v___y_5618_, lean_object* v___y_5619_){
_start:
{
if (lean_obj_tag(v_as_x27_5614_) == 0)
{
lean_object* v___x_5621_; 
v___x_5621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5621_, 0, v_b_5615_);
return v___x_5621_;
}
else
{
lean_object* v_head_5622_; lean_object* v_tail_5623_; lean_object* v_fst_5624_; lean_object* v_snd_5625_; lean_object* v___x_5626_; 
v_head_5622_ = lean_ctor_get(v_as_x27_5614_, 0);
v_tail_5623_ = lean_ctor_get(v_as_x27_5614_, 1);
v_fst_5624_ = lean_ctor_get(v_b_5615_, 0);
lean_inc(v_fst_5624_);
v_snd_5625_ = lean_ctor_get(v_b_5615_, 1);
lean_inc(v_snd_5625_);
lean_dec_ref(v_b_5615_);
lean_inc(v_head_5622_);
v___x_5626_ = l_Lean_Meta_LazyDiscrTree_extractKey___redArg(v_snd_5625_, v_head_5622_, v___y_5616_, v___y_5617_, v___y_5618_, v___y_5619_);
if (lean_obj_tag(v___x_5626_) == 0)
{
lean_object* v_a_5627_; lean_object* v_fst_5628_; lean_object* v_snd_5629_; lean_object* v___x_5631_; uint8_t v_isShared_5632_; uint8_t v_isSharedCheck_5638_; 
v_a_5627_ = lean_ctor_get(v___x_5626_, 0);
lean_inc(v_a_5627_);
lean_dec_ref_known(v___x_5626_, 1);
v_fst_5628_ = lean_ctor_get(v_a_5627_, 0);
v_snd_5629_ = lean_ctor_get(v_a_5627_, 1);
v_isSharedCheck_5638_ = !lean_is_exclusive(v_a_5627_);
if (v_isSharedCheck_5638_ == 0)
{
v___x_5631_ = v_a_5627_;
v_isShared_5632_ = v_isSharedCheck_5638_;
goto v_resetjp_5630_;
}
else
{
lean_inc(v_snd_5629_);
lean_inc(v_fst_5628_);
lean_dec(v_a_5627_);
v___x_5631_ = lean_box(0);
v_isShared_5632_ = v_isSharedCheck_5638_;
goto v_resetjp_5630_;
}
v_resetjp_5630_:
{
lean_object* v___x_5633_; lean_object* v___x_5635_; 
v___x_5633_ = l_Array_append___redArg(v_fst_5624_, v_fst_5628_);
lean_dec(v_fst_5628_);
if (v_isShared_5632_ == 0)
{
lean_ctor_set(v___x_5631_, 0, v___x_5633_);
v___x_5635_ = v___x_5631_;
goto v_reusejp_5634_;
}
else
{
lean_object* v_reuseFailAlloc_5637_; 
v_reuseFailAlloc_5637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5637_, 0, v___x_5633_);
lean_ctor_set(v_reuseFailAlloc_5637_, 1, v_snd_5629_);
v___x_5635_ = v_reuseFailAlloc_5637_;
goto v_reusejp_5634_;
}
v_reusejp_5634_:
{
v_as_x27_5614_ = v_tail_5623_;
v_b_5615_ = v___x_5635_;
goto _start;
}
}
}
else
{
lean_dec(v_fst_5624_);
return v___x_5626_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg___boxed(lean_object* v_as_x27_5639_, lean_object* v_b_5640_, lean_object* v___y_5641_, lean_object* v___y_5642_, lean_object* v___y_5643_, lean_object* v___y_5644_, lean_object* v___y_5645_){
_start:
{
lean_object* v_res_5646_; 
v_res_5646_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(v_as_x27_5639_, v_b_5640_, v___y_5641_, v___y_5642_, v___y_5643_, v___y_5644_);
lean_dec(v___y_5644_);
lean_dec_ref(v___y_5643_);
lean_dec(v___y_5642_);
lean_dec_ref(v___y_5641_);
lean_dec(v_as_x27_5639_);
return v_res_5646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(lean_object* v_t_5647_, lean_object* v_keys_5648_, lean_object* v_a_5649_, lean_object* v_a_5650_, lean_object* v_a_5651_, lean_object* v_a_5652_){
_start:
{
lean_object* v_allExtracted_5654_; lean_object* v___x_5655_; lean_object* v___x_5656_; 
v_allExtracted_5654_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___x_5655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5655_, 0, v_allExtracted_5654_);
lean_ctor_set(v___x_5655_, 1, v_t_5647_);
v___x_5656_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(v_keys_5648_, v___x_5655_, v_a_5649_, v_a_5650_, v_a_5651_, v_a_5652_);
if (lean_obj_tag(v___x_5656_) == 0)
{
lean_object* v_a_5657_; lean_object* v___x_5659_; uint8_t v_isShared_5660_; uint8_t v_isSharedCheck_5673_; 
v_a_5657_ = lean_ctor_get(v___x_5656_, 0);
v_isSharedCheck_5673_ = !lean_is_exclusive(v___x_5656_);
if (v_isSharedCheck_5673_ == 0)
{
v___x_5659_ = v___x_5656_;
v_isShared_5660_ = v_isSharedCheck_5673_;
goto v_resetjp_5658_;
}
else
{
lean_inc(v_a_5657_);
lean_dec(v___x_5656_);
v___x_5659_ = lean_box(0);
v_isShared_5660_ = v_isSharedCheck_5673_;
goto v_resetjp_5658_;
}
v_resetjp_5658_:
{
lean_object* v_fst_5661_; lean_object* v_snd_5662_; lean_object* v___x_5664_; uint8_t v_isShared_5665_; uint8_t v_isSharedCheck_5672_; 
v_fst_5661_ = lean_ctor_get(v_a_5657_, 0);
v_snd_5662_ = lean_ctor_get(v_a_5657_, 1);
v_isSharedCheck_5672_ = !lean_is_exclusive(v_a_5657_);
if (v_isSharedCheck_5672_ == 0)
{
v___x_5664_ = v_a_5657_;
v_isShared_5665_ = v_isSharedCheck_5672_;
goto v_resetjp_5663_;
}
else
{
lean_inc(v_snd_5662_);
lean_inc(v_fst_5661_);
lean_dec(v_a_5657_);
v___x_5664_ = lean_box(0);
v_isShared_5665_ = v_isSharedCheck_5672_;
goto v_resetjp_5663_;
}
v_resetjp_5663_:
{
lean_object* v___x_5667_; 
if (v_isShared_5665_ == 0)
{
v___x_5667_ = v___x_5664_;
goto v_reusejp_5666_;
}
else
{
lean_object* v_reuseFailAlloc_5671_; 
v_reuseFailAlloc_5671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5671_, 0, v_fst_5661_);
lean_ctor_set(v_reuseFailAlloc_5671_, 1, v_snd_5662_);
v___x_5667_ = v_reuseFailAlloc_5671_;
goto v_reusejp_5666_;
}
v_reusejp_5666_:
{
lean_object* v___x_5669_; 
if (v_isShared_5660_ == 0)
{
lean_ctor_set(v___x_5659_, 0, v___x_5667_);
v___x_5669_ = v___x_5659_;
goto v_reusejp_5668_;
}
else
{
lean_object* v_reuseFailAlloc_5670_; 
v_reuseFailAlloc_5670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5670_, 0, v___x_5667_);
v___x_5669_ = v_reuseFailAlloc_5670_;
goto v_reusejp_5668_;
}
v_reusejp_5668_:
{
return v___x_5669_;
}
}
}
}
}
else
{
return v___x_5656_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys___redArg___boxed(lean_object* v_t_5674_, lean_object* v_keys_5675_, lean_object* v_a_5676_, lean_object* v_a_5677_, lean_object* v_a_5678_, lean_object* v_a_5679_, lean_object* v_a_5680_){
_start:
{
lean_object* v_res_5681_; 
v_res_5681_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_t_5674_, v_keys_5675_, v_a_5676_, v_a_5677_, v_a_5678_, v_a_5679_);
lean_dec(v_a_5679_);
lean_dec_ref(v_a_5678_);
lean_dec(v_a_5677_);
lean_dec_ref(v_a_5676_);
lean_dec(v_keys_5675_);
return v_res_5681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys(lean_object* v_00_u03b1_5682_, lean_object* v_t_5683_, lean_object* v_keys_5684_, lean_object* v_a_5685_, lean_object* v_a_5686_, lean_object* v_a_5687_, lean_object* v_a_5688_){
_start:
{
lean_object* v___x_5690_; 
v___x_5690_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_t_5683_, v_keys_5684_, v_a_5685_, v_a_5686_, v_a_5687_, v_a_5688_);
return v___x_5690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys___boxed(lean_object* v_00_u03b1_5691_, lean_object* v_t_5692_, lean_object* v_keys_5693_, lean_object* v_a_5694_, lean_object* v_a_5695_, lean_object* v_a_5696_, lean_object* v_a_5697_, lean_object* v_a_5698_){
_start:
{
lean_object* v_res_5699_; 
v_res_5699_ = l_Lean_Meta_LazyDiscrTree_extractKeys(v_00_u03b1_5691_, v_t_5692_, v_keys_5693_, v_a_5694_, v_a_5695_, v_a_5696_, v_a_5697_);
lean_dec(v_a_5697_);
lean_dec_ref(v_a_5696_);
lean_dec(v_a_5695_);
lean_dec_ref(v_a_5694_);
lean_dec(v_keys_5693_);
return v_res_5699_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0(lean_object* v_00_u03b1_5700_, lean_object* v_as_5701_, lean_object* v_as_x27_5702_, lean_object* v_b_5703_, lean_object* v_a_5704_, lean_object* v___y_5705_, lean_object* v___y_5706_, lean_object* v___y_5707_, lean_object* v___y_5708_){
_start:
{
lean_object* v___x_5710_; 
v___x_5710_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(v_as_x27_5702_, v_b_5703_, v___y_5705_, v___y_5706_, v___y_5707_, v___y_5708_);
return v___x_5710_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___boxed(lean_object* v_00_u03b1_5711_, lean_object* v_as_5712_, lean_object* v_as_x27_5713_, lean_object* v_b_5714_, lean_object* v_a_5715_, lean_object* v___y_5716_, lean_object* v___y_5717_, lean_object* v___y_5718_, lean_object* v___y_5719_, lean_object* v___y_5720_){
_start:
{
lean_object* v_res_5721_; 
v_res_5721_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0(v_00_u03b1_5711_, v_as_5712_, v_as_x27_5713_, v_b_5714_, v_a_5715_, v___y_5716_, v___y_5717_, v___y_5718_, v___y_5719_);
lean_dec(v___y_5719_);
lean_dec_ref(v___y_5718_);
lean_dec(v___y_5717_);
lean_dec_ref(v___y_5716_);
lean_dec(v_as_x27_5713_);
lean_dec(v_as_5712_);
return v_res_5721_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1(void){
_start:
{
lean_object* v___x_5723_; lean_object* v___x_5724_; 
v___x_5723_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__0));
v___x_5724_ = l_Lean_stringToMessageData(v___x_5723_);
return v___x_5724_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3(void){
_start:
{
lean_object* v___x_5726_; lean_object* v___x_5727_; 
v___x_5726_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__2));
v___x_5727_ = l_Lean_stringToMessageData(v___x_5726_);
return v___x_5727_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5(void){
_start:
{
lean_object* v___x_5729_; lean_object* v___x_5730_; 
v___x_5729_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__4));
v___x_5730_ = l_Lean_stringToMessageData(v___x_5729_);
return v___x_5730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg(lean_object* v_inst_5731_, lean_object* v_inst_5732_, lean_object* v_inst_5733_, lean_object* v_inst_5734_, lean_object* v_f_5735_){
_start:
{
lean_object* v_module_5736_; lean_object* v_const_5737_; lean_object* v_exception_5738_; lean_object* v___x_5739_; lean_object* v___x_5740_; lean_object* v___x_5741_; lean_object* v___x_5742_; lean_object* v___x_5743_; lean_object* v___x_5744_; lean_object* v___x_5745_; lean_object* v___x_5746_; lean_object* v___x_5747_; lean_object* v___x_5748_; lean_object* v___x_5749_; lean_object* v___x_5750_; 
v_module_5736_ = lean_ctor_get(v_f_5735_, 0);
lean_inc(v_module_5736_);
v_const_5737_ = lean_ctor_get(v_f_5735_, 1);
lean_inc(v_const_5737_);
v_exception_5738_ = lean_ctor_get(v_f_5735_, 2);
lean_inc_ref(v_exception_5738_);
lean_dec_ref(v_f_5735_);
v___x_5739_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1);
v___x_5740_ = l_Lean_MessageData_ofName(v_const_5737_);
v___x_5741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5741_, 0, v___x_5739_);
lean_ctor_set(v___x_5741_, 1, v___x_5740_);
v___x_5742_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3);
v___x_5743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5743_, 0, v___x_5741_);
lean_ctor_set(v___x_5743_, 1, v___x_5742_);
v___x_5744_ = l_Lean_MessageData_ofName(v_module_5736_);
v___x_5745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5745_, 0, v___x_5743_);
lean_ctor_set(v___x_5745_, 1, v___x_5744_);
v___x_5746_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5);
v___x_5747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5747_, 0, v___x_5745_);
lean_ctor_set(v___x_5747_, 1, v___x_5746_);
v___x_5748_ = l_Lean_Exception_toMessageData(v_exception_5738_);
v___x_5749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5749_, 0, v___x_5747_);
lean_ctor_set(v___x_5749_, 1, v___x_5748_);
v___x_5750_ = l_Lean_logError___redArg(v_inst_5731_, v_inst_5732_, v_inst_5733_, v_inst_5734_, v___x_5749_);
return v___x_5750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure(lean_object* v_m_5751_, lean_object* v_inst_5752_, lean_object* v_inst_5753_, lean_object* v_inst_5754_, lean_object* v_inst_5755_, lean_object* v_f_5756_){
_start:
{
lean_object* v___x_5757_; 
v___x_5757_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg(v_inst_5752_, v_inst_5753_, v_inst_5754_, v_inst_5755_, v_f_5756_);
return v___x_5757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__0(lean_object* v_tasks_5758_, lean_object* v_toPure_5759_, lean_object* v_t_5760_){
_start:
{
lean_object* v___x_5761_; lean_object* v___x_5762_; 
v___x_5761_ = lean_array_push(v_tasks_5758_, v_t_5760_);
v___x_5762_ = lean_apply_2(v_toPure_5759_, lean_box(0), v___x_5761_);
return v___x_5762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(lean_object* v_inst_5763_, lean_object* v_inst_5764_, lean_object* v_cctx_5765_, lean_object* v_env_5766_, lean_object* v_act_5767_, lean_object* v_constantsPerTask_5768_, lean_object* v_n_5769_, lean_object* v_ngen_5770_, lean_object* v_tasks_5771_, lean_object* v_start_5772_, lean_object* v_cnt_5773_, lean_object* v_idx_5774_){
_start:
{
lean_object* v___x_5775_; lean_object* v_toApplicative_5776_; lean_object* v_moduleData_5777_; lean_object* v_toBind_5778_; lean_object* v_toPure_5779_; lean_object* v___x_5780_; uint8_t v___x_5781_; 
v___x_5775_ = l_Lean_Environment_header(v_env_5766_);
v_toApplicative_5776_ = lean_ctor_get(v_inst_5763_, 0);
v_moduleData_5777_ = lean_ctor_get(v___x_5775_, 7);
lean_inc_ref(v_moduleData_5777_);
lean_dec_ref(v___x_5775_);
v_toBind_5778_ = lean_ctor_get(v_inst_5763_, 1);
v_toPure_5779_ = lean_ctor_get(v_toApplicative_5776_, 1);
v___x_5780_ = lean_array_get_size(v_moduleData_5777_);
v___x_5781_ = lean_nat_dec_lt(v_idx_5774_, v___x_5780_);
if (v___x_5781_ == 0)
{
uint8_t v___x_5782_; 
lean_inc(v_toPure_5779_);
lean_inc(v_toBind_5778_);
lean_dec_ref(v_moduleData_5777_);
lean_dec(v_idx_5774_);
lean_dec(v_cnt_5773_);
lean_dec(v_constantsPerTask_5768_);
lean_dec_ref(v_inst_5763_);
v___x_5782_ = lean_nat_dec_lt(v_start_5772_, v_n_5769_);
if (v___x_5782_ == 0)
{
lean_object* v___x_5783_; 
lean_dec(v_toBind_5778_);
lean_dec(v_start_5772_);
lean_dec_ref(v_ngen_5770_);
lean_dec(v_n_5769_);
lean_dec_ref(v_act_5767_);
lean_dec_ref(v_env_5766_);
lean_dec_ref(v_cctx_5765_);
lean_dec(v_inst_5764_);
v___x_5783_ = lean_apply_2(v_toPure_5779_, lean_box(0), v_tasks_5771_);
return v___x_5783_;
}
else
{
lean_object* v_namePrefix_5784_; lean_object* v_idx_5785_; lean_object* v___x_5787_; uint8_t v_isShared_5788_; uint8_t v_isSharedCheck_5800_; 
v_namePrefix_5784_ = lean_ctor_get(v_ngen_5770_, 0);
v_idx_5785_ = lean_ctor_get(v_ngen_5770_, 1);
v_isSharedCheck_5800_ = !lean_is_exclusive(v_ngen_5770_);
if (v_isSharedCheck_5800_ == 0)
{
v___x_5787_ = v_ngen_5770_;
v_isShared_5788_ = v_isSharedCheck_5800_;
goto v_resetjp_5786_;
}
else
{
lean_inc(v_idx_5785_);
lean_inc(v_namePrefix_5784_);
lean_dec(v_ngen_5770_);
v___x_5787_ = lean_box(0);
v_isShared_5788_ = v_isSharedCheck_5800_;
goto v_resetjp_5786_;
}
v_resetjp_5786_:
{
lean_object* v___f_5789_; lean_object* v___x_5790_; lean_object* v___x_5791_; lean_object* v___x_5793_; 
v___f_5789_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5789_, 0, v_tasks_5771_);
lean_closure_set(v___f_5789_, 1, v_toPure_5779_);
v___x_5790_ = l_Lean_Name_num___override(v_namePrefix_5784_, v_idx_5785_);
v___x_5791_ = lean_unsigned_to_nat(1u);
if (v_isShared_5788_ == 0)
{
lean_ctor_set(v___x_5787_, 1, v___x_5791_);
lean_ctor_set(v___x_5787_, 0, v___x_5790_);
v___x_5793_ = v___x_5787_;
goto v_reusejp_5792_;
}
else
{
lean_object* v_reuseFailAlloc_5799_; 
v_reuseFailAlloc_5799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5799_, 0, v___x_5790_);
lean_ctor_set(v_reuseFailAlloc_5799_, 1, v___x_5791_);
v___x_5793_ = v_reuseFailAlloc_5799_;
goto v_reusejp_5792_;
}
v_reusejp_5792_:
{
lean_object* v___x_5794_; lean_object* v___x_5795_; lean_object* v___x_5796_; lean_object* v___x_5797_; lean_object* v___x_5798_; 
v___x_5794_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_5794_, 0, lean_box(0));
lean_closure_set(v___x_5794_, 1, v_cctx_5765_);
lean_closure_set(v___x_5794_, 2, v___x_5793_);
lean_closure_set(v___x_5794_, 3, v_env_5766_);
lean_closure_set(v___x_5794_, 4, v_act_5767_);
lean_closure_set(v___x_5794_, 5, v_start_5772_);
lean_closure_set(v___x_5794_, 6, v_n_5769_);
v___x_5795_ = lean_unsigned_to_nat(0u);
v___x_5796_ = lean_alloc_closure((void*)(l_BaseIO_asTask___boxed), 4, 3);
lean_closure_set(v___x_5796_, 0, lean_box(0));
lean_closure_set(v___x_5796_, 1, v___x_5794_);
lean_closure_set(v___x_5796_, 2, v___x_5795_);
v___x_5797_ = lean_apply_2(v_inst_5764_, lean_box(0), v___x_5796_);
v___x_5798_ = lean_apply_4(v_toBind_5778_, lean_box(0), lean_box(0), v___x_5797_, v___f_5789_);
return v___x_5798_;
}
}
}
}
else
{
lean_object* v_mdata_5801_; lean_object* v_constants_5802_; lean_object* v___x_5803_; lean_object* v_cnt_5804_; uint8_t v___x_5805_; 
v_mdata_5801_ = lean_array_fget(v_moduleData_5777_, v_idx_5774_);
lean_dec_ref(v_moduleData_5777_);
v_constants_5802_ = lean_ctor_get(v_mdata_5801_, 2);
lean_inc_ref(v_constants_5802_);
lean_dec(v_mdata_5801_);
v___x_5803_ = lean_array_get_size(v_constants_5802_);
lean_dec_ref(v_constants_5802_);
v_cnt_5804_ = lean_nat_add(v_cnt_5773_, v___x_5803_);
lean_dec(v_cnt_5773_);
v___x_5805_ = lean_nat_dec_lt(v_constantsPerTask_5768_, v_cnt_5804_);
if (v___x_5805_ == 0)
{
lean_object* v___x_5806_; lean_object* v___x_5807_; 
v___x_5806_ = lean_unsigned_to_nat(1u);
v___x_5807_ = lean_nat_add(v_idx_5774_, v___x_5806_);
lean_dec(v_idx_5774_);
v_cnt_5773_ = v_cnt_5804_;
v_idx_5774_ = v___x_5807_;
goto _start;
}
else
{
lean_object* v_namePrefix_5809_; lean_object* v_idx_5810_; lean_object* v___x_5812_; uint8_t v_isShared_5813_; uint8_t v_isSharedCheck_5828_; 
lean_inc(v_toBind_5778_);
lean_dec(v_cnt_5804_);
v_namePrefix_5809_ = lean_ctor_get(v_ngen_5770_, 0);
v_idx_5810_ = lean_ctor_get(v_ngen_5770_, 1);
v_isSharedCheck_5828_ = !lean_is_exclusive(v_ngen_5770_);
if (v_isSharedCheck_5828_ == 0)
{
v___x_5812_ = v_ngen_5770_;
v_isShared_5813_ = v_isSharedCheck_5828_;
goto v_resetjp_5811_;
}
else
{
lean_inc(v_idx_5810_);
lean_inc(v_namePrefix_5809_);
lean_dec(v_ngen_5770_);
v___x_5812_ = lean_box(0);
v_isShared_5813_ = v_isSharedCheck_5828_;
goto v_resetjp_5811_;
}
v_resetjp_5811_:
{
lean_object* v___x_5814_; lean_object* v___x_5815_; lean_object* v___x_5817_; 
lean_inc(v_idx_5810_);
lean_inc(v_namePrefix_5809_);
v___x_5814_ = l_Lean_Name_num___override(v_namePrefix_5809_, v_idx_5810_);
v___x_5815_ = lean_unsigned_to_nat(1u);
if (v_isShared_5813_ == 0)
{
lean_ctor_set(v___x_5812_, 1, v___x_5815_);
lean_ctor_set(v___x_5812_, 0, v___x_5814_);
v___x_5817_ = v___x_5812_;
goto v_reusejp_5816_;
}
else
{
lean_object* v_reuseFailAlloc_5827_; 
v_reuseFailAlloc_5827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5827_, 0, v___x_5814_);
lean_ctor_set(v_reuseFailAlloc_5827_, 1, v___x_5815_);
v___x_5817_ = v_reuseFailAlloc_5827_;
goto v_reusejp_5816_;
}
v_reusejp_5816_:
{
lean_object* v___x_5818_; lean_object* v___x_5819_; lean_object* v___x_5820_; lean_object* v___f_5821_; lean_object* v___x_5822_; lean_object* v___x_5823_; lean_object* v___x_5824_; lean_object* v___x_5825_; lean_object* v___x_5826_; 
v___x_5818_ = lean_nat_add(v_idx_5810_, v___x_5815_);
lean_dec(v_idx_5810_);
v___x_5819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5819_, 0, v_namePrefix_5809_);
lean_ctor_set(v___x_5819_, 1, v___x_5818_);
v___x_5820_ = lean_nat_add(v_idx_5774_, v___x_5815_);
lean_dec(v_idx_5774_);
lean_inc(v___x_5820_);
lean_inc_ref(v_act_5767_);
lean_inc_ref(v_env_5766_);
lean_inc_ref(v_cctx_5765_);
lean_inc(v_inst_5764_);
v___f_5821_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__1), 11, 10);
lean_closure_set(v___f_5821_, 0, v_tasks_5771_);
lean_closure_set(v___f_5821_, 1, v_inst_5763_);
lean_closure_set(v___f_5821_, 2, v_inst_5764_);
lean_closure_set(v___f_5821_, 3, v_cctx_5765_);
lean_closure_set(v___f_5821_, 4, v_env_5766_);
lean_closure_set(v___f_5821_, 5, v_act_5767_);
lean_closure_set(v___f_5821_, 6, v_constantsPerTask_5768_);
lean_closure_set(v___f_5821_, 7, v_n_5769_);
lean_closure_set(v___f_5821_, 8, v___x_5819_);
lean_closure_set(v___f_5821_, 9, v___x_5820_);
v___x_5822_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_5822_, 0, lean_box(0));
lean_closure_set(v___x_5822_, 1, v_cctx_5765_);
lean_closure_set(v___x_5822_, 2, v___x_5817_);
lean_closure_set(v___x_5822_, 3, v_env_5766_);
lean_closure_set(v___x_5822_, 4, v_act_5767_);
lean_closure_set(v___x_5822_, 5, v_start_5772_);
lean_closure_set(v___x_5822_, 6, v___x_5820_);
v___x_5823_ = lean_unsigned_to_nat(0u);
v___x_5824_ = lean_alloc_closure((void*)(l_BaseIO_asTask___boxed), 4, 3);
lean_closure_set(v___x_5824_, 0, lean_box(0));
lean_closure_set(v___x_5824_, 1, v___x_5822_);
lean_closure_set(v___x_5824_, 2, v___x_5823_);
v___x_5825_ = lean_apply_2(v_inst_5764_, lean_box(0), v___x_5824_);
v___x_5826_ = lean_apply_4(v_toBind_5778_, lean_box(0), lean_box(0), v___x_5825_, v___f_5821_);
return v___x_5826_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__1(lean_object* v_tasks_5829_, lean_object* v_inst_5830_, lean_object* v_inst_5831_, lean_object* v_cctx_5832_, lean_object* v_env_5833_, lean_object* v_act_5834_, lean_object* v_constantsPerTask_5835_, lean_object* v_n_5836_, lean_object* v___x_5837_, lean_object* v___x_5838_, lean_object* v_t_5839_){
_start:
{
lean_object* v___x_5840_; lean_object* v___x_5841_; lean_object* v___x_5842_; 
v___x_5840_ = lean_array_push(v_tasks_5829_, v_t_5839_);
v___x_5841_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_5838_);
v___x_5842_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(v_inst_5830_, v_inst_5831_, v_cctx_5832_, v_env_5833_, v_act_5834_, v_constantsPerTask_5835_, v_n_5836_, v___x_5837_, v___x_5840_, v___x_5838_, v___x_5841_, v___x_5838_);
return v___x_5842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go(lean_object* v_m_5843_, lean_object* v_00_u03b1_5844_, lean_object* v_inst_5845_, lean_object* v_inst_5846_, lean_object* v_cctx_5847_, lean_object* v_env_5848_, lean_object* v_act_5849_, lean_object* v_constantsPerTask_5850_, lean_object* v_n_5851_, lean_object* v_ngen_5852_, lean_object* v_tasks_5853_, lean_object* v_start_5854_, lean_object* v_cnt_5855_, lean_object* v_idx_5856_){
_start:
{
lean_object* v___x_5857_; 
v___x_5857_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(v_inst_5845_, v_inst_5846_, v_cctx_5847_, v_env_5848_, v_act_5849_, v_constantsPerTask_5850_, v_n_5851_, v_ngen_5852_, v_tasks_5853_, v_start_5854_, v_cnt_5855_, v_idx_5856_);
return v___x_5857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_getChildNgen_match__1_splitter___redArg(lean_object* v_x_5858_, lean_object* v_h__1_5859_){
_start:
{
lean_object* v_fst_5860_; lean_object* v_snd_5861_; lean_object* v___x_5862_; 
v_fst_5860_ = lean_ctor_get(v_x_5858_, 0);
lean_inc(v_fst_5860_);
v_snd_5861_ = lean_ctor_get(v_x_5858_, 1);
lean_inc(v_snd_5861_);
lean_dec_ref(v_x_5858_);
v___x_5862_ = lean_apply_2(v_h__1_5859_, v_fst_5860_, v_snd_5861_);
return v___x_5862_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_getChildNgen_match__1_splitter(lean_object* v_motive_5863_, lean_object* v_x_5864_, lean_object* v_h__1_5865_){
_start:
{
lean_object* v_fst_5866_; lean_object* v_snd_5867_; lean_object* v___x_5868_; 
v_fst_5866_ = lean_ctor_get(v_x_5864_, 0);
lean_inc(v_fst_5866_);
v_snd_5867_ = lean_ctor_get(v_x_5864_, 1);
lean_inc(v_snd_5867_);
lean_dec_ref(v_x_5864_);
v___x_5868_ = lean_apply_2(v_h__1_5865_, v_fst_5866_, v_snd_5867_);
return v___x_5868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__0(lean_object* v_inst_5869_, lean_object* v_inst_5870_, lean_object* v_inst_5871_, lean_object* v_inst_5872_, lean_object* v_x_5873_, lean_object* v___y_5874_){
_start:
{
lean_object* v___x_5875_; 
v___x_5875_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg(v_inst_5869_, v_inst_5870_, v_inst_5871_, v_inst_5872_, v___y_5874_);
return v___x_5875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__1(lean_object* v_tree_5876_, lean_object* v_toPure_5877_, lean_object* v_____r_5878_){
_start:
{
lean_object* v___x_5879_; lean_object* v___x_5880_; 
v___x_5879_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_tree_5876_);
v___x_5880_ = lean_apply_2(v_toPure_5877_, lean_box(0), v___x_5879_);
return v___x_5880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__2(lean_object* v___x_5881_, lean_object* v___x_5882_, lean_object* v_toPure_5883_, lean_object* v_toBind_5884_, lean_object* v_inst_5885_, lean_object* v___f_5886_, lean_object* v_tasks_5887_){
_start:
{
lean_object* v___x_5888_; lean_object* v___x_5889_; lean_object* v___x_5890_; lean_object* v___x_5891_; lean_object* v___x_5892_; lean_object* v_r_5893_; lean_object* v_tree_5894_; lean_object* v_errors_5895_; lean_object* v___f_5896_; lean_object* v___x_5897_; lean_object* v___x_5898_; uint8_t v___x_5899_; 
v___x_5888_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__1);
lean_inc(v___x_5881_);
v___x_5889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5889_, 0, v___x_5881_);
lean_ctor_set(v___x_5889_, 1, v___x_5888_);
v___x_5890_ = lean_mk_empty_array_with_capacity(v___x_5881_);
lean_inc_ref(v___x_5890_);
v___x_5891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5891_, 0, v___x_5889_);
lean_ctor_set(v___x_5891_, 1, v___x_5890_);
v___x_5892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5892_, 0, v___x_5891_);
lean_ctor_set(v___x_5892_, 1, v___x_5890_);
v_r_5893_ = l_Lean_Meta_LazyDiscrTree_combineGet___redArg(v___x_5882_, v___x_5892_, v_tasks_5887_);
v_tree_5894_ = lean_ctor_get(v_r_5893_, 0);
lean_inc_ref(v_tree_5894_);
v_errors_5895_ = lean_ctor_get(v_r_5893_, 1);
lean_inc_ref(v_errors_5895_);
lean_dec(v_r_5893_);
lean_inc(v_toPure_5883_);
v___f_5896_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__1), 3, 2);
lean_closure_set(v___f_5896_, 0, v_tree_5894_);
lean_closure_set(v___f_5896_, 1, v_toPure_5883_);
v___x_5897_ = lean_array_get_size(v_errors_5895_);
v___x_5898_ = lean_box(0);
v___x_5899_ = lean_nat_dec_lt(v___x_5881_, v___x_5897_);
lean_dec(v___x_5881_);
if (v___x_5899_ == 0)
{
lean_object* v___x_5900_; lean_object* v___x_5901_; 
lean_dec_ref(v_errors_5895_);
lean_dec(v___f_5886_);
lean_dec_ref(v_inst_5885_);
v___x_5900_ = lean_apply_2(v_toPure_5883_, lean_box(0), v___x_5898_);
v___x_5901_ = lean_apply_4(v_toBind_5884_, lean_box(0), lean_box(0), v___x_5900_, v___f_5896_);
return v___x_5901_;
}
else
{
size_t v___x_5902_; size_t v___x_5903_; lean_object* v___x_5904_; lean_object* v___x_5905_; 
lean_dec(v_toPure_5883_);
v___x_5902_ = ((size_t)0ULL);
v___x_5903_ = lean_usize_of_nat(v___x_5897_);
v___x_5904_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_5885_, v___f_5886_, v_errors_5895_, v___x_5902_, v___x_5903_, v___x_5898_);
v___x_5905_ = lean_apply_4(v_toBind_5884_, lean_box(0), lean_box(0), v___x_5904_, v___f_5896_);
return v___x_5905_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg(lean_object* v_inst_5908_, lean_object* v_inst_5909_, lean_object* v_inst_5910_, lean_object* v_inst_5911_, lean_object* v_inst_5912_, lean_object* v_cctx_5913_, lean_object* v_ngen_5914_, lean_object* v_env_5915_, lean_object* v_act_5916_, lean_object* v_constantsPerTask_5917_){
_start:
{
lean_object* v___x_5918_; lean_object* v_moduleData_5919_; lean_object* v_toApplicative_5920_; lean_object* v_toBind_5921_; lean_object* v_n_5922_; lean_object* v___x_5923_; lean_object* v___x_5924_; lean_object* v___x_5925_; lean_object* v_toPure_5926_; lean_object* v___f_5927_; lean_object* v___x_5928_; lean_object* v___f_5929_; lean_object* v___x_5930_; 
v___x_5918_ = l_Lean_Environment_header(v_env_5915_);
v_moduleData_5919_ = lean_ctor_get(v___x_5918_, 7);
lean_inc_ref(v_moduleData_5919_);
lean_dec_ref(v___x_5918_);
v_toApplicative_5920_ = lean_ctor_get(v_inst_5908_, 0);
v_toBind_5921_ = lean_ctor_get(v_inst_5908_, 1);
lean_inc_n(v_toBind_5921_, 2);
v_n_5922_ = lean_array_get_size(v_moduleData_5919_);
lean_dec_ref(v_moduleData_5919_);
v___x_5923_ = lean_unsigned_to_nat(0u);
v___x_5924_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
lean_inc_ref_n(v_inst_5908_, 2);
v___x_5925_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(v_inst_5908_, v_inst_5912_, v_cctx_5913_, v_env_5915_, v_act_5916_, v_constantsPerTask_5917_, v_n_5922_, v_ngen_5914_, v___x_5924_, v___x_5923_, v___x_5923_, v___x_5923_);
v_toPure_5926_ = lean_ctor_get(v_toApplicative_5920_, 1);
lean_inc(v_toPure_5926_);
v___f_5927_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__0), 6, 4);
lean_closure_set(v___f_5927_, 0, v_inst_5908_);
lean_closure_set(v___f_5927_, 1, v_inst_5909_);
lean_closure_set(v___f_5927_, 2, v_inst_5910_);
lean_closure_set(v___f_5927_, 3, v_inst_5911_);
v___x_5928_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___redArg___closed__0));
v___f_5929_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__2), 7, 6);
lean_closure_set(v___f_5929_, 0, v___x_5923_);
lean_closure_set(v___f_5929_, 1, v___x_5928_);
lean_closure_set(v___f_5929_, 2, v_toPure_5926_);
lean_closure_set(v___f_5929_, 3, v_toBind_5921_);
lean_closure_set(v___f_5929_, 4, v_inst_5908_);
lean_closure_set(v___f_5929_, 5, v___f_5927_);
v___x_5930_ = lean_apply_4(v_toBind_5921_, lean_box(0), lean_box(0), v___x_5925_, v___f_5929_);
return v___x_5930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree(lean_object* v_m_5931_, lean_object* v_00_u03b1_5932_, lean_object* v_inst_5933_, lean_object* v_inst_5934_, lean_object* v_inst_5935_, lean_object* v_inst_5936_, lean_object* v_inst_5937_, lean_object* v_cctx_5938_, lean_object* v_ngen_5939_, lean_object* v_env_5940_, lean_object* v_act_5941_, lean_object* v_constantsPerTask_5942_){
_start:
{
lean_object* v___x_5943_; 
v___x_5943_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg(v_inst_5933_, v_inst_5934_, v_inst_5935_, v_inst_5936_, v_inst_5937_, v_cctx_5938_, v_ngen_5939_, v_env_5940_, v_act_5941_, v_constantsPerTask_5942_);
return v___x_5943_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0(void){
_start:
{
lean_object* v___x_5944_; lean_object* v___x_5945_; lean_object* v___x_5946_; 
v___x_5944_ = lean_box(0);
v___x_5945_ = lean_unsigned_to_nat(16u);
v___x_5946_ = lean_mk_array(v___x_5945_, v___x_5944_);
return v___x_5946_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1(void){
_start:
{
lean_object* v___x_5947_; lean_object* v___x_5948_; lean_object* v___x_5949_; 
v___x_5947_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0, &l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0);
v___x_5948_ = lean_unsigned_to_nat(0u);
v___x_5949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5949_, 0, v___x_5948_);
lean_ctor_set(v___x_5949_, 1, v___x_5947_);
return v___x_5949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createTreeCtx(lean_object* v_ctx_5950_){
_start:
{
lean_object* v_toCold_5951_; lean_object* v_ref_5952_; lean_object* v___x_5954_; uint8_t v_isShared_5955_; uint8_t v_isSharedCheck_5987_; 
v_toCold_5951_ = lean_ctor_get(v_ctx_5950_, 0);
v_ref_5952_ = lean_ctor_get(v_ctx_5950_, 2);
v_isSharedCheck_5987_ = !lean_is_exclusive(v_ctx_5950_);
if (v_isSharedCheck_5987_ == 0)
{
lean_object* v_unused_5988_; 
v_unused_5988_ = lean_ctor_get(v_ctx_5950_, 1);
lean_dec(v_unused_5988_);
v___x_5954_ = v_ctx_5950_;
v_isShared_5955_ = v_isSharedCheck_5987_;
goto v_resetjp_5953_;
}
else
{
lean_inc(v_ref_5952_);
lean_inc(v_toCold_5951_);
lean_dec(v_ctx_5950_);
v___x_5954_ = lean_box(0);
v_isShared_5955_ = v_isSharedCheck_5987_;
goto v_resetjp_5953_;
}
v_resetjp_5953_:
{
lean_object* v_fileName_5956_; lean_object* v_fileMap_5957_; lean_object* v_options_5958_; lean_object* v_maxRecDepth_5959_; lean_object* v___x_5961_; uint8_t v_isShared_5962_; uint8_t v_isSharedCheck_5978_; 
v_fileName_5956_ = lean_ctor_get(v_toCold_5951_, 0);
v_fileMap_5957_ = lean_ctor_get(v_toCold_5951_, 1);
v_options_5958_ = lean_ctor_get(v_toCold_5951_, 2);
v_maxRecDepth_5959_ = lean_ctor_get(v_toCold_5951_, 3);
v_isSharedCheck_5978_ = !lean_is_exclusive(v_toCold_5951_);
if (v_isSharedCheck_5978_ == 0)
{
lean_object* v_unused_5979_; lean_object* v_unused_5980_; lean_object* v_unused_5981_; lean_object* v_unused_5982_; lean_object* v_unused_5983_; lean_object* v_unused_5984_; lean_object* v_unused_5985_; lean_object* v_unused_5986_; 
v_unused_5979_ = lean_ctor_get(v_toCold_5951_, 11);
lean_dec(v_unused_5979_);
v_unused_5980_ = lean_ctor_get(v_toCold_5951_, 10);
lean_dec(v_unused_5980_);
v_unused_5981_ = lean_ctor_get(v_toCold_5951_, 9);
lean_dec(v_unused_5981_);
v_unused_5982_ = lean_ctor_get(v_toCold_5951_, 8);
lean_dec(v_unused_5982_);
v_unused_5983_ = lean_ctor_get(v_toCold_5951_, 7);
lean_dec(v_unused_5983_);
v_unused_5984_ = lean_ctor_get(v_toCold_5951_, 6);
lean_dec(v_unused_5984_);
v_unused_5985_ = lean_ctor_get(v_toCold_5951_, 5);
lean_dec(v_unused_5985_);
v_unused_5986_ = lean_ctor_get(v_toCold_5951_, 4);
lean_dec(v_unused_5986_);
v___x_5961_ = v_toCold_5951_;
v_isShared_5962_ = v_isSharedCheck_5978_;
goto v_resetjp_5960_;
}
else
{
lean_inc(v_maxRecDepth_5959_);
lean_inc(v_options_5958_);
lean_inc(v_fileMap_5957_);
lean_inc(v_fileName_5956_);
lean_dec(v_toCold_5951_);
v___x_5961_ = lean_box(0);
v_isShared_5962_ = v_isSharedCheck_5978_;
goto v_resetjp_5960_;
}
v_resetjp_5960_:
{
lean_object* v___x_5963_; lean_object* v___x_5964_; lean_object* v___x_5965_; lean_object* v___x_5966_; lean_object* v___x_5967_; lean_object* v___x_5968_; lean_object* v___x_5970_; 
v___x_5963_ = lean_box(0);
v___x_5964_ = lean_box(0);
v___x_5965_ = lean_unsigned_to_nat(0u);
v___x_5966_ = l_Lean_firstFrontendMacroScope;
v___x_5967_ = lean_box(0);
v___x_5968_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1, &l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1);
lean_inc_ref(v_options_5958_);
if (v_isShared_5962_ == 0)
{
lean_ctor_set(v___x_5961_, 11, v___x_5968_);
lean_ctor_set(v___x_5961_, 10, v___x_5967_);
lean_ctor_set(v___x_5961_, 9, v___x_5966_);
lean_ctor_set(v___x_5961_, 8, v___x_5963_);
lean_ctor_set(v___x_5961_, 7, v___x_5965_);
lean_ctor_set(v___x_5961_, 6, v___x_5965_);
lean_ctor_set(v___x_5961_, 5, v___x_5964_);
lean_ctor_set(v___x_5961_, 4, v___x_5963_);
v___x_5970_ = v___x_5961_;
goto v_reusejp_5969_;
}
else
{
lean_object* v_reuseFailAlloc_5977_; 
v_reuseFailAlloc_5977_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_5977_, 0, v_fileName_5956_);
lean_ctor_set(v_reuseFailAlloc_5977_, 1, v_fileMap_5957_);
lean_ctor_set(v_reuseFailAlloc_5977_, 2, v_options_5958_);
lean_ctor_set(v_reuseFailAlloc_5977_, 3, v_maxRecDepth_5959_);
lean_ctor_set(v_reuseFailAlloc_5977_, 4, v___x_5963_);
lean_ctor_set(v_reuseFailAlloc_5977_, 5, v___x_5964_);
lean_ctor_set(v_reuseFailAlloc_5977_, 6, v___x_5965_);
lean_ctor_set(v_reuseFailAlloc_5977_, 7, v___x_5965_);
lean_ctor_set(v_reuseFailAlloc_5977_, 8, v___x_5963_);
lean_ctor_set(v_reuseFailAlloc_5977_, 9, v___x_5966_);
lean_ctor_set(v_reuseFailAlloc_5977_, 10, v___x_5967_);
lean_ctor_set(v_reuseFailAlloc_5977_, 11, v___x_5968_);
v___x_5970_ = v_reuseFailAlloc_5977_;
goto v_reusejp_5969_;
}
v_reusejp_5969_:
{
uint16_t v___x_5971_; uint8_t v___x_5972_; uint8_t v___x_5973_; lean_object* v___x_5975_; 
v___x_5971_ = l_Lean_OptionFlags_ofOptions(v_options_5958_);
lean_dec_ref(v_options_5958_);
v___x_5972_ = 0;
v___x_5973_ = 0;
if (v_isShared_5955_ == 0)
{
lean_ctor_set(v___x_5954_, 1, v___x_5965_);
lean_ctor_set(v___x_5954_, 0, v___x_5970_);
v___x_5975_ = v___x_5954_;
goto v_reusejp_5974_;
}
else
{
lean_object* v_reuseFailAlloc_5976_; 
v_reuseFailAlloc_5976_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_5976_, 0, v___x_5970_);
lean_ctor_set(v_reuseFailAlloc_5976_, 1, v___x_5965_);
lean_ctor_set(v_reuseFailAlloc_5976_, 2, v_ref_5952_);
v___x_5975_ = v_reuseFailAlloc_5976_;
goto v_reusejp_5974_;
}
v_reusejp_5974_:
{
lean_ctor_set_uint16(v___x_5975_, sizeof(void*)*3, v___x_5971_);
lean_ctor_set_uint8(v___x_5975_, sizeof(void*)*3 + 2, v___x_5972_);
lean_ctor_set_uint8(v___x_5975_, sizeof(void*)*3 + 3, v___x_5973_);
lean_ctor_set_uint8(v___x_5975_, sizeof(void*)*3 + 4, v___x_5972_);
return v___x_5975_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(lean_object* v_category_5989_, lean_object* v_opts_5990_, lean_object* v_act_5991_, lean_object* v_decl_5992_, lean_object* v___y_5993_, lean_object* v___y_5994_, lean_object* v___y_5995_, lean_object* v___y_5996_){
_start:
{
lean_object* v___x_5998_; lean_object* v___x_5999_; 
lean_inc(v___y_5996_);
lean_inc_ref(v___y_5995_);
lean_inc(v___y_5994_);
lean_inc_ref(v___y_5993_);
v___x_5998_ = lean_apply_4(v_act_5991_, v___y_5993_, v___y_5994_, v___y_5995_, v___y_5996_);
v___x_5999_ = l_Lean_profileitIOUnsafe___redArg(v_category_5989_, v_opts_5990_, v___x_5998_, v_decl_5992_);
return v___x_5999_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg___boxed(lean_object* v_category_6000_, lean_object* v_opts_6001_, lean_object* v_act_6002_, lean_object* v_decl_6003_, lean_object* v___y_6004_, lean_object* v___y_6005_, lean_object* v___y_6006_, lean_object* v___y_6007_, lean_object* v___y_6008_){
_start:
{
lean_object* v_res_6009_; 
v_res_6009_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v_category_6000_, v_opts_6001_, v_act_6002_, v_decl_6003_, v___y_6004_, v___y_6005_, v___y_6006_, v___y_6007_);
lean_dec(v___y_6007_);
lean_dec_ref(v___y_6006_);
lean_dec(v___y_6005_);
lean_dec_ref(v___y_6004_);
lean_dec_ref(v_opts_6001_);
lean_dec_ref(v_category_6000_);
return v_res_6009_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1(lean_object* v_00_u03b1_6010_, lean_object* v_category_6011_, lean_object* v_opts_6012_, lean_object* v_act_6013_, lean_object* v_decl_6014_, lean_object* v___y_6015_, lean_object* v___y_6016_, lean_object* v___y_6017_, lean_object* v___y_6018_){
_start:
{
lean_object* v___x_6020_; 
v___x_6020_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v_category_6011_, v_opts_6012_, v_act_6013_, v_decl_6014_, v___y_6015_, v___y_6016_, v___y_6017_, v___y_6018_);
return v___x_6020_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___boxed(lean_object* v_00_u03b1_6021_, lean_object* v_category_6022_, lean_object* v_opts_6023_, lean_object* v_act_6024_, lean_object* v_decl_6025_, lean_object* v___y_6026_, lean_object* v___y_6027_, lean_object* v___y_6028_, lean_object* v___y_6029_, lean_object* v___y_6030_){
_start:
{
lean_object* v_res_6031_; 
v_res_6031_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1(v_00_u03b1_6021_, v_category_6022_, v_opts_6023_, v_act_6024_, v_decl_6025_, v___y_6026_, v___y_6027_, v___y_6028_, v___y_6029_);
lean_dec(v___y_6029_);
lean_dec_ref(v___y_6028_);
lean_dec(v___y_6027_);
lean_dec_ref(v___y_6026_);
lean_dec_ref(v_opts_6023_);
lean_dec_ref(v_category_6022_);
return v_res_6031_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(lean_object* v_cctx_6032_, lean_object* v_env_6033_, lean_object* v_act_6034_, lean_object* v_constantsPerTask_6035_, lean_object* v_n_6036_, lean_object* v_ngen_6037_, lean_object* v_tasks_6038_, lean_object* v_start_6039_, lean_object* v_cnt_6040_, lean_object* v_idx_6041_){
_start:
{
lean_object* v___x_6043_; lean_object* v_moduleData_6044_; lean_object* v___x_6045_; uint8_t v___x_6046_; 
v___x_6043_ = l_Lean_Environment_header(v_env_6033_);
v_moduleData_6044_ = lean_ctor_get(v___x_6043_, 7);
lean_inc_ref(v_moduleData_6044_);
lean_dec_ref(v___x_6043_);
v___x_6045_ = lean_array_get_size(v_moduleData_6044_);
v___x_6046_ = lean_nat_dec_lt(v_idx_6041_, v___x_6045_);
if (v___x_6046_ == 0)
{
uint8_t v___x_6047_; 
lean_dec_ref(v_moduleData_6044_);
lean_dec(v_idx_6041_);
lean_dec(v_cnt_6040_);
v___x_6047_ = lean_nat_dec_lt(v_start_6039_, v_n_6036_);
if (v___x_6047_ == 0)
{
lean_object* v___x_6048_; 
lean_dec(v_start_6039_);
lean_dec_ref(v_ngen_6037_);
lean_dec(v_n_6036_);
lean_dec_ref(v_act_6034_);
lean_dec_ref(v_env_6033_);
lean_dec_ref(v_cctx_6032_);
v___x_6048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6048_, 0, v_tasks_6038_);
return v___x_6048_;
}
else
{
lean_object* v_namePrefix_6049_; lean_object* v_idx_6050_; lean_object* v___x_6052_; uint8_t v_isShared_6053_; uint8_t v_isSharedCheck_6064_; 
v_namePrefix_6049_ = lean_ctor_get(v_ngen_6037_, 0);
v_idx_6050_ = lean_ctor_get(v_ngen_6037_, 1);
v_isSharedCheck_6064_ = !lean_is_exclusive(v_ngen_6037_);
if (v_isSharedCheck_6064_ == 0)
{
v___x_6052_ = v_ngen_6037_;
v_isShared_6053_ = v_isSharedCheck_6064_;
goto v_resetjp_6051_;
}
else
{
lean_inc(v_idx_6050_);
lean_inc(v_namePrefix_6049_);
lean_dec(v_ngen_6037_);
v___x_6052_ = lean_box(0);
v_isShared_6053_ = v_isSharedCheck_6064_;
goto v_resetjp_6051_;
}
v_resetjp_6051_:
{
lean_object* v___x_6054_; lean_object* v___x_6055_; lean_object* v___x_6057_; 
v___x_6054_ = l_Lean_Name_num___override(v_namePrefix_6049_, v_idx_6050_);
v___x_6055_ = lean_unsigned_to_nat(1u);
if (v_isShared_6053_ == 0)
{
lean_ctor_set(v___x_6052_, 1, v___x_6055_);
lean_ctor_set(v___x_6052_, 0, v___x_6054_);
v___x_6057_ = v___x_6052_;
goto v_reusejp_6056_;
}
else
{
lean_object* v_reuseFailAlloc_6063_; 
v_reuseFailAlloc_6063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6063_, 0, v___x_6054_);
lean_ctor_set(v_reuseFailAlloc_6063_, 1, v___x_6055_);
v___x_6057_ = v_reuseFailAlloc_6063_;
goto v_reusejp_6056_;
}
v_reusejp_6056_:
{
lean_object* v___x_6058_; lean_object* v___x_6059_; lean_object* v___x_6060_; lean_object* v___x_6061_; lean_object* v___x_6062_; 
v___x_6058_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_6058_, 0, lean_box(0));
lean_closure_set(v___x_6058_, 1, v_cctx_6032_);
lean_closure_set(v___x_6058_, 2, v___x_6057_);
lean_closure_set(v___x_6058_, 3, v_env_6033_);
lean_closure_set(v___x_6058_, 4, v_act_6034_);
lean_closure_set(v___x_6058_, 5, v_start_6039_);
lean_closure_set(v___x_6058_, 6, v_n_6036_);
v___x_6059_ = lean_unsigned_to_nat(0u);
v___x_6060_ = lean_io_as_task(v___x_6058_, v___x_6059_);
v___x_6061_ = lean_array_push(v_tasks_6038_, v___x_6060_);
v___x_6062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6062_, 0, v___x_6061_);
return v___x_6062_;
}
}
}
}
else
{
lean_object* v_mdata_6065_; lean_object* v_constants_6066_; lean_object* v___x_6067_; lean_object* v_cnt_6068_; uint8_t v___x_6069_; 
v_mdata_6065_ = lean_array_fget(v_moduleData_6044_, v_idx_6041_);
lean_dec_ref(v_moduleData_6044_);
v_constants_6066_ = lean_ctor_get(v_mdata_6065_, 2);
lean_inc_ref(v_constants_6066_);
lean_dec(v_mdata_6065_);
v___x_6067_ = lean_array_get_size(v_constants_6066_);
lean_dec_ref(v_constants_6066_);
v_cnt_6068_ = lean_nat_add(v_cnt_6040_, v___x_6067_);
lean_dec(v_cnt_6040_);
v___x_6069_ = lean_nat_dec_lt(v_constantsPerTask_6035_, v_cnt_6068_);
if (v___x_6069_ == 0)
{
lean_object* v___x_6070_; lean_object* v___x_6071_; 
v___x_6070_ = lean_unsigned_to_nat(1u);
v___x_6071_ = lean_nat_add(v_idx_6041_, v___x_6070_);
lean_dec(v_idx_6041_);
v_cnt_6040_ = v_cnt_6068_;
v_idx_6041_ = v___x_6071_;
goto _start;
}
else
{
lean_object* v_namePrefix_6073_; lean_object* v_idx_6074_; lean_object* v___x_6076_; uint8_t v_isShared_6077_; uint8_t v_isSharedCheck_6091_; 
lean_dec(v_cnt_6068_);
v_namePrefix_6073_ = lean_ctor_get(v_ngen_6037_, 0);
v_idx_6074_ = lean_ctor_get(v_ngen_6037_, 1);
v_isSharedCheck_6091_ = !lean_is_exclusive(v_ngen_6037_);
if (v_isSharedCheck_6091_ == 0)
{
v___x_6076_ = v_ngen_6037_;
v_isShared_6077_ = v_isSharedCheck_6091_;
goto v_resetjp_6075_;
}
else
{
lean_inc(v_idx_6074_);
lean_inc(v_namePrefix_6073_);
lean_dec(v_ngen_6037_);
v___x_6076_ = lean_box(0);
v_isShared_6077_ = v_isSharedCheck_6091_;
goto v_resetjp_6075_;
}
v_resetjp_6075_:
{
lean_object* v___x_6078_; lean_object* v___x_6079_; lean_object* v___x_6081_; 
lean_inc(v_idx_6074_);
lean_inc(v_namePrefix_6073_);
v___x_6078_ = l_Lean_Name_num___override(v_namePrefix_6073_, v_idx_6074_);
v___x_6079_ = lean_unsigned_to_nat(1u);
if (v_isShared_6077_ == 0)
{
lean_ctor_set(v___x_6076_, 1, v___x_6079_);
lean_ctor_set(v___x_6076_, 0, v___x_6078_);
v___x_6081_ = v___x_6076_;
goto v_reusejp_6080_;
}
else
{
lean_object* v_reuseFailAlloc_6090_; 
v_reuseFailAlloc_6090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6090_, 0, v___x_6078_);
lean_ctor_set(v_reuseFailAlloc_6090_, 1, v___x_6079_);
v___x_6081_ = v_reuseFailAlloc_6090_;
goto v_reusejp_6080_;
}
v_reusejp_6080_:
{
lean_object* v___x_6082_; lean_object* v___x_6083_; lean_object* v___x_6084_; lean_object* v___x_6085_; lean_object* v___x_6086_; lean_object* v___x_6087_; lean_object* v___x_6088_; 
v___x_6082_ = lean_nat_add(v_idx_6074_, v___x_6079_);
lean_dec(v_idx_6074_);
v___x_6083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6083_, 0, v_namePrefix_6073_);
lean_ctor_set(v___x_6083_, 1, v___x_6082_);
v___x_6084_ = lean_nat_add(v_idx_6041_, v___x_6079_);
lean_dec(v_idx_6041_);
lean_inc_n(v___x_6084_, 2);
lean_inc_ref(v_act_6034_);
lean_inc_ref(v_env_6033_);
lean_inc_ref(v_cctx_6032_);
v___x_6085_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_6085_, 0, lean_box(0));
lean_closure_set(v___x_6085_, 1, v_cctx_6032_);
lean_closure_set(v___x_6085_, 2, v___x_6081_);
lean_closure_set(v___x_6085_, 3, v_env_6033_);
lean_closure_set(v___x_6085_, 4, v_act_6034_);
lean_closure_set(v___x_6085_, 5, v_start_6039_);
lean_closure_set(v___x_6085_, 6, v___x_6084_);
v___x_6086_ = lean_unsigned_to_nat(0u);
v___x_6087_ = lean_io_as_task(v___x_6085_, v___x_6086_);
v___x_6088_ = lean_array_push(v_tasks_6038_, v___x_6087_);
v_ngen_6037_ = v___x_6083_;
v_tasks_6038_ = v___x_6088_;
v_start_6039_ = v___x_6084_;
v_cnt_6040_ = v___x_6086_;
v_idx_6041_ = v___x_6084_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg___boxed(lean_object* v_cctx_6092_, lean_object* v_env_6093_, lean_object* v_act_6094_, lean_object* v_constantsPerTask_6095_, lean_object* v_n_6096_, lean_object* v_ngen_6097_, lean_object* v_tasks_6098_, lean_object* v_start_6099_, lean_object* v_cnt_6100_, lean_object* v_idx_6101_, lean_object* v___y_6102_){
_start:
{
lean_object* v_res_6103_; 
v_res_6103_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(v_cctx_6092_, v_env_6093_, v_act_6094_, v_constantsPerTask_6095_, v_n_6096_, v_ngen_6097_, v_tasks_6098_, v_start_6099_, v_cnt_6100_, v_idx_6101_);
lean_dec(v_constantsPerTask_6095_);
return v_res_6103_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0(uint8_t v_suppressElabErrors_6112_, lean_object* v_x_6113_){
_start:
{
if (lean_obj_tag(v_x_6113_) == 1)
{
lean_object* v_pre_6114_; 
v_pre_6114_ = lean_ctor_get(v_x_6113_, 0);
switch(lean_obj_tag(v_pre_6114_))
{
case 1:
{
lean_object* v_pre_6115_; 
v_pre_6115_ = lean_ctor_get(v_pre_6114_, 0);
switch(lean_obj_tag(v_pre_6115_))
{
case 0:
{
lean_object* v_str_6116_; lean_object* v_str_6117_; lean_object* v___x_6118_; uint8_t v___x_6119_; 
v_str_6116_ = lean_ctor_get(v_x_6113_, 1);
v_str_6117_ = lean_ctor_get(v_pre_6114_, 1);
v___x_6118_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__0));
v___x_6119_ = lean_string_dec_eq(v_str_6117_, v___x_6118_);
if (v___x_6119_ == 0)
{
lean_object* v___x_6120_; uint8_t v___x_6121_; 
v___x_6120_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__1));
v___x_6121_ = lean_string_dec_eq(v_str_6117_, v___x_6120_);
if (v___x_6121_ == 0)
{
return v___x_6121_;
}
else
{
lean_object* v___x_6122_; uint8_t v___x_6123_; 
v___x_6122_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__2));
v___x_6123_ = lean_string_dec_eq(v_str_6116_, v___x_6122_);
if (v___x_6123_ == 0)
{
return v___x_6123_;
}
else
{
return v_suppressElabErrors_6112_;
}
}
}
else
{
lean_object* v___x_6124_; uint8_t v___x_6125_; 
v___x_6124_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__3));
v___x_6125_ = lean_string_dec_eq(v_str_6116_, v___x_6124_);
if (v___x_6125_ == 0)
{
return v___x_6125_;
}
else
{
return v_suppressElabErrors_6112_;
}
}
}
case 1:
{
lean_object* v_pre_6126_; 
v_pre_6126_ = lean_ctor_get(v_pre_6115_, 0);
if (lean_obj_tag(v_pre_6126_) == 0)
{
lean_object* v_str_6127_; lean_object* v_str_6128_; lean_object* v_str_6129_; lean_object* v___x_6130_; uint8_t v___x_6131_; 
v_str_6127_ = lean_ctor_get(v_x_6113_, 1);
v_str_6128_ = lean_ctor_get(v_pre_6114_, 1);
v_str_6129_ = lean_ctor_get(v_pre_6115_, 1);
v___x_6130_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__4));
v___x_6131_ = lean_string_dec_eq(v_str_6129_, v___x_6130_);
if (v___x_6131_ == 0)
{
return v___x_6131_;
}
else
{
lean_object* v___x_6132_; uint8_t v___x_6133_; 
v___x_6132_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__5));
v___x_6133_ = lean_string_dec_eq(v_str_6128_, v___x_6132_);
if (v___x_6133_ == 0)
{
return v___x_6133_;
}
else
{
lean_object* v___x_6134_; uint8_t v___x_6135_; 
v___x_6134_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__6));
v___x_6135_ = lean_string_dec_eq(v_str_6127_, v___x_6134_);
if (v___x_6135_ == 0)
{
return v___x_6135_;
}
else
{
return v_suppressElabErrors_6112_;
}
}
}
}
else
{
uint8_t v___x_6136_; 
v___x_6136_ = 0;
return v___x_6136_;
}
}
default: 
{
uint8_t v___x_6137_; 
v___x_6137_ = 0;
return v___x_6137_;
}
}
}
case 0:
{
lean_object* v_str_6138_; lean_object* v___x_6139_; uint8_t v___x_6140_; 
v_str_6138_ = lean_ctor_get(v_x_6113_, 1);
v___x_6139_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__7));
v___x_6140_ = lean_string_dec_eq(v_str_6138_, v___x_6139_);
if (v___x_6140_ == 0)
{
return v___x_6140_;
}
else
{
return v_suppressElabErrors_6112_;
}
}
default: 
{
uint8_t v___x_6141_; 
v___x_6141_ = 0;
return v___x_6141_;
}
}
}
else
{
uint8_t v___x_6142_; 
v___x_6142_ = 0;
return v___x_6142_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___boxed(lean_object* v_suppressElabErrors_6143_, lean_object* v_x_6144_){
_start:
{
uint8_t v_suppressElabErrors_boxed_6145_; uint8_t v_res_6146_; lean_object* v_r_6147_; 
v_suppressElabErrors_boxed_6145_ = lean_unbox(v_suppressElabErrors_6143_);
v_res_6146_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0(v_suppressElabErrors_boxed_6145_, v_x_6144_);
lean_dec(v_x_6144_);
v_r_6147_ = lean_box(v_res_6146_);
return v_r_6147_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7_spec__9(lean_object* v_opts_6148_, lean_object* v_opt_6149_){
_start:
{
lean_object* v_name_6150_; lean_object* v_defValue_6151_; lean_object* v_map_6152_; lean_object* v___x_6153_; 
v_name_6150_ = lean_ctor_get(v_opt_6149_, 0);
v_defValue_6151_ = lean_ctor_get(v_opt_6149_, 1);
v_map_6152_ = lean_ctor_get(v_opts_6148_, 0);
v___x_6153_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_6152_, v_name_6150_);
if (lean_obj_tag(v___x_6153_) == 0)
{
uint8_t v___x_6154_; 
v___x_6154_ = lean_unbox(v_defValue_6151_);
return v___x_6154_;
}
else
{
lean_object* v_val_6155_; 
v_val_6155_ = lean_ctor_get(v___x_6153_, 0);
lean_inc(v_val_6155_);
lean_dec_ref_known(v___x_6153_, 1);
if (lean_obj_tag(v_val_6155_) == 1)
{
uint8_t v_v_6156_; 
v_v_6156_ = lean_ctor_get_uint8(v_val_6155_, 0);
lean_dec_ref_known(v_val_6155_, 0);
return v_v_6156_;
}
else
{
uint8_t v___x_6157_; 
lean_dec(v_val_6155_);
v___x_6157_ = lean_unbox(v_defValue_6151_);
return v___x_6157_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7_spec__9___boxed(lean_object* v_opts_6158_, lean_object* v_opt_6159_){
_start:
{
uint8_t v_res_6160_; lean_object* v_r_6161_; 
v_res_6160_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7_spec__9(v_opts_6158_, v_opt_6159_);
lean_dec_ref(v_opt_6159_);
lean_dec_ref(v_opts_6158_);
v_r_6161_ = lean_box(v_res_6160_);
return v_r_6161_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7(lean_object* v_ref_6163_, lean_object* v_msgData_6164_, uint8_t v_severity_6165_, uint8_t v_isSilent_6166_, lean_object* v___y_6167_, lean_object* v___y_6168_, lean_object* v___y_6169_, lean_object* v___y_6170_){
_start:
{
uint8_t v___y_6173_; lean_object* v___y_6174_; lean_object* v___y_6175_; lean_object* v___y_6176_; lean_object* v___y_6177_; lean_object* v___y_6178_; uint8_t v___y_6179_; lean_object* v_toCold_6180_; lean_object* v___y_6181_; lean_object* v___y_6210_; lean_object* v___y_6211_; uint8_t v___y_6212_; lean_object* v___y_6213_; uint8_t v___y_6214_; lean_object* v___y_6215_; uint8_t v___y_6216_; lean_object* v___y_6217_; lean_object* v___y_6237_; lean_object* v___y_6238_; uint8_t v___y_6239_; uint8_t v___y_6240_; lean_object* v___y_6241_; uint8_t v___y_6242_; lean_object* v___y_6243_; uint8_t v___y_6247_; uint8_t v___y_6248_; uint8_t v___x_6258_; uint8_t v___y_6260_; uint8_t v___x_6266_; 
v___x_6258_ = 2;
v___x_6266_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6165_, v___x_6258_);
if (v___x_6266_ == 0)
{
v___y_6260_ = v___x_6266_;
goto v___jp_6259_;
}
else
{
uint8_t v___x_6267_; 
lean_inc_ref(v_msgData_6164_);
v___x_6267_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_6164_);
if (v___x_6267_ == 0)
{
v___y_6260_ = v___x_6267_;
goto v___jp_6259_;
}
else
{
lean_object* v___x_6268_; lean_object* v___x_6269_; 
lean_dec_ref(v_msgData_6164_);
v___x_6268_ = lean_box(0);
v___x_6269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6269_, 0, v___x_6268_);
return v___x_6269_;
}
}
v___jp_6172_:
{
lean_object* v_currNamespace_6182_; lean_object* v_openDecls_6183_; lean_object* v___x_6184_; lean_object* v___x_6185_; lean_object* v___x_6186_; lean_object* v___x_6187_; lean_object* v_env_6188_; lean_object* v_nextMacroScope_6189_; lean_object* v_ngen_6190_; lean_object* v_auxDeclNGen_6191_; lean_object* v_traceState_6192_; lean_object* v_cache_6193_; lean_object* v_recordedDeps_6194_; lean_object* v_messages_6195_; lean_object* v_infoState_6196_; lean_object* v_snapshotTasks_6197_; lean_object* v___x_6199_; uint8_t v_isShared_6200_; uint8_t v_isSharedCheck_6208_; 
v_currNamespace_6182_ = lean_ctor_get(v_toCold_6180_, 4);
v_openDecls_6183_ = lean_ctor_get(v_toCold_6180_, 5);
lean_inc(v_openDecls_6183_);
lean_inc(v_currNamespace_6182_);
v___x_6184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6184_, 0, v_currNamespace_6182_);
lean_ctor_set(v___x_6184_, 1, v_openDecls_6183_);
v___x_6185_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6185_, 0, v___x_6184_);
lean_ctor_set(v___x_6185_, 1, v___y_6176_);
lean_inc_ref(v___y_6177_);
lean_inc_ref(v___y_6174_);
v___x_6186_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_6186_, 0, v___y_6174_);
lean_ctor_set(v___x_6186_, 1, v___y_6178_);
lean_ctor_set(v___x_6186_, 2, v___y_6175_);
lean_ctor_set(v___x_6186_, 3, v___y_6177_);
lean_ctor_set(v___x_6186_, 4, v___x_6185_);
lean_ctor_set_uint8(v___x_6186_, sizeof(void*)*5, v___y_6179_);
lean_ctor_set_uint8(v___x_6186_, sizeof(void*)*5 + 1, v___y_6173_);
lean_ctor_set_uint8(v___x_6186_, sizeof(void*)*5 + 2, v_isSilent_6166_);
v___x_6187_ = lean_st_ref_take(v___y_6181_);
v_env_6188_ = lean_ctor_get(v___x_6187_, 0);
v_nextMacroScope_6189_ = lean_ctor_get(v___x_6187_, 1);
v_ngen_6190_ = lean_ctor_get(v___x_6187_, 2);
v_auxDeclNGen_6191_ = lean_ctor_get(v___x_6187_, 3);
v_traceState_6192_ = lean_ctor_get(v___x_6187_, 4);
v_cache_6193_ = lean_ctor_get(v___x_6187_, 5);
v_recordedDeps_6194_ = lean_ctor_get(v___x_6187_, 6);
v_messages_6195_ = lean_ctor_get(v___x_6187_, 7);
v_infoState_6196_ = lean_ctor_get(v___x_6187_, 8);
v_snapshotTasks_6197_ = lean_ctor_get(v___x_6187_, 9);
v_isSharedCheck_6208_ = !lean_is_exclusive(v___x_6187_);
if (v_isSharedCheck_6208_ == 0)
{
v___x_6199_ = v___x_6187_;
v_isShared_6200_ = v_isSharedCheck_6208_;
goto v_resetjp_6198_;
}
else
{
lean_inc(v_snapshotTasks_6197_);
lean_inc(v_infoState_6196_);
lean_inc(v_messages_6195_);
lean_inc(v_recordedDeps_6194_);
lean_inc(v_cache_6193_);
lean_inc(v_traceState_6192_);
lean_inc(v_auxDeclNGen_6191_);
lean_inc(v_ngen_6190_);
lean_inc(v_nextMacroScope_6189_);
lean_inc(v_env_6188_);
lean_dec(v___x_6187_);
v___x_6199_ = lean_box(0);
v_isShared_6200_ = v_isSharedCheck_6208_;
goto v_resetjp_6198_;
}
v_resetjp_6198_:
{
lean_object* v___x_6201_; lean_object* v___x_6202_; lean_object* v___x_6204_; 
v___x_6201_ = lean_box(0);
v___x_6202_ = l_Lean_MessageLog_add(v___x_6186_, v_messages_6195_);
if (v_isShared_6200_ == 0)
{
lean_ctor_set(v___x_6199_, 7, v___x_6202_);
v___x_6204_ = v___x_6199_;
goto v_reusejp_6203_;
}
else
{
lean_object* v_reuseFailAlloc_6207_; 
v_reuseFailAlloc_6207_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6207_, 0, v_env_6188_);
lean_ctor_set(v_reuseFailAlloc_6207_, 1, v_nextMacroScope_6189_);
lean_ctor_set(v_reuseFailAlloc_6207_, 2, v_ngen_6190_);
lean_ctor_set(v_reuseFailAlloc_6207_, 3, v_auxDeclNGen_6191_);
lean_ctor_set(v_reuseFailAlloc_6207_, 4, v_traceState_6192_);
lean_ctor_set(v_reuseFailAlloc_6207_, 5, v_cache_6193_);
lean_ctor_set(v_reuseFailAlloc_6207_, 6, v_recordedDeps_6194_);
lean_ctor_set(v_reuseFailAlloc_6207_, 7, v___x_6202_);
lean_ctor_set(v_reuseFailAlloc_6207_, 8, v_infoState_6196_);
lean_ctor_set(v_reuseFailAlloc_6207_, 9, v_snapshotTasks_6197_);
v___x_6204_ = v_reuseFailAlloc_6207_;
goto v_reusejp_6203_;
}
v_reusejp_6203_:
{
lean_object* v___x_6205_; lean_object* v___x_6206_; 
v___x_6205_ = lean_st_ref_put(v___y_6181_, v___x_6204_);
v___x_6206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6206_, 0, v___x_6201_);
return v___x_6206_;
}
}
}
v___jp_6209_:
{
lean_object* v_fileName_6218_; lean_object* v_fileMap_6219_; lean_object* v___x_6220_; lean_object* v___x_6221_; lean_object* v_a_6222_; lean_object* v___x_6224_; uint8_t v_isShared_6225_; uint8_t v_isSharedCheck_6235_; 
v_fileName_6218_ = lean_ctor_get(v___y_6213_, 0);
v_fileMap_6219_ = lean_ctor_get(v___y_6213_, 1);
v___x_6220_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_6164_);
v___x_6221_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(v___x_6220_, v___y_6167_, v___y_6168_, v___y_6169_, v___y_6170_);
v_a_6222_ = lean_ctor_get(v___x_6221_, 0);
v_isSharedCheck_6235_ = !lean_is_exclusive(v___x_6221_);
if (v_isSharedCheck_6235_ == 0)
{
v___x_6224_ = v___x_6221_;
v_isShared_6225_ = v_isSharedCheck_6235_;
goto v_resetjp_6223_;
}
else
{
lean_inc(v_a_6222_);
lean_dec(v___x_6221_);
v___x_6224_ = lean_box(0);
v_isShared_6225_ = v_isSharedCheck_6235_;
goto v_resetjp_6223_;
}
v_resetjp_6223_:
{
lean_object* v___x_6226_; lean_object* v___x_6227_; lean_object* v___x_6228_; lean_object* v___x_6229_; 
lean_inc_ref_n(v_fileMap_6219_, 2);
v___x_6226_ = l_Lean_FileMap_toPosition(v_fileMap_6219_, v___y_6215_);
lean_dec(v___y_6215_);
v___x_6227_ = l_Lean_FileMap_toPosition(v_fileMap_6219_, v___y_6217_);
lean_dec(v___y_6217_);
v___x_6228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6228_, 0, v___x_6227_);
v___x_6229_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___closed__0));
if (v___y_6214_ == 0)
{
lean_del_object(v___x_6224_);
lean_dec_ref(v___y_6210_);
v___y_6173_ = v___y_6212_;
v___y_6174_ = v_fileName_6218_;
v___y_6175_ = v___x_6228_;
v___y_6176_ = v_a_6222_;
v___y_6177_ = v___x_6229_;
v___y_6178_ = v___x_6226_;
v___y_6179_ = v___y_6216_;
v_toCold_6180_ = v___y_6211_;
v___y_6181_ = v___y_6170_;
goto v___jp_6172_;
}
else
{
uint8_t v___x_6230_; 
lean_inc(v_a_6222_);
v___x_6230_ = l_Lean_MessageData_hasTag(v___y_6210_, v_a_6222_);
if (v___x_6230_ == 0)
{
lean_object* v___x_6231_; lean_object* v___x_6233_; 
lean_dec_ref_known(v___x_6228_, 1);
lean_dec_ref(v___x_6226_);
lean_dec(v_a_6222_);
v___x_6231_ = lean_box(0);
if (v_isShared_6225_ == 0)
{
lean_ctor_set(v___x_6224_, 0, v___x_6231_);
v___x_6233_ = v___x_6224_;
goto v_reusejp_6232_;
}
else
{
lean_object* v_reuseFailAlloc_6234_; 
v_reuseFailAlloc_6234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6234_, 0, v___x_6231_);
v___x_6233_ = v_reuseFailAlloc_6234_;
goto v_reusejp_6232_;
}
v_reusejp_6232_:
{
return v___x_6233_;
}
}
else
{
lean_del_object(v___x_6224_);
v___y_6173_ = v___y_6212_;
v___y_6174_ = v_fileName_6218_;
v___y_6175_ = v___x_6228_;
v___y_6176_ = v_a_6222_;
v___y_6177_ = v___x_6229_;
v___y_6178_ = v___x_6226_;
v___y_6179_ = v___y_6216_;
v_toCold_6180_ = v___y_6211_;
v___y_6181_ = v___y_6170_;
goto v___jp_6172_;
}
}
}
}
v___jp_6236_:
{
lean_object* v___x_6244_; 
v___x_6244_ = l_Lean_Syntax_getTailPos_x3f(v___y_6241_, v___y_6242_);
lean_dec(v___y_6241_);
if (lean_obj_tag(v___x_6244_) == 0)
{
lean_inc(v___y_6243_);
v___y_6210_ = v___y_6237_;
v___y_6211_ = v___y_6238_;
v___y_6212_ = v___y_6240_;
v___y_6213_ = v___y_6238_;
v___y_6214_ = v___y_6239_;
v___y_6215_ = v___y_6243_;
v___y_6216_ = v___y_6242_;
v___y_6217_ = v___y_6243_;
goto v___jp_6209_;
}
else
{
lean_object* v_val_6245_; 
v_val_6245_ = lean_ctor_get(v___x_6244_, 0);
lean_inc(v_val_6245_);
lean_dec_ref_known(v___x_6244_, 1);
v___y_6210_ = v___y_6237_;
v___y_6211_ = v___y_6238_;
v___y_6212_ = v___y_6240_;
v___y_6213_ = v___y_6238_;
v___y_6214_ = v___y_6239_;
v___y_6215_ = v___y_6243_;
v___y_6216_ = v___y_6242_;
v___y_6217_ = v_val_6245_;
goto v___jp_6209_;
}
}
v___jp_6246_:
{
lean_object* v_toCold_6249_; lean_object* v_ref_6250_; uint8_t v_suppressElabErrors_6251_; lean_object* v___x_6252_; lean_object* v___f_6253_; lean_object* v_ref_6254_; lean_object* v___x_6255_; 
v_toCold_6249_ = lean_ctor_get(v___y_6169_, 0);
v_ref_6250_ = lean_ctor_get(v___y_6169_, 2);
v_suppressElabErrors_6251_ = lean_ctor_get_uint8(v___y_6169_, sizeof(void*)*3 + 2);
v___x_6252_ = lean_box(v_suppressElabErrors_6251_);
v___f_6253_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___boxed), 2, 1);
lean_closure_set(v___f_6253_, 0, v___x_6252_);
v_ref_6254_ = l_Lean_replaceRef(v_ref_6163_, v_ref_6250_);
v___x_6255_ = l_Lean_Syntax_getPos_x3f(v_ref_6254_, v___y_6247_);
if (lean_obj_tag(v___x_6255_) == 0)
{
lean_object* v___x_6256_; 
v___x_6256_ = lean_unsigned_to_nat(0u);
v___y_6237_ = v___f_6253_;
v___y_6238_ = v_toCold_6249_;
v___y_6239_ = v_suppressElabErrors_6251_;
v___y_6240_ = v___y_6248_;
v___y_6241_ = v_ref_6254_;
v___y_6242_ = v___y_6247_;
v___y_6243_ = v___x_6256_;
goto v___jp_6236_;
}
else
{
lean_object* v_val_6257_; 
v_val_6257_ = lean_ctor_get(v___x_6255_, 0);
lean_inc(v_val_6257_);
lean_dec_ref_known(v___x_6255_, 1);
v___y_6237_ = v___f_6253_;
v___y_6238_ = v_toCold_6249_;
v___y_6239_ = v_suppressElabErrors_6251_;
v___y_6240_ = v___y_6248_;
v___y_6241_ = v_ref_6254_;
v___y_6242_ = v___y_6247_;
v___y_6243_ = v_val_6257_;
goto v___jp_6236_;
}
}
v___jp_6259_:
{
uint8_t v___x_6261_; uint8_t v___x_6262_; 
v___x_6261_ = 1;
v___x_6262_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6165_, v___x_6261_);
if (v___x_6262_ == 0)
{
v___y_6247_ = v___y_6260_;
v___y_6248_ = v_severity_6165_;
goto v___jp_6246_;
}
else
{
lean_object* v___x_6263_; lean_object* v___x_6264_; uint8_t v___x_6265_; 
v___x_6263_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_6169_);
v___x_6264_ = l_Lean_warningAsError;
v___x_6265_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7_spec__9(v___x_6263_, v___x_6264_);
lean_dec_ref(v___x_6263_);
if (v___x_6265_ == 0)
{
v___y_6247_ = v___y_6260_;
v___y_6248_ = v_severity_6165_;
goto v___jp_6246_;
}
else
{
v___y_6247_ = v___y_6260_;
v___y_6248_ = v___x_6258_;
goto v___jp_6246_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___boxed(lean_object* v_ref_6270_, lean_object* v_msgData_6271_, lean_object* v_severity_6272_, lean_object* v_isSilent_6273_, lean_object* v___y_6274_, lean_object* v___y_6275_, lean_object* v___y_6276_, lean_object* v___y_6277_, lean_object* v___y_6278_){
_start:
{
uint8_t v_severity_boxed_6279_; uint8_t v_isSilent_boxed_6280_; lean_object* v_res_6281_; 
v_severity_boxed_6279_ = lean_unbox(v_severity_6272_);
v_isSilent_boxed_6280_ = lean_unbox(v_isSilent_6273_);
v_res_6281_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7(v_ref_6270_, v_msgData_6271_, v_severity_boxed_6279_, v_isSilent_boxed_6280_, v___y_6274_, v___y_6275_, v___y_6276_, v___y_6277_);
lean_dec(v___y_6277_);
lean_dec_ref(v___y_6276_);
lean_dec(v___y_6275_);
lean_dec_ref(v___y_6274_);
lean_dec(v_ref_6270_);
return v_res_6281_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3(lean_object* v_msgData_6282_, uint8_t v_severity_6283_, uint8_t v_isSilent_6284_, lean_object* v___y_6285_, lean_object* v___y_6286_, lean_object* v___y_6287_, lean_object* v___y_6288_){
_start:
{
lean_object* v_ref_6290_; lean_object* v___x_6291_; 
v_ref_6290_ = lean_ctor_get(v___y_6287_, 2);
v___x_6291_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7(v_ref_6290_, v_msgData_6282_, v_severity_6283_, v_isSilent_6284_, v___y_6285_, v___y_6286_, v___y_6287_, v___y_6288_);
return v___x_6291_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_msgData_6292_, lean_object* v_severity_6293_, lean_object* v_isSilent_6294_, lean_object* v___y_6295_, lean_object* v___y_6296_, lean_object* v___y_6297_, lean_object* v___y_6298_, lean_object* v___y_6299_){
_start:
{
uint8_t v_severity_boxed_6300_; uint8_t v_isSilent_boxed_6301_; lean_object* v_res_6302_; 
v_severity_boxed_6300_ = lean_unbox(v_severity_6293_);
v_isSilent_boxed_6301_ = lean_unbox(v_isSilent_6294_);
v_res_6302_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3(v_msgData_6292_, v_severity_boxed_6300_, v_isSilent_boxed_6301_, v___y_6295_, v___y_6296_, v___y_6297_, v___y_6298_);
lean_dec(v___y_6298_);
lean_dec_ref(v___y_6297_);
lean_dec(v___y_6296_);
lean_dec_ref(v___y_6295_);
return v_res_6302_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2(lean_object* v_msgData_6303_, lean_object* v___y_6304_, lean_object* v___y_6305_, lean_object* v___y_6306_, lean_object* v___y_6307_){
_start:
{
uint8_t v___x_6309_; uint8_t v___x_6310_; lean_object* v___x_6311_; 
v___x_6309_ = 2;
v___x_6310_ = 0;
v___x_6311_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3(v_msgData_6303_, v___x_6309_, v___x_6310_, v___y_6304_, v___y_6305_, v___y_6306_, v___y_6307_);
return v___x_6311_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_6312_, lean_object* v___y_6313_, lean_object* v___y_6314_, lean_object* v___y_6315_, lean_object* v___y_6316_, lean_object* v___y_6317_){
_start:
{
lean_object* v_res_6318_; 
v_res_6318_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2(v_msgData_6312_, v___y_6313_, v___y_6314_, v___y_6315_, v___y_6316_);
lean_dec(v___y_6316_);
lean_dec_ref(v___y_6315_);
lean_dec(v___y_6314_);
lean_dec_ref(v___y_6313_);
return v_res_6318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0(lean_object* v_f_6319_, lean_object* v___y_6320_, lean_object* v___y_6321_, lean_object* v___y_6322_, lean_object* v___y_6323_){
_start:
{
lean_object* v_module_6325_; lean_object* v_const_6326_; lean_object* v_exception_6327_; lean_object* v___x_6328_; lean_object* v___x_6329_; lean_object* v___x_6330_; lean_object* v___x_6331_; lean_object* v___x_6332_; lean_object* v___x_6333_; lean_object* v___x_6334_; lean_object* v___x_6335_; lean_object* v___x_6336_; lean_object* v___x_6337_; lean_object* v___x_6338_; lean_object* v___x_6339_; 
v_module_6325_ = lean_ctor_get(v_f_6319_, 0);
lean_inc(v_module_6325_);
v_const_6326_ = lean_ctor_get(v_f_6319_, 1);
lean_inc(v_const_6326_);
v_exception_6327_ = lean_ctor_get(v_f_6319_, 2);
lean_inc_ref(v_exception_6327_);
lean_dec_ref(v_f_6319_);
v___x_6328_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1);
v___x_6329_ = l_Lean_MessageData_ofName(v_const_6326_);
v___x_6330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6330_, 0, v___x_6328_);
lean_ctor_set(v___x_6330_, 1, v___x_6329_);
v___x_6331_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3);
v___x_6332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6332_, 0, v___x_6330_);
lean_ctor_set(v___x_6332_, 1, v___x_6331_);
v___x_6333_ = l_Lean_MessageData_ofName(v_module_6325_);
v___x_6334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6334_, 0, v___x_6332_);
lean_ctor_set(v___x_6334_, 1, v___x_6333_);
v___x_6335_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5);
v___x_6336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6336_, 0, v___x_6334_);
lean_ctor_set(v___x_6336_, 1, v___x_6335_);
v___x_6337_ = l_Lean_Exception_toMessageData(v_exception_6327_);
v___x_6338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6338_, 0, v___x_6336_);
lean_ctor_set(v___x_6338_, 1, v___x_6337_);
v___x_6339_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2(v___x_6338_, v___y_6320_, v___y_6321_, v___y_6322_, v___y_6323_);
return v___x_6339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0___boxed(lean_object* v_f_6340_, lean_object* v___y_6341_, lean_object* v___y_6342_, lean_object* v___y_6343_, lean_object* v___y_6344_, lean_object* v___y_6345_){
_start:
{
lean_object* v_res_6346_; 
v_res_6346_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0(v_f_6340_, v___y_6341_, v___y_6342_, v___y_6343_, v___y_6344_);
lean_dec(v___y_6344_);
lean_dec_ref(v___y_6343_);
lean_dec(v___y_6342_);
lean_dec_ref(v___y_6341_);
return v_res_6346_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3(lean_object* v_as_6347_, size_t v_i_6348_, size_t v_stop_6349_, lean_object* v_b_6350_, lean_object* v___y_6351_, lean_object* v___y_6352_, lean_object* v___y_6353_, lean_object* v___y_6354_){
_start:
{
uint8_t v___x_6356_; 
v___x_6356_ = lean_usize_dec_eq(v_i_6348_, v_stop_6349_);
if (v___x_6356_ == 0)
{
lean_object* v___x_6357_; lean_object* v___x_6358_; 
v___x_6357_ = lean_array_uget_borrowed(v_as_6347_, v_i_6348_);
lean_inc(v___x_6357_);
v___x_6358_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0(v___x_6357_, v___y_6351_, v___y_6352_, v___y_6353_, v___y_6354_);
if (lean_obj_tag(v___x_6358_) == 0)
{
lean_object* v_a_6359_; size_t v___x_6360_; size_t v___x_6361_; 
v_a_6359_ = lean_ctor_get(v___x_6358_, 0);
lean_inc(v_a_6359_);
lean_dec_ref_known(v___x_6358_, 1);
v___x_6360_ = ((size_t)1ULL);
v___x_6361_ = lean_usize_add(v_i_6348_, v___x_6360_);
v_i_6348_ = v___x_6361_;
v_b_6350_ = v_a_6359_;
goto _start;
}
else
{
return v___x_6358_;
}
}
else
{
lean_object* v___x_6363_; 
v___x_6363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6363_, 0, v_b_6350_);
return v___x_6363_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3___boxed(lean_object* v_as_6364_, lean_object* v_i_6365_, lean_object* v_stop_6366_, lean_object* v_b_6367_, lean_object* v___y_6368_, lean_object* v___y_6369_, lean_object* v___y_6370_, lean_object* v___y_6371_, lean_object* v___y_6372_){
_start:
{
size_t v_i_boxed_6373_; size_t v_stop_boxed_6374_; lean_object* v_res_6375_; 
v_i_boxed_6373_ = lean_unbox_usize(v_i_6365_);
lean_dec(v_i_6365_);
v_stop_boxed_6374_ = lean_unbox_usize(v_stop_6366_);
lean_dec(v_stop_6366_);
v_res_6375_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3(v_as_6364_, v_i_boxed_6373_, v_stop_boxed_6374_, v_b_6367_, v___y_6368_, v___y_6369_, v___y_6370_, v___y_6371_);
lean_dec(v___y_6371_);
lean_dec_ref(v___y_6370_);
lean_dec(v___y_6369_);
lean_dec_ref(v___y_6368_);
lean_dec_ref(v_as_6364_);
return v_res_6375_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(lean_object* v_as_6376_, size_t v_i_6377_, size_t v_stop_6378_, lean_object* v_b_6379_){
_start:
{
uint8_t v___x_6380_; 
v___x_6380_ = lean_usize_dec_eq(v_i_6377_, v_stop_6378_);
if (v___x_6380_ == 0)
{
lean_object* v___x_6381_; lean_object* v___x_6382_; lean_object* v___x_6383_; size_t v___x_6384_; size_t v___x_6385_; 
v___x_6381_ = lean_array_uget_borrowed(v_as_6376_, v_i_6377_);
lean_inc(v___x_6381_);
v___x_6382_ = lean_task_get_own(v___x_6381_);
v___x_6383_ = l_Lean_Meta_LazyDiscrTree_InitResults_append___redArg(v_b_6379_, v___x_6382_);
v___x_6384_ = ((size_t)1ULL);
v___x_6385_ = lean_usize_add(v_i_6377_, v___x_6384_);
v_i_6377_ = v___x_6385_;
v_b_6379_ = v___x_6383_;
goto _start;
}
else
{
return v_b_6379_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_as_6387_, lean_object* v_i_6388_, lean_object* v_stop_6389_, lean_object* v_b_6390_){
_start:
{
size_t v_i_boxed_6391_; size_t v_stop_boxed_6392_; lean_object* v_res_6393_; 
v_i_boxed_6391_ = lean_unbox_usize(v_i_6388_);
lean_dec(v_i_6388_);
v_stop_boxed_6392_ = lean_unbox_usize(v_stop_6389_);
lean_dec(v_stop_6389_);
v_res_6393_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(v_as_6387_, v_i_boxed_6391_, v_stop_boxed_6392_, v_b_6390_);
lean_dec_ref(v_as_6387_);
return v_res_6393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(lean_object* v_z_6394_, lean_object* v_tasks_6395_){
_start:
{
lean_object* v___x_6396_; lean_object* v___x_6397_; uint8_t v___x_6398_; 
v___x_6396_ = lean_unsigned_to_nat(0u);
v___x_6397_ = lean_array_get_size(v_tasks_6395_);
v___x_6398_ = lean_nat_dec_lt(v___x_6396_, v___x_6397_);
if (v___x_6398_ == 0)
{
return v_z_6394_;
}
else
{
size_t v___x_6399_; size_t v___x_6400_; lean_object* v___x_6401_; 
v___x_6399_ = ((size_t)0ULL);
v___x_6400_ = lean_usize_of_nat(v___x_6397_);
v___x_6401_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(v_tasks_6395_, v___x_6399_, v___x_6400_, v_z_6394_);
return v___x_6401_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg___boxed(lean_object* v_z_6402_, lean_object* v_tasks_6403_){
_start:
{
lean_object* v_res_6404_; 
v_res_6404_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(v_z_6402_, v_tasks_6403_);
lean_dec_ref(v_tasks_6403_);
return v_res_6404_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_6405_; lean_object* v___x_6406_; lean_object* v___x_6407_; 
v___x_6405_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
v___x_6406_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2);
v___x_6407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6407_, 0, v___x_6406_);
lean_ctor_set(v___x_6407_, 1, v___x_6405_);
return v___x_6407_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_6408_; lean_object* v___x_6409_; lean_object* v___x_6410_; 
v___x_6408_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
v___x_6409_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0);
v___x_6410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6410_, 0, v___x_6409_);
lean_ctor_set(v___x_6410_, 1, v___x_6408_);
return v___x_6410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(lean_object* v_cctx_6411_, lean_object* v_ngen_6412_, lean_object* v_env_6413_, lean_object* v_act_6414_, lean_object* v_constantsPerTask_6415_, lean_object* v___y_6416_, lean_object* v___y_6417_, lean_object* v___y_6418_, lean_object* v___y_6419_){
_start:
{
lean_object* v___x_6421_; lean_object* v_moduleData_6422_; lean_object* v_n_6423_; lean_object* v___x_6424_; lean_object* v___x_6425_; lean_object* v___x_6426_; lean_object* v_a_6427_; lean_object* v___x_6429_; uint8_t v_isShared_6430_; uint8_t v_isSharedCheck_6462_; 
v___x_6421_ = l_Lean_Environment_header(v_env_6413_);
v_moduleData_6422_ = lean_ctor_get(v___x_6421_, 7);
lean_inc_ref(v_moduleData_6422_);
lean_dec_ref(v___x_6421_);
v_n_6423_ = lean_array_get_size(v_moduleData_6422_);
lean_dec_ref(v_moduleData_6422_);
v___x_6424_ = lean_unsigned_to_nat(0u);
v___x_6425_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
v___x_6426_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(v_cctx_6411_, v_env_6413_, v_act_6414_, v_constantsPerTask_6415_, v_n_6423_, v_ngen_6412_, v___x_6425_, v___x_6424_, v___x_6424_, v___x_6424_);
v_a_6427_ = lean_ctor_get(v___x_6426_, 0);
v_isSharedCheck_6462_ = !lean_is_exclusive(v___x_6426_);
if (v_isSharedCheck_6462_ == 0)
{
v___x_6429_ = v___x_6426_;
v_isShared_6430_ = v_isSharedCheck_6462_;
goto v_resetjp_6428_;
}
else
{
lean_inc(v_a_6427_);
lean_dec(v___x_6426_);
v___x_6429_ = lean_box(0);
v_isShared_6430_ = v_isSharedCheck_6462_;
goto v_resetjp_6428_;
}
v_resetjp_6428_:
{
lean_object* v___x_6431_; lean_object* v_r_6432_; lean_object* v_tree_6433_; lean_object* v_errors_6434_; lean_object* v___x_6435_; uint8_t v___x_6436_; 
v___x_6431_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1);
v_r_6432_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(v___x_6431_, v_a_6427_);
lean_dec(v_a_6427_);
v_tree_6433_ = lean_ctor_get(v_r_6432_, 0);
lean_inc_ref(v_tree_6433_);
v_errors_6434_ = lean_ctor_get(v_r_6432_, 1);
lean_inc_ref(v_errors_6434_);
lean_dec_ref(v_r_6432_);
v___x_6435_ = lean_array_get_size(v_errors_6434_);
v___x_6436_ = lean_nat_dec_lt(v___x_6424_, v___x_6435_);
if (v___x_6436_ == 0)
{
lean_object* v___x_6437_; lean_object* v___x_6439_; 
lean_dec_ref(v_errors_6434_);
v___x_6437_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_tree_6433_);
if (v_isShared_6430_ == 0)
{
lean_ctor_set(v___x_6429_, 0, v___x_6437_);
v___x_6439_ = v___x_6429_;
goto v_reusejp_6438_;
}
else
{
lean_object* v_reuseFailAlloc_6440_; 
v_reuseFailAlloc_6440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6440_, 0, v___x_6437_);
v___x_6439_ = v_reuseFailAlloc_6440_;
goto v_reusejp_6438_;
}
v_reusejp_6438_:
{
return v___x_6439_;
}
}
else
{
lean_object* v___x_6441_; size_t v___x_6442_; size_t v___x_6443_; lean_object* v___x_6444_; 
lean_del_object(v___x_6429_);
v___x_6441_ = lean_box(0);
v___x_6442_ = ((size_t)0ULL);
v___x_6443_ = lean_usize_of_nat(v___x_6435_);
v___x_6444_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3(v_errors_6434_, v___x_6442_, v___x_6443_, v___x_6441_, v___y_6416_, v___y_6417_, v___y_6418_, v___y_6419_);
lean_dec_ref(v_errors_6434_);
if (lean_obj_tag(v___x_6444_) == 0)
{
lean_object* v___x_6446_; uint8_t v_isShared_6447_; uint8_t v_isSharedCheck_6452_; 
v_isSharedCheck_6452_ = !lean_is_exclusive(v___x_6444_);
if (v_isSharedCheck_6452_ == 0)
{
lean_object* v_unused_6453_; 
v_unused_6453_ = lean_ctor_get(v___x_6444_, 0);
lean_dec(v_unused_6453_);
v___x_6446_ = v___x_6444_;
v_isShared_6447_ = v_isSharedCheck_6452_;
goto v_resetjp_6445_;
}
else
{
lean_dec(v___x_6444_);
v___x_6446_ = lean_box(0);
v_isShared_6447_ = v_isSharedCheck_6452_;
goto v_resetjp_6445_;
}
v_resetjp_6445_:
{
lean_object* v___x_6448_; lean_object* v___x_6450_; 
v___x_6448_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_tree_6433_);
if (v_isShared_6447_ == 0)
{
lean_ctor_set(v___x_6446_, 0, v___x_6448_);
v___x_6450_ = v___x_6446_;
goto v_reusejp_6449_;
}
else
{
lean_object* v_reuseFailAlloc_6451_; 
v_reuseFailAlloc_6451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6451_, 0, v___x_6448_);
v___x_6450_ = v_reuseFailAlloc_6451_;
goto v_reusejp_6449_;
}
v_reusejp_6449_:
{
return v___x_6450_;
}
}
}
else
{
lean_object* v_a_6454_; lean_object* v___x_6456_; uint8_t v_isShared_6457_; uint8_t v_isSharedCheck_6461_; 
lean_dec_ref(v_tree_6433_);
v_a_6454_ = lean_ctor_get(v___x_6444_, 0);
v_isSharedCheck_6461_ = !lean_is_exclusive(v___x_6444_);
if (v_isSharedCheck_6461_ == 0)
{
v___x_6456_ = v___x_6444_;
v_isShared_6457_ = v_isSharedCheck_6461_;
goto v_resetjp_6455_;
}
else
{
lean_inc(v_a_6454_);
lean_dec(v___x_6444_);
v___x_6456_ = lean_box(0);
v_isShared_6457_ = v_isSharedCheck_6461_;
goto v_resetjp_6455_;
}
v_resetjp_6455_:
{
lean_object* v___x_6459_; 
if (v_isShared_6457_ == 0)
{
v___x_6459_ = v___x_6456_;
goto v_reusejp_6458_;
}
else
{
lean_object* v_reuseFailAlloc_6460_; 
v_reuseFailAlloc_6460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6460_, 0, v_a_6454_);
v___x_6459_ = v_reuseFailAlloc_6460_;
goto v_reusejp_6458_;
}
v_reusejp_6458_:
{
return v___x_6459_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___boxed(lean_object* v_cctx_6463_, lean_object* v_ngen_6464_, lean_object* v_env_6465_, lean_object* v_act_6466_, lean_object* v_constantsPerTask_6467_, lean_object* v___y_6468_, lean_object* v___y_6469_, lean_object* v___y_6470_, lean_object* v___y_6471_, lean_object* v___y_6472_){
_start:
{
lean_object* v_res_6473_; 
v_res_6473_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(v_cctx_6463_, v_ngen_6464_, v_env_6465_, v_act_6466_, v_constantsPerTask_6467_, v___y_6468_, v___y_6469_, v___y_6470_, v___y_6471_);
lean_dec(v___y_6471_);
lean_dec_ref(v___y_6470_);
lean_dec(v___y_6469_);
lean_dec_ref(v___y_6468_);
lean_dec(v_constantsPerTask_6467_);
return v_res_6473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0(lean_object* v_a_6474_, lean_object* v___x_6475_, lean_object* v_addEntry_6476_, lean_object* v_constantsPerTask_6477_, lean_object* v_droppedEntriesRef_6478_, lean_object* v_droppedKeys_6479_, lean_object* v___y_6480_, lean_object* v___y_6481_, lean_object* v___y_6482_, lean_object* v___y_6483_){
_start:
{
lean_object* v___x_6485_; lean_object* v_env_6486_; lean_object* v___x_6487_; lean_object* v___x_6488_; 
v___x_6485_ = lean_st_ref_get(v___y_6483_);
v_env_6486_ = lean_ctor_get(v___x_6485_, 0);
lean_inc_ref(v_env_6486_);
lean_dec(v___x_6485_);
lean_inc_ref(v_a_6474_);
v___x_6487_ = l_Lean_Meta_LazyDiscrTree_createTreeCtx(v_a_6474_);
v___x_6488_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(v___x_6487_, v___x_6475_, v_env_6486_, v_addEntry_6476_, v_constantsPerTask_6477_, v___y_6480_, v___y_6481_, v___y_6482_, v___y_6483_);
if (lean_obj_tag(v___x_6488_) == 0)
{
if (lean_obj_tag(v_droppedEntriesRef_6478_) == 1)
{
lean_object* v_a_6489_; lean_object* v_val_6490_; lean_object* v___x_6492_; uint8_t v_isShared_6493_; uint8_t v_isSharedCheck_6523_; 
v_a_6489_ = lean_ctor_get(v___x_6488_, 0);
lean_inc(v_a_6489_);
lean_dec_ref_known(v___x_6488_, 1);
v_val_6490_ = lean_ctor_get(v_droppedEntriesRef_6478_, 0);
v_isSharedCheck_6523_ = !lean_is_exclusive(v_droppedEntriesRef_6478_);
if (v_isSharedCheck_6523_ == 0)
{
v___x_6492_ = v_droppedEntriesRef_6478_;
v_isShared_6493_ = v_isSharedCheck_6523_;
goto v_resetjp_6491_;
}
else
{
lean_inc(v_val_6490_);
lean_dec(v_droppedEntriesRef_6478_);
v___x_6492_ = lean_box(0);
v_isShared_6493_ = v_isSharedCheck_6523_;
goto v_resetjp_6491_;
}
v_resetjp_6491_:
{
lean_object* v___x_6494_; 
v___x_6494_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_a_6489_, v_droppedKeys_6479_, v___y_6480_, v___y_6481_, v___y_6482_, v___y_6483_);
lean_dec(v_droppedKeys_6479_);
if (lean_obj_tag(v___x_6494_) == 0)
{
lean_object* v_a_6495_; lean_object* v___x_6497_; uint8_t v_isShared_6498_; uint8_t v_isSharedCheck_6514_; 
v_a_6495_ = lean_ctor_get(v___x_6494_, 0);
v_isSharedCheck_6514_ = !lean_is_exclusive(v___x_6494_);
if (v_isSharedCheck_6514_ == 0)
{
v___x_6497_ = v___x_6494_;
v_isShared_6498_ = v_isSharedCheck_6514_;
goto v_resetjp_6496_;
}
else
{
lean_inc(v_a_6495_);
lean_dec(v___x_6494_);
v___x_6497_ = lean_box(0);
v_isShared_6498_ = v_isSharedCheck_6514_;
goto v_resetjp_6496_;
}
v_resetjp_6496_:
{
lean_object* v_fst_6499_; lean_object* v_snd_6500_; lean_object* v___x_6501_; lean_object* v___y_6503_; 
v_fst_6499_ = lean_ctor_get(v_a_6495_, 0);
lean_inc(v_fst_6499_);
v_snd_6500_ = lean_ctor_get(v_a_6495_, 1);
lean_inc(v_snd_6500_);
lean_dec(v_a_6495_);
v___x_6501_ = lean_st_ref_get(v_val_6490_);
if (lean_obj_tag(v___x_6501_) == 0)
{
lean_object* v___x_6512_; 
v___x_6512_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___y_6503_ = v___x_6512_;
goto v___jp_6502_;
}
else
{
lean_object* v_val_6513_; 
v_val_6513_ = lean_ctor_get(v___x_6501_, 0);
lean_inc(v_val_6513_);
lean_dec_ref_known(v___x_6501_, 1);
v___y_6503_ = v_val_6513_;
goto v___jp_6502_;
}
v___jp_6502_:
{
lean_object* v___x_6504_; lean_object* v___x_6506_; 
v___x_6504_ = l_Array_append___redArg(v___y_6503_, v_fst_6499_);
lean_dec(v_fst_6499_);
if (v_isShared_6493_ == 0)
{
lean_ctor_set(v___x_6492_, 0, v___x_6504_);
v___x_6506_ = v___x_6492_;
goto v_reusejp_6505_;
}
else
{
lean_object* v_reuseFailAlloc_6511_; 
v_reuseFailAlloc_6511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6511_, 0, v___x_6504_);
v___x_6506_ = v_reuseFailAlloc_6511_;
goto v_reusejp_6505_;
}
v_reusejp_6505_:
{
lean_object* v___x_6507_; lean_object* v___x_6509_; 
v___x_6507_ = lean_st_ref_swap(v_val_6490_, v___x_6506_);
lean_dec(v_val_6490_);
lean_dec(v___x_6507_);
if (v_isShared_6498_ == 0)
{
lean_ctor_set(v___x_6497_, 0, v_snd_6500_);
v___x_6509_ = v___x_6497_;
goto v_reusejp_6508_;
}
else
{
lean_object* v_reuseFailAlloc_6510_; 
v_reuseFailAlloc_6510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6510_, 0, v_snd_6500_);
v___x_6509_ = v_reuseFailAlloc_6510_;
goto v_reusejp_6508_;
}
v_reusejp_6508_:
{
return v___x_6509_;
}
}
}
}
}
else
{
lean_object* v_a_6515_; lean_object* v___x_6517_; uint8_t v_isShared_6518_; uint8_t v_isSharedCheck_6522_; 
lean_del_object(v___x_6492_);
lean_dec(v_val_6490_);
v_a_6515_ = lean_ctor_get(v___x_6494_, 0);
v_isSharedCheck_6522_ = !lean_is_exclusive(v___x_6494_);
if (v_isSharedCheck_6522_ == 0)
{
v___x_6517_ = v___x_6494_;
v_isShared_6518_ = v_isSharedCheck_6522_;
goto v_resetjp_6516_;
}
else
{
lean_inc(v_a_6515_);
lean_dec(v___x_6494_);
v___x_6517_ = lean_box(0);
v_isShared_6518_ = v_isSharedCheck_6522_;
goto v_resetjp_6516_;
}
v_resetjp_6516_:
{
lean_object* v___x_6520_; 
if (v_isShared_6518_ == 0)
{
v___x_6520_ = v___x_6517_;
goto v_reusejp_6519_;
}
else
{
lean_object* v_reuseFailAlloc_6521_; 
v_reuseFailAlloc_6521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6521_, 0, v_a_6515_);
v___x_6520_ = v_reuseFailAlloc_6521_;
goto v_reusejp_6519_;
}
v_reusejp_6519_:
{
return v___x_6520_;
}
}
}
}
}
else
{
lean_object* v_a_6524_; lean_object* v___x_6525_; 
lean_dec(v_droppedEntriesRef_6478_);
v_a_6524_ = lean_ctor_get(v___x_6488_, 0);
lean_inc(v_a_6524_);
lean_dec_ref_known(v___x_6488_, 1);
v___x_6525_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_a_6524_, v_droppedKeys_6479_, v___y_6480_, v___y_6481_, v___y_6482_, v___y_6483_);
return v___x_6525_;
}
}
else
{
lean_dec(v_droppedKeys_6479_);
lean_dec(v_droppedEntriesRef_6478_);
return v___x_6488_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0___boxed(lean_object* v_a_6526_, lean_object* v___x_6527_, lean_object* v_addEntry_6528_, lean_object* v_constantsPerTask_6529_, lean_object* v_droppedEntriesRef_6530_, lean_object* v_droppedKeys_6531_, lean_object* v___y_6532_, lean_object* v___y_6533_, lean_object* v___y_6534_, lean_object* v___y_6535_, lean_object* v___y_6536_){
_start:
{
lean_object* v_res_6537_; 
v_res_6537_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0(v_a_6526_, v___x_6527_, v_addEntry_6528_, v_constantsPerTask_6529_, v_droppedEntriesRef_6530_, v_droppedKeys_6531_, v___y_6532_, v___y_6533_, v___y_6534_, v___y_6535_);
lean_dec(v___y_6535_);
lean_dec_ref(v___y_6534_);
lean_dec(v___y_6533_);
lean_dec_ref(v___y_6532_);
lean_dec(v_constantsPerTask_6529_);
lean_dec_ref(v_a_6526_);
return v_res_6537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(lean_object* v_ref_6539_, lean_object* v_addEntry_6540_, lean_object* v_droppedKeys_6541_, lean_object* v_constantsPerTask_6542_, lean_object* v_droppedEntriesRef_6543_, lean_object* v_ty_6544_, lean_object* v_a_6545_, lean_object* v_a_6546_, lean_object* v_a_6547_, lean_object* v_a_6548_){
_start:
{
lean_object* v_a_6551_; lean_object* v___x_6573_; lean_object* v_ngen_6574_; lean_object* v_namePrefix_6575_; lean_object* v_idx_6576_; lean_object* v___x_6578_; uint8_t v_isShared_6579_; uint8_t v_isSharedCheck_6622_; 
v___x_6573_ = lean_st_ref_get(v_a_6548_);
v_ngen_6574_ = lean_ctor_get(v___x_6573_, 2);
lean_inc_ref(v_ngen_6574_);
lean_dec(v___x_6573_);
v_namePrefix_6575_ = lean_ctor_get(v_ngen_6574_, 0);
v_idx_6576_ = lean_ctor_get(v_ngen_6574_, 1);
v_isSharedCheck_6622_ = !lean_is_exclusive(v_ngen_6574_);
if (v_isSharedCheck_6622_ == 0)
{
v___x_6578_ = v_ngen_6574_;
v_isShared_6579_ = v_isSharedCheck_6622_;
goto v_resetjp_6577_;
}
else
{
lean_inc(v_idx_6576_);
lean_inc(v_namePrefix_6575_);
lean_dec(v_ngen_6574_);
v___x_6578_ = lean_box(0);
v_isShared_6579_ = v_isSharedCheck_6622_;
goto v_resetjp_6577_;
}
v___jp_6550_:
{
lean_object* v___x_6552_; 
v___x_6552_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v_a_6551_, v_ty_6544_, v_a_6545_, v_a_6546_, v_a_6547_, v_a_6548_);
if (lean_obj_tag(v___x_6552_) == 0)
{
lean_object* v_a_6553_; lean_object* v___x_6555_; uint8_t v_isShared_6556_; uint8_t v_isSharedCheck_6564_; 
v_a_6553_ = lean_ctor_get(v___x_6552_, 0);
v_isSharedCheck_6564_ = !lean_is_exclusive(v___x_6552_);
if (v_isSharedCheck_6564_ == 0)
{
v___x_6555_ = v___x_6552_;
v_isShared_6556_ = v_isSharedCheck_6564_;
goto v_resetjp_6554_;
}
else
{
lean_inc(v_a_6553_);
lean_dec(v___x_6552_);
v___x_6555_ = lean_box(0);
v_isShared_6556_ = v_isSharedCheck_6564_;
goto v_resetjp_6554_;
}
v_resetjp_6554_:
{
lean_object* v_fst_6557_; lean_object* v_snd_6558_; lean_object* v___x_6559_; lean_object* v___x_6560_; lean_object* v___x_6562_; 
v_fst_6557_ = lean_ctor_get(v_a_6553_, 0);
lean_inc(v_fst_6557_);
v_snd_6558_ = lean_ctor_get(v_a_6553_, 1);
lean_inc(v_snd_6558_);
lean_dec(v_a_6553_);
v___x_6559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6559_, 0, v_snd_6558_);
v___x_6560_ = lean_st_ref_swap(v_ref_6539_, v___x_6559_);
lean_dec(v___x_6560_);
if (v_isShared_6556_ == 0)
{
lean_ctor_set(v___x_6555_, 0, v_fst_6557_);
v___x_6562_ = v___x_6555_;
goto v_reusejp_6561_;
}
else
{
lean_object* v_reuseFailAlloc_6563_; 
v_reuseFailAlloc_6563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6563_, 0, v_fst_6557_);
v___x_6562_ = v_reuseFailAlloc_6563_;
goto v_reusejp_6561_;
}
v_reusejp_6561_:
{
return v___x_6562_;
}
}
}
else
{
lean_object* v_a_6565_; lean_object* v___x_6567_; uint8_t v_isShared_6568_; uint8_t v_isSharedCheck_6572_; 
v_a_6565_ = lean_ctor_get(v___x_6552_, 0);
v_isSharedCheck_6572_ = !lean_is_exclusive(v___x_6552_);
if (v_isSharedCheck_6572_ == 0)
{
v___x_6567_ = v___x_6552_;
v_isShared_6568_ = v_isSharedCheck_6572_;
goto v_resetjp_6566_;
}
else
{
lean_inc(v_a_6565_);
lean_dec(v___x_6552_);
v___x_6567_ = lean_box(0);
v_isShared_6568_ = v_isSharedCheck_6572_;
goto v_resetjp_6566_;
}
v_resetjp_6566_:
{
lean_object* v___x_6570_; 
if (v_isShared_6568_ == 0)
{
v___x_6570_ = v___x_6567_;
goto v_reusejp_6569_;
}
else
{
lean_object* v_reuseFailAlloc_6571_; 
v_reuseFailAlloc_6571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6571_, 0, v_a_6565_);
v___x_6570_ = v_reuseFailAlloc_6571_;
goto v_reusejp_6569_;
}
v_reusejp_6569_:
{
return v___x_6570_;
}
}
}
}
v_resetjp_6577_:
{
lean_object* v___x_6580_; lean_object* v___x_6581_; lean_object* v___x_6583_; 
lean_inc(v_idx_6576_);
lean_inc(v_namePrefix_6575_);
v___x_6580_ = l_Lean_Name_num___override(v_namePrefix_6575_, v_idx_6576_);
v___x_6581_ = lean_unsigned_to_nat(1u);
if (v_isShared_6579_ == 0)
{
lean_ctor_set(v___x_6578_, 1, v___x_6581_);
lean_ctor_set(v___x_6578_, 0, v___x_6580_);
v___x_6583_ = v___x_6578_;
goto v_reusejp_6582_;
}
else
{
lean_object* v_reuseFailAlloc_6621_; 
v_reuseFailAlloc_6621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6621_, 0, v___x_6580_);
lean_ctor_set(v_reuseFailAlloc_6621_, 1, v___x_6581_);
v___x_6583_ = v_reuseFailAlloc_6621_;
goto v_reusejp_6582_;
}
v_reusejp_6582_:
{
lean_object* v___f_6584_; lean_object* v___x_6585_; lean_object* v___x_6586_; lean_object* v___x_6587_; lean_object* v_env_6588_; lean_object* v_nextMacroScope_6589_; lean_object* v_auxDeclNGen_6590_; lean_object* v_traceState_6591_; lean_object* v_cache_6592_; lean_object* v_recordedDeps_6593_; lean_object* v_messages_6594_; lean_object* v_infoState_6595_; lean_object* v_snapshotTasks_6596_; lean_object* v___x_6598_; uint8_t v_isShared_6599_; uint8_t v_isSharedCheck_6619_; 
lean_inc_ref(v_a_6547_);
v___f_6584_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_6584_, 0, v_a_6547_);
lean_closure_set(v___f_6584_, 1, v___x_6583_);
lean_closure_set(v___f_6584_, 2, v_addEntry_6540_);
lean_closure_set(v___f_6584_, 3, v_constantsPerTask_6542_);
lean_closure_set(v___f_6584_, 4, v_droppedEntriesRef_6543_);
lean_closure_set(v___f_6584_, 5, v_droppedKeys_6541_);
v___x_6585_ = lean_nat_add(v_idx_6576_, v___x_6581_);
lean_dec(v_idx_6576_);
v___x_6586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6586_, 0, v_namePrefix_6575_);
lean_ctor_set(v___x_6586_, 1, v___x_6585_);
v___x_6587_ = lean_st_ref_take(v_a_6548_);
v_env_6588_ = lean_ctor_get(v___x_6587_, 0);
v_nextMacroScope_6589_ = lean_ctor_get(v___x_6587_, 1);
v_auxDeclNGen_6590_ = lean_ctor_get(v___x_6587_, 3);
v_traceState_6591_ = lean_ctor_get(v___x_6587_, 4);
v_cache_6592_ = lean_ctor_get(v___x_6587_, 5);
v_recordedDeps_6593_ = lean_ctor_get(v___x_6587_, 6);
v_messages_6594_ = lean_ctor_get(v___x_6587_, 7);
v_infoState_6595_ = lean_ctor_get(v___x_6587_, 8);
v_snapshotTasks_6596_ = lean_ctor_get(v___x_6587_, 9);
v_isSharedCheck_6619_ = !lean_is_exclusive(v___x_6587_);
if (v_isSharedCheck_6619_ == 0)
{
lean_object* v_unused_6620_; 
v_unused_6620_ = lean_ctor_get(v___x_6587_, 2);
lean_dec(v_unused_6620_);
v___x_6598_ = v___x_6587_;
v_isShared_6599_ = v_isSharedCheck_6619_;
goto v_resetjp_6597_;
}
else
{
lean_inc(v_snapshotTasks_6596_);
lean_inc(v_infoState_6595_);
lean_inc(v_messages_6594_);
lean_inc(v_recordedDeps_6593_);
lean_inc(v_cache_6592_);
lean_inc(v_traceState_6591_);
lean_inc(v_auxDeclNGen_6590_);
lean_inc(v_nextMacroScope_6589_);
lean_inc(v_env_6588_);
lean_dec(v___x_6587_);
v___x_6598_ = lean_box(0);
v_isShared_6599_ = v_isSharedCheck_6619_;
goto v_resetjp_6597_;
}
v_resetjp_6597_:
{
lean_object* v___x_6601_; 
if (v_isShared_6599_ == 0)
{
lean_ctor_set(v___x_6598_, 2, v___x_6586_);
v___x_6601_ = v___x_6598_;
goto v_reusejp_6600_;
}
else
{
lean_object* v_reuseFailAlloc_6618_; 
v_reuseFailAlloc_6618_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6618_, 0, v_env_6588_);
lean_ctor_set(v_reuseFailAlloc_6618_, 1, v_nextMacroScope_6589_);
lean_ctor_set(v_reuseFailAlloc_6618_, 2, v___x_6586_);
lean_ctor_set(v_reuseFailAlloc_6618_, 3, v_auxDeclNGen_6590_);
lean_ctor_set(v_reuseFailAlloc_6618_, 4, v_traceState_6591_);
lean_ctor_set(v_reuseFailAlloc_6618_, 5, v_cache_6592_);
lean_ctor_set(v_reuseFailAlloc_6618_, 6, v_recordedDeps_6593_);
lean_ctor_set(v_reuseFailAlloc_6618_, 7, v_messages_6594_);
lean_ctor_set(v_reuseFailAlloc_6618_, 8, v_infoState_6595_);
lean_ctor_set(v_reuseFailAlloc_6618_, 9, v_snapshotTasks_6596_);
v___x_6601_ = v_reuseFailAlloc_6618_;
goto v_reusejp_6600_;
}
v_reusejp_6600_:
{
lean_object* v___x_6602_; lean_object* v___x_6603_; 
v___x_6602_ = lean_st_ref_put(v_a_6548_, v___x_6601_);
v___x_6603_ = lean_st_ref_get(v_ref_6539_);
if (lean_obj_tag(v___x_6603_) == 0)
{
lean_object* v___x_6604_; lean_object* v___x_6605_; lean_object* v___x_6606_; lean_object* v___x_6607_; 
v___x_6604_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_6547_);
v___x_6605_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___closed__0));
v___x_6606_ = lean_box(0);
v___x_6607_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v___x_6605_, v___x_6604_, v___f_6584_, v___x_6606_, v_a_6545_, v_a_6546_, v_a_6547_, v_a_6548_);
lean_dec_ref(v___x_6604_);
if (lean_obj_tag(v___x_6607_) == 0)
{
lean_object* v_a_6608_; 
v_a_6608_ = lean_ctor_get(v___x_6607_, 0);
lean_inc(v_a_6608_);
lean_dec_ref_known(v___x_6607_, 1);
v_a_6551_ = v_a_6608_;
goto v___jp_6550_;
}
else
{
lean_object* v_a_6609_; lean_object* v___x_6611_; uint8_t v_isShared_6612_; uint8_t v_isSharedCheck_6616_; 
lean_dec_ref(v_ty_6544_);
v_a_6609_ = lean_ctor_get(v___x_6607_, 0);
v_isSharedCheck_6616_ = !lean_is_exclusive(v___x_6607_);
if (v_isSharedCheck_6616_ == 0)
{
v___x_6611_ = v___x_6607_;
v_isShared_6612_ = v_isSharedCheck_6616_;
goto v_resetjp_6610_;
}
else
{
lean_inc(v_a_6609_);
lean_dec(v___x_6607_);
v___x_6611_ = lean_box(0);
v_isShared_6612_ = v_isSharedCheck_6616_;
goto v_resetjp_6610_;
}
v_resetjp_6610_:
{
lean_object* v___x_6614_; 
if (v_isShared_6612_ == 0)
{
v___x_6614_ = v___x_6611_;
goto v_reusejp_6613_;
}
else
{
lean_object* v_reuseFailAlloc_6615_; 
v_reuseFailAlloc_6615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6615_, 0, v_a_6609_);
v___x_6614_ = v_reuseFailAlloc_6615_;
goto v_reusejp_6613_;
}
v_reusejp_6613_:
{
return v___x_6614_;
}
}
}
}
else
{
lean_object* v_val_6617_; 
lean_dec_ref(v___f_6584_);
v_val_6617_ = lean_ctor_get(v___x_6603_, 0);
lean_inc(v_val_6617_);
lean_dec_ref_known(v___x_6603_, 1);
v_a_6551_ = v_val_6617_;
goto v___jp_6550_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___boxed(lean_object* v_ref_6623_, lean_object* v_addEntry_6624_, lean_object* v_droppedKeys_6625_, lean_object* v_constantsPerTask_6626_, lean_object* v_droppedEntriesRef_6627_, lean_object* v_ty_6628_, lean_object* v_a_6629_, lean_object* v_a_6630_, lean_object* v_a_6631_, lean_object* v_a_6632_, lean_object* v_a_6633_){
_start:
{
lean_object* v_res_6634_; 
v_res_6634_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(v_ref_6623_, v_addEntry_6624_, v_droppedKeys_6625_, v_constantsPerTask_6626_, v_droppedEntriesRef_6627_, v_ty_6628_, v_a_6629_, v_a_6630_, v_a_6631_, v_a_6632_);
lean_dec(v_a_6632_);
lean_dec_ref(v_a_6631_);
lean_dec(v_a_6630_);
lean_dec_ref(v_a_6629_);
lean_dec(v_ref_6623_);
return v_res_6634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches(lean_object* v_00_u03b1_6635_, lean_object* v_ref_6636_, lean_object* v_addEntry_6637_, lean_object* v_droppedKeys_6638_, lean_object* v_constantsPerTask_6639_, lean_object* v_droppedEntriesRef_6640_, lean_object* v_ty_6641_, lean_object* v_a_6642_, lean_object* v_a_6643_, lean_object* v_a_6644_, lean_object* v_a_6645_){
_start:
{
lean_object* v___x_6647_; 
v___x_6647_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(v_ref_6636_, v_addEntry_6637_, v_droppedKeys_6638_, v_constantsPerTask_6639_, v_droppedEntriesRef_6640_, v_ty_6641_, v_a_6642_, v_a_6643_, v_a_6644_, v_a_6645_);
return v___x_6647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___boxed(lean_object* v_00_u03b1_6648_, lean_object* v_ref_6649_, lean_object* v_addEntry_6650_, lean_object* v_droppedKeys_6651_, lean_object* v_constantsPerTask_6652_, lean_object* v_droppedEntriesRef_6653_, lean_object* v_ty_6654_, lean_object* v_a_6655_, lean_object* v_a_6656_, lean_object* v_a_6657_, lean_object* v_a_6658_, lean_object* v_a_6659_){
_start:
{
lean_object* v_res_6660_; 
v_res_6660_ = l_Lean_Meta_LazyDiscrTree_findImportMatches(v_00_u03b1_6648_, v_ref_6649_, v_addEntry_6650_, v_droppedKeys_6651_, v_constantsPerTask_6652_, v_droppedEntriesRef_6653_, v_ty_6654_, v_a_6655_, v_a_6656_, v_a_6657_, v_a_6658_);
lean_dec(v_a_6658_);
lean_dec_ref(v_a_6657_);
lean_dec(v_a_6656_);
lean_dec_ref(v_a_6655_);
lean_dec(v_ref_6649_);
return v_res_6660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0(lean_object* v_00_u03b1_6661_, lean_object* v_cctx_6662_, lean_object* v_ngen_6663_, lean_object* v_env_6664_, lean_object* v_act_6665_, lean_object* v_constantsPerTask_6666_, lean_object* v___y_6667_, lean_object* v___y_6668_, lean_object* v___y_6669_, lean_object* v___y_6670_){
_start:
{
lean_object* v___x_6672_; 
v___x_6672_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(v_cctx_6662_, v_ngen_6663_, v_env_6664_, v_act_6665_, v_constantsPerTask_6666_, v___y_6667_, v___y_6668_, v___y_6669_, v___y_6670_);
return v___x_6672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___boxed(lean_object* v_00_u03b1_6673_, lean_object* v_cctx_6674_, lean_object* v_ngen_6675_, lean_object* v_env_6676_, lean_object* v_act_6677_, lean_object* v_constantsPerTask_6678_, lean_object* v___y_6679_, lean_object* v___y_6680_, lean_object* v___y_6681_, lean_object* v___y_6682_, lean_object* v___y_6683_){
_start:
{
lean_object* v_res_6684_; 
v_res_6684_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0(v_00_u03b1_6673_, v_cctx_6674_, v_ngen_6675_, v_env_6676_, v_act_6677_, v_constantsPerTask_6678_, v___y_6679_, v___y_6680_, v___y_6681_, v___y_6682_);
lean_dec(v___y_6682_);
lean_dec_ref(v___y_6681_);
lean_dec(v___y_6680_);
lean_dec_ref(v___y_6679_);
lean_dec(v_constantsPerTask_6678_);
return v_res_6684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1(lean_object* v_00_u03b1_6685_, lean_object* v_cctx_6686_, lean_object* v_env_6687_, lean_object* v_act_6688_, lean_object* v_constantsPerTask_6689_, lean_object* v_n_6690_, lean_object* v_ngen_6691_, lean_object* v_tasks_6692_, lean_object* v_start_6693_, lean_object* v_cnt_6694_, lean_object* v_idx_6695_, lean_object* v___y_6696_, lean_object* v___y_6697_, lean_object* v___y_6698_, lean_object* v___y_6699_){
_start:
{
lean_object* v___x_6701_; 
v___x_6701_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(v_cctx_6686_, v_env_6687_, v_act_6688_, v_constantsPerTask_6689_, v_n_6690_, v_ngen_6691_, v_tasks_6692_, v_start_6693_, v_cnt_6694_, v_idx_6695_);
return v___x_6701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___boxed(lean_object* v_00_u03b1_6702_, lean_object* v_cctx_6703_, lean_object* v_env_6704_, lean_object* v_act_6705_, lean_object* v_constantsPerTask_6706_, lean_object* v_n_6707_, lean_object* v_ngen_6708_, lean_object* v_tasks_6709_, lean_object* v_start_6710_, lean_object* v_cnt_6711_, lean_object* v_idx_6712_, lean_object* v___y_6713_, lean_object* v___y_6714_, lean_object* v___y_6715_, lean_object* v___y_6716_, lean_object* v___y_6717_){
_start:
{
lean_object* v_res_6718_; 
v_res_6718_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1(v_00_u03b1_6702_, v_cctx_6703_, v_env_6704_, v_act_6705_, v_constantsPerTask_6706_, v_n_6707_, v_ngen_6708_, v_tasks_6709_, v_start_6710_, v_cnt_6711_, v_idx_6712_, v___y_6713_, v___y_6714_, v___y_6715_, v___y_6716_);
lean_dec(v___y_6716_);
lean_dec_ref(v___y_6715_);
lean_dec(v___y_6714_);
lean_dec_ref(v___y_6713_);
lean_dec(v_constantsPerTask_6706_);
return v_res_6718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2(lean_object* v_00_u03b1_6719_, lean_object* v_z_6720_, lean_object* v_tasks_6721_){
_start:
{
lean_object* v___x_6722_; 
v___x_6722_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(v_z_6720_, v_tasks_6721_);
return v___x_6722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___boxed(lean_object* v_00_u03b1_6723_, lean_object* v_z_6724_, lean_object* v_tasks_6725_){
_start:
{
lean_object* v_res_6726_; 
v_res_6726_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2(v_00_u03b1_6723_, v_z_6724_, v_tasks_6725_);
lean_dec_ref(v_tasks_6725_);
return v_res_6726_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5(lean_object* v_00_u03b1_6727_, lean_object* v_as_6728_, size_t v_i_6729_, size_t v_stop_6730_, lean_object* v_b_6731_){
_start:
{
lean_object* v___x_6732_; 
v___x_6732_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(v_as_6728_, v_i_6729_, v_stop_6730_, v_b_6731_);
return v___x_6732_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b1_6733_, lean_object* v_as_6734_, lean_object* v_i_6735_, lean_object* v_stop_6736_, lean_object* v_b_6737_){
_start:
{
size_t v_i_boxed_6738_; size_t v_stop_boxed_6739_; lean_object* v_res_6740_; 
v_i_boxed_6738_ = lean_unbox_usize(v_i_6735_);
lean_dec(v_i_6735_);
v_stop_boxed_6739_ = lean_unbox_usize(v_stop_6736_);
lean_dec(v_stop_6736_);
v_res_6740_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5(v_00_u03b1_6733_, v_as_6734_, v_i_boxed_6738_, v_stop_boxed_6739_, v_b_6737_);
lean_dec_ref(v_as_6734_);
return v_res_6740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(lean_object* v___y_6741_){
_start:
{
lean_object* v___x_6743_; lean_object* v_ngen_6744_; lean_object* v_namePrefix_6745_; lean_object* v_idx_6746_; lean_object* v___x_6748_; uint8_t v_isShared_6749_; uint8_t v_isSharedCheck_6777_; 
v___x_6743_ = lean_st_ref_get(v___y_6741_);
v_ngen_6744_ = lean_ctor_get(v___x_6743_, 2);
lean_inc_ref(v_ngen_6744_);
lean_dec(v___x_6743_);
v_namePrefix_6745_ = lean_ctor_get(v_ngen_6744_, 0);
v_idx_6746_ = lean_ctor_get(v_ngen_6744_, 1);
v_isSharedCheck_6777_ = !lean_is_exclusive(v_ngen_6744_);
if (v_isSharedCheck_6777_ == 0)
{
v___x_6748_ = v_ngen_6744_;
v_isShared_6749_ = v_isSharedCheck_6777_;
goto v_resetjp_6747_;
}
else
{
lean_inc(v_idx_6746_);
lean_inc(v_namePrefix_6745_);
lean_dec(v_ngen_6744_);
v___x_6748_ = lean_box(0);
v_isShared_6749_ = v_isSharedCheck_6777_;
goto v_resetjp_6747_;
}
v_resetjp_6747_:
{
lean_object* v___x_6750_; lean_object* v___x_6751_; lean_object* v___x_6753_; 
lean_inc(v_idx_6746_);
lean_inc(v_namePrefix_6745_);
v___x_6750_ = l_Lean_Name_num___override(v_namePrefix_6745_, v_idx_6746_);
v___x_6751_ = lean_unsigned_to_nat(1u);
if (v_isShared_6749_ == 0)
{
lean_ctor_set(v___x_6748_, 1, v___x_6751_);
lean_ctor_set(v___x_6748_, 0, v___x_6750_);
v___x_6753_ = v___x_6748_;
goto v_reusejp_6752_;
}
else
{
lean_object* v_reuseFailAlloc_6776_; 
v_reuseFailAlloc_6776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6776_, 0, v___x_6750_);
lean_ctor_set(v_reuseFailAlloc_6776_, 1, v___x_6751_);
v___x_6753_ = v_reuseFailAlloc_6776_;
goto v_reusejp_6752_;
}
v_reusejp_6752_:
{
lean_object* v___x_6754_; lean_object* v___x_6755_; lean_object* v___x_6756_; lean_object* v_env_6757_; lean_object* v_nextMacroScope_6758_; lean_object* v_auxDeclNGen_6759_; lean_object* v_traceState_6760_; lean_object* v_cache_6761_; lean_object* v_recordedDeps_6762_; lean_object* v_messages_6763_; lean_object* v_infoState_6764_; lean_object* v_snapshotTasks_6765_; lean_object* v___x_6767_; uint8_t v_isShared_6768_; uint8_t v_isSharedCheck_6774_; 
v___x_6754_ = lean_nat_add(v_idx_6746_, v___x_6751_);
lean_dec(v_idx_6746_);
v___x_6755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6755_, 0, v_namePrefix_6745_);
lean_ctor_set(v___x_6755_, 1, v___x_6754_);
v___x_6756_ = lean_st_ref_take(v___y_6741_);
v_env_6757_ = lean_ctor_get(v___x_6756_, 0);
v_nextMacroScope_6758_ = lean_ctor_get(v___x_6756_, 1);
v_auxDeclNGen_6759_ = lean_ctor_get(v___x_6756_, 3);
v_traceState_6760_ = lean_ctor_get(v___x_6756_, 4);
v_cache_6761_ = lean_ctor_get(v___x_6756_, 5);
v_recordedDeps_6762_ = lean_ctor_get(v___x_6756_, 6);
v_messages_6763_ = lean_ctor_get(v___x_6756_, 7);
v_infoState_6764_ = lean_ctor_get(v___x_6756_, 8);
v_snapshotTasks_6765_ = lean_ctor_get(v___x_6756_, 9);
v_isSharedCheck_6774_ = !lean_is_exclusive(v___x_6756_);
if (v_isSharedCheck_6774_ == 0)
{
lean_object* v_unused_6775_; 
v_unused_6775_ = lean_ctor_get(v___x_6756_, 2);
lean_dec(v_unused_6775_);
v___x_6767_ = v___x_6756_;
v_isShared_6768_ = v_isSharedCheck_6774_;
goto v_resetjp_6766_;
}
else
{
lean_inc(v_snapshotTasks_6765_);
lean_inc(v_infoState_6764_);
lean_inc(v_messages_6763_);
lean_inc(v_recordedDeps_6762_);
lean_inc(v_cache_6761_);
lean_inc(v_traceState_6760_);
lean_inc(v_auxDeclNGen_6759_);
lean_inc(v_nextMacroScope_6758_);
lean_inc(v_env_6757_);
lean_dec(v___x_6756_);
v___x_6767_ = lean_box(0);
v_isShared_6768_ = v_isSharedCheck_6774_;
goto v_resetjp_6766_;
}
v_resetjp_6766_:
{
lean_object* v___x_6770_; 
if (v_isShared_6768_ == 0)
{
lean_ctor_set(v___x_6767_, 2, v___x_6755_);
v___x_6770_ = v___x_6767_;
goto v_reusejp_6769_;
}
else
{
lean_object* v_reuseFailAlloc_6773_; 
v_reuseFailAlloc_6773_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6773_, 0, v_env_6757_);
lean_ctor_set(v_reuseFailAlloc_6773_, 1, v_nextMacroScope_6758_);
lean_ctor_set(v_reuseFailAlloc_6773_, 2, v___x_6755_);
lean_ctor_set(v_reuseFailAlloc_6773_, 3, v_auxDeclNGen_6759_);
lean_ctor_set(v_reuseFailAlloc_6773_, 4, v_traceState_6760_);
lean_ctor_set(v_reuseFailAlloc_6773_, 5, v_cache_6761_);
lean_ctor_set(v_reuseFailAlloc_6773_, 6, v_recordedDeps_6762_);
lean_ctor_set(v_reuseFailAlloc_6773_, 7, v_messages_6763_);
lean_ctor_set(v_reuseFailAlloc_6773_, 8, v_infoState_6764_);
lean_ctor_set(v_reuseFailAlloc_6773_, 9, v_snapshotTasks_6765_);
v___x_6770_ = v_reuseFailAlloc_6773_;
goto v_reusejp_6769_;
}
v_reusejp_6769_:
{
lean_object* v___x_6771_; lean_object* v___x_6772_; 
v___x_6771_ = lean_st_ref_put(v___y_6741_, v___x_6770_);
v___x_6772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6772_, 0, v___x_6753_);
return v___x_6772_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg___boxed(lean_object* v___y_6778_, lean_object* v___y_6779_){
_start:
{
lean_object* v_res_6780_; 
v_res_6780_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(v___y_6778_);
lean_dec(v___y_6778_);
return v_res_6780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1(lean_object* v___y_6781_, lean_object* v___y_6782_){
_start:
{
lean_object* v___x_6784_; 
v___x_6784_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(v___y_6782_);
return v___x_6784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___boxed(lean_object* v___y_6785_, lean_object* v___y_6786_, lean_object* v___y_6787_){
_start:
{
lean_object* v_res_6788_; 
v_res_6788_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1(v___y_6785_, v___y_6786_);
lean_dec(v___y_6786_);
lean_dec_ref(v___y_6785_);
return v_res_6788_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0(void){
_start:
{
lean_object* v___x_6789_; lean_object* v___x_6790_; lean_object* v___x_6791_; 
v___x_6789_ = lean_unsigned_to_nat(32u);
v___x_6790_ = lean_mk_empty_array_with_capacity(v___x_6789_);
v___x_6791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6791_, 0, v___x_6790_);
return v___x_6791_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1(void){
_start:
{
size_t v___x_6792_; lean_object* v___x_6793_; lean_object* v___x_6794_; lean_object* v___x_6795_; lean_object* v___x_6796_; lean_object* v___x_6797_; 
v___x_6792_ = ((size_t)5ULL);
v___x_6793_ = lean_unsigned_to_nat(0u);
v___x_6794_ = lean_unsigned_to_nat(32u);
v___x_6795_ = lean_mk_empty_array_with_capacity(v___x_6794_);
v___x_6796_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0);
v___x_6797_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_6797_, 0, v___x_6796_);
lean_ctor_set(v___x_6797_, 1, v___x_6795_);
lean_ctor_set(v___x_6797_, 2, v___x_6793_);
lean_ctor_set(v___x_6797_, 3, v___x_6793_);
lean_ctor_set_usize(v___x_6797_, 4, v___x_6792_);
return v___x_6797_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2(void){
_start:
{
lean_object* v___x_6798_; lean_object* v___x_6799_; lean_object* v___x_6800_; lean_object* v___x_6801_; 
v___x_6798_ = lean_box(1);
v___x_6799_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1);
v___x_6800_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0);
v___x_6801_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6801_, 0, v___x_6800_);
lean_ctor_set(v___x_6801_, 1, v___x_6799_);
lean_ctor_set(v___x_6801_, 2, v___x_6798_);
return v___x_6801_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_msgData_6802_, lean_object* v___y_6803_, lean_object* v___y_6804_){
_start:
{
lean_object* v___x_6806_; lean_object* v_toCold_6807_; lean_object* v_env_6808_; lean_object* v_options_6809_; uint8_t v___x_6810_; lean_object* v_env_6811_; lean_object* v___x_6812_; lean_object* v___x_6813_; lean_object* v___x_6814_; lean_object* v___x_6815_; lean_object* v___x_6816_; 
v___x_6806_ = lean_st_ref_get(v___y_6804_);
v_toCold_6807_ = lean_ctor_get(v___y_6803_, 0);
v_env_6808_ = lean_ctor_get(v___x_6806_, 0);
lean_inc_ref(v_env_6808_);
lean_dec(v___x_6806_);
v_options_6809_ = lean_ctor_get(v_toCold_6807_, 2);
v___x_6810_ = 0;
v_env_6811_ = l_Lean_Environment_setRecordingDeps(v_env_6808_, v___x_6810_);
v___x_6812_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_6813_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2);
lean_inc_ref(v_options_6809_);
v___x_6814_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6814_, 0, v_env_6811_);
lean_ctor_set(v___x_6814_, 1, v___x_6812_);
lean_ctor_set(v___x_6814_, 2, v___x_6813_);
lean_ctor_set(v___x_6814_, 3, v_options_6809_);
v___x_6815_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_6815_, 0, v___x_6814_);
lean_ctor_set(v___x_6815_, 1, v_msgData_6802_);
v___x_6816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6816_, 0, v___x_6815_);
return v___x_6816_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(lean_object* v_msgData_6817_, lean_object* v___y_6818_, lean_object* v___y_6819_, lean_object* v___y_6820_){
_start:
{
lean_object* v_res_6821_; 
v_res_6821_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5(v_msgData_6817_, v___y_6818_, v___y_6819_);
lean_dec(v___y_6819_);
lean_dec_ref(v___y_6818_);
return v_res_6821_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4(lean_object* v_ref_6822_, lean_object* v_msgData_6823_, uint8_t v_severity_6824_, uint8_t v_isSilent_6825_, lean_object* v___y_6826_, lean_object* v___y_6827_){
_start:
{
lean_object* v___y_6830_; lean_object* v___y_6831_; uint8_t v___y_6832_; lean_object* v___y_6833_; uint8_t v___y_6834_; lean_object* v___y_6835_; lean_object* v___y_6836_; lean_object* v_toCold_6837_; lean_object* v___y_6838_; lean_object* v___y_6867_; lean_object* v___y_6868_; uint8_t v___y_6869_; uint8_t v___y_6870_; lean_object* v___y_6871_; uint8_t v___y_6872_; lean_object* v___y_6873_; lean_object* v___y_6874_; uint8_t v___y_6894_; lean_object* v___y_6895_; lean_object* v___y_6896_; lean_object* v___y_6897_; uint8_t v___y_6898_; uint8_t v___y_6899_; lean_object* v___y_6900_; uint8_t v___y_6904_; uint8_t v___y_6905_; uint8_t v___x_6915_; uint8_t v___y_6917_; uint8_t v___x_6923_; 
v___x_6915_ = 2;
v___x_6923_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6824_, v___x_6915_);
if (v___x_6923_ == 0)
{
v___y_6917_ = v___x_6923_;
goto v___jp_6916_;
}
else
{
uint8_t v___x_6924_; 
lean_inc_ref(v_msgData_6823_);
v___x_6924_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_6823_);
if (v___x_6924_ == 0)
{
v___y_6917_ = v___x_6924_;
goto v___jp_6916_;
}
else
{
lean_object* v___x_6925_; lean_object* v___x_6926_; 
lean_dec_ref(v_msgData_6823_);
v___x_6925_ = lean_box(0);
v___x_6926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6926_, 0, v___x_6925_);
return v___x_6926_;
}
}
v___jp_6829_:
{
lean_object* v_currNamespace_6839_; lean_object* v_openDecls_6840_; lean_object* v___x_6841_; lean_object* v___x_6842_; lean_object* v___x_6843_; lean_object* v___x_6844_; lean_object* v_env_6845_; lean_object* v_nextMacroScope_6846_; lean_object* v_ngen_6847_; lean_object* v_auxDeclNGen_6848_; lean_object* v_traceState_6849_; lean_object* v_cache_6850_; lean_object* v_recordedDeps_6851_; lean_object* v_messages_6852_; lean_object* v_infoState_6853_; lean_object* v_snapshotTasks_6854_; lean_object* v___x_6856_; uint8_t v_isShared_6857_; uint8_t v_isSharedCheck_6865_; 
v_currNamespace_6839_ = lean_ctor_get(v_toCold_6837_, 4);
v_openDecls_6840_ = lean_ctor_get(v_toCold_6837_, 5);
lean_inc(v_openDecls_6840_);
lean_inc(v_currNamespace_6839_);
v___x_6841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6841_, 0, v_currNamespace_6839_);
lean_ctor_set(v___x_6841_, 1, v_openDecls_6840_);
v___x_6842_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6842_, 0, v___x_6841_);
lean_ctor_set(v___x_6842_, 1, v___y_6835_);
lean_inc_ref(v___y_6836_);
lean_inc_ref(v___y_6831_);
v___x_6843_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_6843_, 0, v___y_6831_);
lean_ctor_set(v___x_6843_, 1, v___y_6833_);
lean_ctor_set(v___x_6843_, 2, v___y_6830_);
lean_ctor_set(v___x_6843_, 3, v___y_6836_);
lean_ctor_set(v___x_6843_, 4, v___x_6842_);
lean_ctor_set_uint8(v___x_6843_, sizeof(void*)*5, v___y_6834_);
lean_ctor_set_uint8(v___x_6843_, sizeof(void*)*5 + 1, v___y_6832_);
lean_ctor_set_uint8(v___x_6843_, sizeof(void*)*5 + 2, v_isSilent_6825_);
v___x_6844_ = lean_st_ref_take(v___y_6838_);
v_env_6845_ = lean_ctor_get(v___x_6844_, 0);
v_nextMacroScope_6846_ = lean_ctor_get(v___x_6844_, 1);
v_ngen_6847_ = lean_ctor_get(v___x_6844_, 2);
v_auxDeclNGen_6848_ = lean_ctor_get(v___x_6844_, 3);
v_traceState_6849_ = lean_ctor_get(v___x_6844_, 4);
v_cache_6850_ = lean_ctor_get(v___x_6844_, 5);
v_recordedDeps_6851_ = lean_ctor_get(v___x_6844_, 6);
v_messages_6852_ = lean_ctor_get(v___x_6844_, 7);
v_infoState_6853_ = lean_ctor_get(v___x_6844_, 8);
v_snapshotTasks_6854_ = lean_ctor_get(v___x_6844_, 9);
v_isSharedCheck_6865_ = !lean_is_exclusive(v___x_6844_);
if (v_isSharedCheck_6865_ == 0)
{
v___x_6856_ = v___x_6844_;
v_isShared_6857_ = v_isSharedCheck_6865_;
goto v_resetjp_6855_;
}
else
{
lean_inc(v_snapshotTasks_6854_);
lean_inc(v_infoState_6853_);
lean_inc(v_messages_6852_);
lean_inc(v_recordedDeps_6851_);
lean_inc(v_cache_6850_);
lean_inc(v_traceState_6849_);
lean_inc(v_auxDeclNGen_6848_);
lean_inc(v_ngen_6847_);
lean_inc(v_nextMacroScope_6846_);
lean_inc(v_env_6845_);
lean_dec(v___x_6844_);
v___x_6856_ = lean_box(0);
v_isShared_6857_ = v_isSharedCheck_6865_;
goto v_resetjp_6855_;
}
v_resetjp_6855_:
{
lean_object* v___x_6858_; lean_object* v___x_6859_; lean_object* v___x_6861_; 
v___x_6858_ = lean_box(0);
v___x_6859_ = l_Lean_MessageLog_add(v___x_6843_, v_messages_6852_);
if (v_isShared_6857_ == 0)
{
lean_ctor_set(v___x_6856_, 7, v___x_6859_);
v___x_6861_ = v___x_6856_;
goto v_reusejp_6860_;
}
else
{
lean_object* v_reuseFailAlloc_6864_; 
v_reuseFailAlloc_6864_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6864_, 0, v_env_6845_);
lean_ctor_set(v_reuseFailAlloc_6864_, 1, v_nextMacroScope_6846_);
lean_ctor_set(v_reuseFailAlloc_6864_, 2, v_ngen_6847_);
lean_ctor_set(v_reuseFailAlloc_6864_, 3, v_auxDeclNGen_6848_);
lean_ctor_set(v_reuseFailAlloc_6864_, 4, v_traceState_6849_);
lean_ctor_set(v_reuseFailAlloc_6864_, 5, v_cache_6850_);
lean_ctor_set(v_reuseFailAlloc_6864_, 6, v_recordedDeps_6851_);
lean_ctor_set(v_reuseFailAlloc_6864_, 7, v___x_6859_);
lean_ctor_set(v_reuseFailAlloc_6864_, 8, v_infoState_6853_);
lean_ctor_set(v_reuseFailAlloc_6864_, 9, v_snapshotTasks_6854_);
v___x_6861_ = v_reuseFailAlloc_6864_;
goto v_reusejp_6860_;
}
v_reusejp_6860_:
{
lean_object* v___x_6862_; lean_object* v___x_6863_; 
v___x_6862_ = lean_st_ref_put(v___y_6838_, v___x_6861_);
v___x_6863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6863_, 0, v___x_6858_);
return v___x_6863_;
}
}
}
v___jp_6866_:
{
lean_object* v_fileName_6875_; lean_object* v_fileMap_6876_; lean_object* v___x_6877_; lean_object* v___x_6878_; lean_object* v_a_6879_; lean_object* v___x_6881_; uint8_t v_isShared_6882_; uint8_t v_isSharedCheck_6892_; 
v_fileName_6875_ = lean_ctor_get(v___y_6873_, 0);
v_fileMap_6876_ = lean_ctor_get(v___y_6873_, 1);
v___x_6877_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_6823_);
v___x_6878_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5(v___x_6877_, v___y_6826_, v___y_6827_);
v_a_6879_ = lean_ctor_get(v___x_6878_, 0);
v_isSharedCheck_6892_ = !lean_is_exclusive(v___x_6878_);
if (v_isSharedCheck_6892_ == 0)
{
v___x_6881_ = v___x_6878_;
v_isShared_6882_ = v_isSharedCheck_6892_;
goto v_resetjp_6880_;
}
else
{
lean_inc(v_a_6879_);
lean_dec(v___x_6878_);
v___x_6881_ = lean_box(0);
v_isShared_6882_ = v_isSharedCheck_6892_;
goto v_resetjp_6880_;
}
v_resetjp_6880_:
{
lean_object* v___x_6883_; lean_object* v___x_6884_; lean_object* v___x_6885_; lean_object* v___x_6886_; 
lean_inc_ref_n(v_fileMap_6876_, 2);
v___x_6883_ = l_Lean_FileMap_toPosition(v_fileMap_6876_, v___y_6871_);
lean_dec(v___y_6871_);
v___x_6884_ = l_Lean_FileMap_toPosition(v_fileMap_6876_, v___y_6874_);
lean_dec(v___y_6874_);
v___x_6885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6885_, 0, v___x_6884_);
v___x_6886_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___closed__0));
if (v___y_6869_ == 0)
{
lean_del_object(v___x_6881_);
lean_dec_ref(v___y_6867_);
v___y_6830_ = v___x_6885_;
v___y_6831_ = v_fileName_6875_;
v___y_6832_ = v___y_6870_;
v___y_6833_ = v___x_6883_;
v___y_6834_ = v___y_6872_;
v___y_6835_ = v_a_6879_;
v___y_6836_ = v___x_6886_;
v_toCold_6837_ = v___y_6868_;
v___y_6838_ = v___y_6827_;
goto v___jp_6829_;
}
else
{
uint8_t v___x_6887_; 
lean_inc(v_a_6879_);
v___x_6887_ = l_Lean_MessageData_hasTag(v___y_6867_, v_a_6879_);
if (v___x_6887_ == 0)
{
lean_object* v___x_6888_; lean_object* v___x_6890_; 
lean_dec_ref_known(v___x_6885_, 1);
lean_dec_ref(v___x_6883_);
lean_dec(v_a_6879_);
v___x_6888_ = lean_box(0);
if (v_isShared_6882_ == 0)
{
lean_ctor_set(v___x_6881_, 0, v___x_6888_);
v___x_6890_ = v___x_6881_;
goto v_reusejp_6889_;
}
else
{
lean_object* v_reuseFailAlloc_6891_; 
v_reuseFailAlloc_6891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6891_, 0, v___x_6888_);
v___x_6890_ = v_reuseFailAlloc_6891_;
goto v_reusejp_6889_;
}
v_reusejp_6889_:
{
return v___x_6890_;
}
}
else
{
lean_del_object(v___x_6881_);
v___y_6830_ = v___x_6885_;
v___y_6831_ = v_fileName_6875_;
v___y_6832_ = v___y_6870_;
v___y_6833_ = v___x_6883_;
v___y_6834_ = v___y_6872_;
v___y_6835_ = v_a_6879_;
v___y_6836_ = v___x_6886_;
v_toCold_6837_ = v___y_6868_;
v___y_6838_ = v___y_6827_;
goto v___jp_6829_;
}
}
}
}
v___jp_6893_:
{
lean_object* v___x_6901_; 
v___x_6901_ = l_Lean_Syntax_getTailPos_x3f(v___y_6897_, v___y_6899_);
lean_dec(v___y_6897_);
if (lean_obj_tag(v___x_6901_) == 0)
{
lean_inc(v___y_6900_);
v___y_6867_ = v___y_6895_;
v___y_6868_ = v___y_6896_;
v___y_6869_ = v___y_6894_;
v___y_6870_ = v___y_6898_;
v___y_6871_ = v___y_6900_;
v___y_6872_ = v___y_6899_;
v___y_6873_ = v___y_6896_;
v___y_6874_ = v___y_6900_;
goto v___jp_6866_;
}
else
{
lean_object* v_val_6902_; 
v_val_6902_ = lean_ctor_get(v___x_6901_, 0);
lean_inc(v_val_6902_);
lean_dec_ref_known(v___x_6901_, 1);
v___y_6867_ = v___y_6895_;
v___y_6868_ = v___y_6896_;
v___y_6869_ = v___y_6894_;
v___y_6870_ = v___y_6898_;
v___y_6871_ = v___y_6900_;
v___y_6872_ = v___y_6899_;
v___y_6873_ = v___y_6896_;
v___y_6874_ = v_val_6902_;
goto v___jp_6866_;
}
}
v___jp_6903_:
{
lean_object* v_toCold_6906_; lean_object* v_ref_6907_; uint8_t v_suppressElabErrors_6908_; lean_object* v___x_6909_; lean_object* v___f_6910_; lean_object* v_ref_6911_; lean_object* v___x_6912_; 
v_toCold_6906_ = lean_ctor_get(v___y_6826_, 0);
v_ref_6907_ = lean_ctor_get(v___y_6826_, 2);
v_suppressElabErrors_6908_ = lean_ctor_get_uint8(v___y_6826_, sizeof(void*)*3 + 2);
v___x_6909_ = lean_box(v_suppressElabErrors_6908_);
v___f_6910_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___boxed), 2, 1);
lean_closure_set(v___f_6910_, 0, v___x_6909_);
v_ref_6911_ = l_Lean_replaceRef(v_ref_6822_, v_ref_6907_);
v___x_6912_ = l_Lean_Syntax_getPos_x3f(v_ref_6911_, v___y_6904_);
if (lean_obj_tag(v___x_6912_) == 0)
{
lean_object* v___x_6913_; 
v___x_6913_ = lean_unsigned_to_nat(0u);
v___y_6894_ = v_suppressElabErrors_6908_;
v___y_6895_ = v___f_6910_;
v___y_6896_ = v_toCold_6906_;
v___y_6897_ = v_ref_6911_;
v___y_6898_ = v___y_6905_;
v___y_6899_ = v___y_6904_;
v___y_6900_ = v___x_6913_;
goto v___jp_6893_;
}
else
{
lean_object* v_val_6914_; 
v_val_6914_ = lean_ctor_get(v___x_6912_, 0);
lean_inc(v_val_6914_);
lean_dec_ref_known(v___x_6912_, 1);
v___y_6894_ = v_suppressElabErrors_6908_;
v___y_6895_ = v___f_6910_;
v___y_6896_ = v_toCold_6906_;
v___y_6897_ = v_ref_6911_;
v___y_6898_ = v___y_6905_;
v___y_6899_ = v___y_6904_;
v___y_6900_ = v_val_6914_;
goto v___jp_6893_;
}
}
v___jp_6916_:
{
uint8_t v___x_6918_; uint8_t v___x_6919_; 
v___x_6918_ = 1;
v___x_6919_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6824_, v___x_6918_);
if (v___x_6919_ == 0)
{
v___y_6904_ = v___y_6917_;
v___y_6905_ = v_severity_6824_;
goto v___jp_6903_;
}
else
{
lean_object* v___x_6920_; lean_object* v___x_6921_; uint8_t v___x_6922_; 
v___x_6920_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_6826_);
v___x_6921_ = l_Lean_warningAsError;
v___x_6922_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7_spec__9(v___x_6920_, v___x_6921_);
lean_dec_ref(v___x_6920_);
if (v___x_6922_ == 0)
{
v___y_6904_ = v___y_6917_;
v___y_6905_ = v_severity_6824_;
goto v___jp_6903_;
}
else
{
v___y_6904_ = v___y_6917_;
v___y_6905_ = v___x_6915_;
goto v___jp_6903_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_ref_6927_, lean_object* v_msgData_6928_, lean_object* v_severity_6929_, lean_object* v_isSilent_6930_, lean_object* v___y_6931_, lean_object* v___y_6932_, lean_object* v___y_6933_){
_start:
{
uint8_t v_severity_boxed_6934_; uint8_t v_isSilent_boxed_6935_; lean_object* v_res_6936_; 
v_severity_boxed_6934_ = lean_unbox(v_severity_6929_);
v_isSilent_boxed_6935_ = lean_unbox(v_isSilent_6930_);
v_res_6936_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4(v_ref_6927_, v_msgData_6928_, v_severity_boxed_6934_, v_isSilent_boxed_6935_, v___y_6931_, v___y_6932_);
lean_dec(v___y_6932_);
lean_dec_ref(v___y_6931_);
lean_dec(v_ref_6927_);
return v_res_6936_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2(lean_object* v_msgData_6937_, uint8_t v_severity_6938_, uint8_t v_isSilent_6939_, lean_object* v___y_6940_, lean_object* v___y_6941_){
_start:
{
lean_object* v_ref_6943_; lean_object* v___x_6944_; 
v_ref_6943_ = lean_ctor_get(v___y_6940_, 2);
v___x_6944_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4(v_ref_6943_, v_msgData_6937_, v_severity_6938_, v_isSilent_6939_, v___y_6940_, v___y_6941_);
return v___x_6944_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_6945_, lean_object* v_severity_6946_, lean_object* v_isSilent_6947_, lean_object* v___y_6948_, lean_object* v___y_6949_, lean_object* v___y_6950_){
_start:
{
uint8_t v_severity_boxed_6951_; uint8_t v_isSilent_boxed_6952_; lean_object* v_res_6953_; 
v_severity_boxed_6951_ = lean_unbox(v_severity_6946_);
v_isSilent_boxed_6952_ = lean_unbox(v_isSilent_6947_);
v_res_6953_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2(v_msgData_6945_, v_severity_boxed_6951_, v_isSilent_boxed_6952_, v___y_6948_, v___y_6949_);
lean_dec(v___y_6949_);
lean_dec_ref(v___y_6948_);
return v_res_6953_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0(lean_object* v_msgData_6954_, lean_object* v___y_6955_, lean_object* v___y_6956_){
_start:
{
uint8_t v___x_6958_; uint8_t v___x_6959_; lean_object* v___x_6960_; 
v___x_6958_ = 2;
v___x_6959_ = 0;
v___x_6960_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2(v_msgData_6954_, v___x_6958_, v___x_6959_, v___y_6955_, v___y_6956_);
return v___x_6960_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0___boxed(lean_object* v_msgData_6961_, lean_object* v___y_6962_, lean_object* v___y_6963_, lean_object* v___y_6964_){
_start:
{
lean_object* v_res_6965_; 
v_res_6965_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0(v_msgData_6961_, v___y_6962_, v___y_6963_);
lean_dec(v___y_6963_);
lean_dec_ref(v___y_6962_);
return v_res_6965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0(lean_object* v_f_6966_, lean_object* v___y_6967_, lean_object* v___y_6968_){
_start:
{
lean_object* v_module_6970_; lean_object* v_const_6971_; lean_object* v_exception_6972_; lean_object* v___x_6973_; lean_object* v___x_6974_; lean_object* v___x_6975_; lean_object* v___x_6976_; lean_object* v___x_6977_; lean_object* v___x_6978_; lean_object* v___x_6979_; lean_object* v___x_6980_; lean_object* v___x_6981_; lean_object* v___x_6982_; lean_object* v___x_6983_; lean_object* v___x_6984_; 
v_module_6970_ = lean_ctor_get(v_f_6966_, 0);
lean_inc(v_module_6970_);
v_const_6971_ = lean_ctor_get(v_f_6966_, 1);
lean_inc(v_const_6971_);
v_exception_6972_ = lean_ctor_get(v_f_6966_, 2);
lean_inc_ref(v_exception_6972_);
lean_dec_ref(v_f_6966_);
v___x_6973_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1);
v___x_6974_ = l_Lean_MessageData_ofName(v_const_6971_);
v___x_6975_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6975_, 0, v___x_6973_);
lean_ctor_set(v___x_6975_, 1, v___x_6974_);
v___x_6976_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3);
v___x_6977_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6977_, 0, v___x_6975_);
lean_ctor_set(v___x_6977_, 1, v___x_6976_);
v___x_6978_ = l_Lean_MessageData_ofName(v_module_6970_);
v___x_6979_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6979_, 0, v___x_6977_);
lean_ctor_set(v___x_6979_, 1, v___x_6978_);
v___x_6980_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5);
v___x_6981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6981_, 0, v___x_6979_);
lean_ctor_set(v___x_6981_, 1, v___x_6980_);
v___x_6982_ = l_Lean_Exception_toMessageData(v_exception_6972_);
v___x_6983_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6983_, 0, v___x_6981_);
lean_ctor_set(v___x_6983_, 1, v___x_6982_);
v___x_6984_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0(v___x_6983_, v___y_6967_, v___y_6968_);
return v___x_6984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0___boxed(lean_object* v_f_6985_, lean_object* v___y_6986_, lean_object* v___y_6987_, lean_object* v___y_6988_){
_start:
{
lean_object* v_res_6989_; 
v_res_6989_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0(v_f_6985_, v___y_6986_, v___y_6987_);
lean_dec(v___y_6987_);
lean_dec_ref(v___y_6986_);
return v_res_6989_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2(lean_object* v_as_6990_, size_t v_i_6991_, size_t v_stop_6992_, lean_object* v_b_6993_, lean_object* v___y_6994_, lean_object* v___y_6995_){
_start:
{
uint8_t v___x_6997_; 
v___x_6997_ = lean_usize_dec_eq(v_i_6991_, v_stop_6992_);
if (v___x_6997_ == 0)
{
lean_object* v___x_6998_; lean_object* v___x_6999_; 
v___x_6998_ = lean_array_uget_borrowed(v_as_6990_, v_i_6991_);
lean_inc(v___x_6998_);
v___x_6999_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0(v___x_6998_, v___y_6994_, v___y_6995_);
if (lean_obj_tag(v___x_6999_) == 0)
{
lean_object* v_a_7000_; size_t v___x_7001_; size_t v___x_7002_; 
v_a_7000_ = lean_ctor_get(v___x_6999_, 0);
lean_inc(v_a_7000_);
lean_dec_ref_known(v___x_6999_, 1);
v___x_7001_ = ((size_t)1ULL);
v___x_7002_ = lean_usize_add(v_i_6991_, v___x_7001_);
v_i_6991_ = v___x_7002_;
v_b_6993_ = v_a_7000_;
goto _start;
}
else
{
return v___x_6999_;
}
}
else
{
lean_object* v___x_7004_; 
v___x_7004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7004_, 0, v_b_6993_);
return v___x_7004_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2___boxed(lean_object* v_as_7005_, lean_object* v_i_7006_, lean_object* v_stop_7007_, lean_object* v_b_7008_, lean_object* v___y_7009_, lean_object* v___y_7010_, lean_object* v___y_7011_){
_start:
{
size_t v_i_boxed_7012_; size_t v_stop_boxed_7013_; lean_object* v_res_7014_; 
v_i_boxed_7012_ = lean_unbox_usize(v_i_7006_);
lean_dec(v_i_7006_);
v_stop_boxed_7013_ = lean_unbox_usize(v_stop_7007_);
lean_dec(v_stop_7007_);
v_res_7014_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2(v_as_7005_, v_i_boxed_7012_, v_stop_boxed_7013_, v_b_7008_, v___y_7009_, v___y_7010_);
lean_dec(v___y_7010_);
lean_dec_ref(v___y_7009_);
lean_dec_ref(v_as_7005_);
return v_res_7014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(lean_object* v_entriesForConst_7015_, lean_object* v_a_7016_, lean_object* v_a_7017_){
_start:
{
lean_object* v___x_7019_; lean_object* v_env_7020_; lean_object* v___x_7021_; lean_object* v_a_7022_; lean_object* v___x_7024_; uint8_t v_isShared_7025_; uint8_t v_isSharedCheck_7049_; 
v___x_7019_ = lean_st_ref_get(v_a_7017_);
v_env_7020_ = lean_ctor_get(v___x_7019_, 0);
lean_inc_ref(v_env_7020_);
lean_dec(v___x_7019_);
v___x_7021_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(v_a_7017_);
v_a_7022_ = lean_ctor_get(v___x_7021_, 0);
v_isSharedCheck_7049_ = !lean_is_exclusive(v___x_7021_);
if (v_isSharedCheck_7049_ == 0)
{
v___x_7024_ = v___x_7021_;
v_isShared_7025_ = v_isSharedCheck_7049_;
goto v_resetjp_7023_;
}
else
{
lean_inc(v_a_7022_);
lean_dec(v___x_7021_);
v___x_7024_ = lean_box(0);
v_isShared_7025_ = v_isSharedCheck_7049_;
goto v_resetjp_7023_;
}
v_resetjp_7023_:
{
lean_object* v___x_7026_; lean_object* v___x_7027_; lean_object* v___x_7033_; lean_object* v___x_7034_; lean_object* v___x_7035_; uint8_t v___x_7036_; 
v___x_7026_ = l_Lean_Meta_LazyDiscrTree_ImportData_new();
lean_inc_ref(v_a_7016_);
v___x_7027_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(v_a_7016_, v_a_7022_, v_env_7020_, v___x_7026_, v_entriesForConst_7015_);
v___x_7033_ = lean_st_ref_get(v___x_7026_);
lean_dec(v___x_7026_);
v___x_7034_ = lean_unsigned_to_nat(0u);
v___x_7035_ = lean_array_get_size(v___x_7033_);
v___x_7036_ = lean_nat_dec_lt(v___x_7034_, v___x_7035_);
if (v___x_7036_ == 0)
{
lean_dec(v___x_7033_);
goto v___jp_7028_;
}
else
{
lean_object* v___x_7037_; size_t v___x_7038_; size_t v___x_7039_; lean_object* v___x_7040_; 
v___x_7037_ = lean_box(0);
v___x_7038_ = ((size_t)0ULL);
v___x_7039_ = lean_usize_of_nat(v___x_7035_);
v___x_7040_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2(v___x_7033_, v___x_7038_, v___x_7039_, v___x_7037_, v_a_7016_, v_a_7017_);
lean_dec(v___x_7033_);
if (lean_obj_tag(v___x_7040_) == 0)
{
lean_dec_ref_known(v___x_7040_, 1);
goto v___jp_7028_;
}
else
{
lean_object* v_a_7041_; lean_object* v___x_7043_; uint8_t v_isShared_7044_; uint8_t v_isSharedCheck_7048_; 
lean_dec_ref(v___x_7027_);
lean_del_object(v___x_7024_);
v_a_7041_ = lean_ctor_get(v___x_7040_, 0);
v_isSharedCheck_7048_ = !lean_is_exclusive(v___x_7040_);
if (v_isSharedCheck_7048_ == 0)
{
v___x_7043_ = v___x_7040_;
v_isShared_7044_ = v_isSharedCheck_7048_;
goto v_resetjp_7042_;
}
else
{
lean_inc(v_a_7041_);
lean_dec(v___x_7040_);
v___x_7043_ = lean_box(0);
v_isShared_7044_ = v_isSharedCheck_7048_;
goto v_resetjp_7042_;
}
v_resetjp_7042_:
{
lean_object* v___x_7046_; 
if (v_isShared_7044_ == 0)
{
v___x_7046_ = v___x_7043_;
goto v_reusejp_7045_;
}
else
{
lean_object* v_reuseFailAlloc_7047_; 
v_reuseFailAlloc_7047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7047_, 0, v_a_7041_);
v___x_7046_ = v_reuseFailAlloc_7047_;
goto v_reusejp_7045_;
}
v_reusejp_7045_:
{
return v___x_7046_;
}
}
}
}
v___jp_7028_:
{
lean_object* v___x_7029_; lean_object* v___x_7031_; 
v___x_7029_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v___x_7027_);
if (v_isShared_7025_ == 0)
{
lean_ctor_set(v___x_7024_, 0, v___x_7029_);
v___x_7031_ = v___x_7024_;
goto v_reusejp_7030_;
}
else
{
lean_object* v_reuseFailAlloc_7032_; 
v_reuseFailAlloc_7032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7032_, 0, v___x_7029_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg___boxed(lean_object* v_entriesForConst_7050_, lean_object* v_a_7051_, lean_object* v_a_7052_, lean_object* v_a_7053_){
_start:
{
lean_object* v_res_7054_; 
v_res_7054_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(v_entriesForConst_7050_, v_a_7051_, v_a_7052_);
lean_dec(v_a_7052_);
lean_dec_ref(v_a_7051_);
return v_res_7054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree(lean_object* v_00_u03b1_7055_, lean_object* v_entriesForConst_7056_, lean_object* v_a_7057_, lean_object* v_a_7058_){
_start:
{
lean_object* v___x_7060_; 
v___x_7060_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(v_entriesForConst_7056_, v_a_7057_, v_a_7058_);
return v___x_7060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___boxed(lean_object* v_00_u03b1_7061_, lean_object* v_entriesForConst_7062_, lean_object* v_a_7063_, lean_object* v_a_7064_, lean_object* v_a_7065_){
_start:
{
lean_object* v_res_7066_; 
v_res_7066_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree(v_00_u03b1_7061_, v_entriesForConst_7062_, v_a_7063_, v_a_7064_);
lean_dec(v_a_7064_);
lean_dec_ref(v_a_7063_);
return v_res_7066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0(lean_object* v_entriesForConst_7067_, lean_object* v_droppedEntriesRef_7068_, lean_object* v_droppedKeys_7069_, lean_object* v___y_7070_, lean_object* v___y_7071_, lean_object* v___y_7072_, lean_object* v___y_7073_){
_start:
{
lean_object* v_t_7076_; lean_object* v___x_7079_; 
v___x_7079_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(v_entriesForConst_7067_, v___y_7072_, v___y_7073_);
if (lean_obj_tag(v___x_7079_) == 0)
{
if (lean_obj_tag(v_droppedEntriesRef_7068_) == 1)
{
lean_object* v_a_7080_; lean_object* v_val_7081_; lean_object* v___x_7083_; uint8_t v_isShared_7084_; uint8_t v_isSharedCheck_7107_; 
v_a_7080_ = lean_ctor_get(v___x_7079_, 0);
lean_inc(v_a_7080_);
lean_dec_ref_known(v___x_7079_, 1);
v_val_7081_ = lean_ctor_get(v_droppedEntriesRef_7068_, 0);
v_isSharedCheck_7107_ = !lean_is_exclusive(v_droppedEntriesRef_7068_);
if (v_isSharedCheck_7107_ == 0)
{
v___x_7083_ = v_droppedEntriesRef_7068_;
v_isShared_7084_ = v_isSharedCheck_7107_;
goto v_resetjp_7082_;
}
else
{
lean_inc(v_val_7081_);
lean_dec(v_droppedEntriesRef_7068_);
v___x_7083_ = lean_box(0);
v_isShared_7084_ = v_isSharedCheck_7107_;
goto v_resetjp_7082_;
}
v_resetjp_7082_:
{
lean_object* v___x_7085_; 
v___x_7085_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_a_7080_, v_droppedKeys_7069_, v___y_7070_, v___y_7071_, v___y_7072_, v___y_7073_);
lean_dec(v_droppedKeys_7069_);
if (lean_obj_tag(v___x_7085_) == 0)
{
lean_object* v_a_7086_; lean_object* v_fst_7087_; lean_object* v_snd_7088_; lean_object* v___x_7089_; lean_object* v___y_7091_; 
v_a_7086_ = lean_ctor_get(v___x_7085_, 0);
lean_inc(v_a_7086_);
lean_dec_ref_known(v___x_7085_, 1);
v_fst_7087_ = lean_ctor_get(v_a_7086_, 0);
lean_inc(v_fst_7087_);
v_snd_7088_ = lean_ctor_get(v_a_7086_, 1);
lean_inc(v_snd_7088_);
lean_dec(v_a_7086_);
v___x_7089_ = lean_st_ref_get(v_val_7081_);
if (lean_obj_tag(v___x_7089_) == 0)
{
lean_object* v___x_7097_; 
v___x_7097_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___y_7091_ = v___x_7097_;
goto v___jp_7090_;
}
else
{
lean_object* v_val_7098_; 
v_val_7098_ = lean_ctor_get(v___x_7089_, 0);
lean_inc(v_val_7098_);
lean_dec_ref_known(v___x_7089_, 1);
v___y_7091_ = v_val_7098_;
goto v___jp_7090_;
}
v___jp_7090_:
{
lean_object* v___x_7092_; lean_object* v___x_7094_; 
v___x_7092_ = l_Array_append___redArg(v___y_7091_, v_fst_7087_);
lean_dec(v_fst_7087_);
if (v_isShared_7084_ == 0)
{
lean_ctor_set(v___x_7083_, 0, v___x_7092_);
v___x_7094_ = v___x_7083_;
goto v_reusejp_7093_;
}
else
{
lean_object* v_reuseFailAlloc_7096_; 
v_reuseFailAlloc_7096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7096_, 0, v___x_7092_);
v___x_7094_ = v_reuseFailAlloc_7096_;
goto v_reusejp_7093_;
}
v_reusejp_7093_:
{
lean_object* v___x_7095_; 
v___x_7095_ = lean_st_ref_swap(v_val_7081_, v___x_7094_);
lean_dec(v_val_7081_);
lean_dec(v___x_7095_);
v_t_7076_ = v_snd_7088_;
goto v___jp_7075_;
}
}
}
else
{
lean_object* v_a_7099_; lean_object* v___x_7101_; uint8_t v_isShared_7102_; uint8_t v_isSharedCheck_7106_; 
lean_del_object(v___x_7083_);
lean_dec(v_val_7081_);
v_a_7099_ = lean_ctor_get(v___x_7085_, 0);
v_isSharedCheck_7106_ = !lean_is_exclusive(v___x_7085_);
if (v_isSharedCheck_7106_ == 0)
{
v___x_7101_ = v___x_7085_;
v_isShared_7102_ = v_isSharedCheck_7106_;
goto v_resetjp_7100_;
}
else
{
lean_inc(v_a_7099_);
lean_dec(v___x_7085_);
v___x_7101_ = lean_box(0);
v_isShared_7102_ = v_isSharedCheck_7106_;
goto v_resetjp_7100_;
}
v_resetjp_7100_:
{
lean_object* v___x_7104_; 
if (v_isShared_7102_ == 0)
{
v___x_7104_ = v___x_7101_;
goto v_reusejp_7103_;
}
else
{
lean_object* v_reuseFailAlloc_7105_; 
v_reuseFailAlloc_7105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7105_, 0, v_a_7099_);
v___x_7104_ = v_reuseFailAlloc_7105_;
goto v_reusejp_7103_;
}
v_reusejp_7103_:
{
return v___x_7104_;
}
}
}
}
}
else
{
lean_object* v_a_7108_; lean_object* v___x_7109_; 
lean_dec(v_droppedEntriesRef_7068_);
v_a_7108_ = lean_ctor_get(v___x_7079_, 0);
lean_inc(v_a_7108_);
lean_dec_ref_known(v___x_7079_, 1);
v___x_7109_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_a_7108_, v_droppedKeys_7069_, v___y_7070_, v___y_7071_, v___y_7072_, v___y_7073_);
if (lean_obj_tag(v___x_7109_) == 0)
{
lean_object* v_a_7110_; 
v_a_7110_ = lean_ctor_get(v___x_7109_, 0);
lean_inc(v_a_7110_);
lean_dec_ref_known(v___x_7109_, 1);
v_t_7076_ = v_a_7110_;
goto v___jp_7075_;
}
else
{
lean_object* v_a_7111_; lean_object* v___x_7113_; uint8_t v_isShared_7114_; uint8_t v_isSharedCheck_7118_; 
v_a_7111_ = lean_ctor_get(v___x_7109_, 0);
v_isSharedCheck_7118_ = !lean_is_exclusive(v___x_7109_);
if (v_isSharedCheck_7118_ == 0)
{
v___x_7113_ = v___x_7109_;
v_isShared_7114_ = v_isSharedCheck_7118_;
goto v_resetjp_7112_;
}
else
{
lean_inc(v_a_7111_);
lean_dec(v___x_7109_);
v___x_7113_ = lean_box(0);
v_isShared_7114_ = v_isSharedCheck_7118_;
goto v_resetjp_7112_;
}
v_resetjp_7112_:
{
lean_object* v___x_7116_; 
if (v_isShared_7114_ == 0)
{
v___x_7116_ = v___x_7113_;
goto v_reusejp_7115_;
}
else
{
lean_object* v_reuseFailAlloc_7117_; 
v_reuseFailAlloc_7117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7117_, 0, v_a_7111_);
v___x_7116_ = v_reuseFailAlloc_7117_;
goto v_reusejp_7115_;
}
v_reusejp_7115_:
{
return v___x_7116_;
}
}
}
}
}
else
{
lean_object* v_a_7119_; lean_object* v___x_7121_; uint8_t v_isShared_7122_; uint8_t v_isSharedCheck_7126_; 
lean_dec(v_droppedKeys_7069_);
lean_dec(v_droppedEntriesRef_7068_);
v_a_7119_ = lean_ctor_get(v___x_7079_, 0);
v_isSharedCheck_7126_ = !lean_is_exclusive(v___x_7079_);
if (v_isSharedCheck_7126_ == 0)
{
v___x_7121_ = v___x_7079_;
v_isShared_7122_ = v_isSharedCheck_7126_;
goto v_resetjp_7120_;
}
else
{
lean_inc(v_a_7119_);
lean_dec(v___x_7079_);
v___x_7121_ = lean_box(0);
v_isShared_7122_ = v_isSharedCheck_7126_;
goto v_resetjp_7120_;
}
v_resetjp_7120_:
{
lean_object* v___x_7124_; 
if (v_isShared_7122_ == 0)
{
v___x_7124_ = v___x_7121_;
goto v_reusejp_7123_;
}
else
{
lean_object* v_reuseFailAlloc_7125_; 
v_reuseFailAlloc_7125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7125_, 0, v_a_7119_);
v___x_7124_ = v_reuseFailAlloc_7125_;
goto v_reusejp_7123_;
}
v_reusejp_7123_:
{
return v___x_7124_;
}
}
}
v___jp_7075_:
{
lean_object* v___x_7077_; lean_object* v___x_7078_; 
v___x_7077_ = lean_st_mk_ref(v_t_7076_);
v___x_7078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7078_, 0, v___x_7077_);
return v___x_7078_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0___boxed(lean_object* v_entriesForConst_7127_, lean_object* v_droppedEntriesRef_7128_, lean_object* v_droppedKeys_7129_, lean_object* v___y_7130_, lean_object* v___y_7131_, lean_object* v___y_7132_, lean_object* v___y_7133_, lean_object* v___y_7134_){
_start:
{
lean_object* v_res_7135_; 
v_res_7135_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0(v_entriesForConst_7127_, v_droppedEntriesRef_7128_, v_droppedKeys_7129_, v___y_7130_, v___y_7131_, v___y_7132_, v___y_7133_);
lean_dec(v___y_7133_);
lean_dec_ref(v___y_7132_);
lean_dec(v___y_7131_);
lean_dec_ref(v___y_7130_);
return v_res_7135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(lean_object* v_entriesForConst_7137_, lean_object* v_droppedKeys_7138_, lean_object* v_droppedEntriesRef_7139_, lean_object* v_a_7140_, lean_object* v_a_7141_, lean_object* v_a_7142_, lean_object* v_a_7143_){
_start:
{
lean_object* v___f_7145_; lean_object* v___x_7146_; lean_object* v___x_7147_; lean_object* v___x_7148_; lean_object* v___x_7149_; 
v___f_7145_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_7145_, 0, v_entriesForConst_7137_);
lean_closure_set(v___f_7145_, 1, v_droppedEntriesRef_7139_);
lean_closure_set(v___f_7145_, 2, v_droppedKeys_7138_);
v___x_7146_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_7142_);
v___x_7147_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___closed__0));
v___x_7148_ = lean_box(0);
v___x_7149_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v___x_7147_, v___x_7146_, v___f_7145_, v___x_7148_, v_a_7140_, v_a_7141_, v_a_7142_, v_a_7143_);
lean_dec_ref(v___x_7146_);
return v___x_7149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___boxed(lean_object* v_entriesForConst_7150_, lean_object* v_droppedKeys_7151_, lean_object* v_droppedEntriesRef_7152_, lean_object* v_a_7153_, lean_object* v_a_7154_, lean_object* v_a_7155_, lean_object* v_a_7156_, lean_object* v_a_7157_){
_start:
{
lean_object* v_res_7158_; 
v_res_7158_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v_entriesForConst_7150_, v_droppedKeys_7151_, v_droppedEntriesRef_7152_, v_a_7153_, v_a_7154_, v_a_7155_, v_a_7156_);
lean_dec(v_a_7156_);
lean_dec_ref(v_a_7155_);
lean_dec(v_a_7154_);
lean_dec_ref(v_a_7153_);
return v_res_7158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef(lean_object* v_00_u03b1_7159_, lean_object* v_entriesForConst_7160_, lean_object* v_droppedKeys_7161_, lean_object* v_droppedEntriesRef_7162_, lean_object* v_a_7163_, lean_object* v_a_7164_, lean_object* v_a_7165_, lean_object* v_a_7166_){
_start:
{
lean_object* v___x_7168_; 
v___x_7168_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v_entriesForConst_7160_, v_droppedKeys_7161_, v_droppedEntriesRef_7162_, v_a_7163_, v_a_7164_, v_a_7165_, v_a_7166_);
return v___x_7168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___boxed(lean_object* v_00_u03b1_7169_, lean_object* v_entriesForConst_7170_, lean_object* v_droppedKeys_7171_, lean_object* v_droppedEntriesRef_7172_, lean_object* v_a_7173_, lean_object* v_a_7174_, lean_object* v_a_7175_, lean_object* v_a_7176_, lean_object* v_a_7177_){
_start:
{
lean_object* v_res_7178_; 
v_res_7178_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef(v_00_u03b1_7169_, v_entriesForConst_7170_, v_droppedKeys_7171_, v_droppedEntriesRef_7172_, v_a_7173_, v_a_7174_, v_a_7175_, v_a_7176_);
lean_dec(v_a_7176_);
lean_dec_ref(v_a_7175_);
lean_dec(v_a_7174_);
lean_dec_ref(v_a_7173_);
return v_res_7178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0(lean_object* v_moduleRef_7179_, lean_object* v_ty_7180_, lean_object* v___y_7181_, lean_object* v___y_7182_, lean_object* v___y_7183_, lean_object* v___y_7184_){
_start:
{
lean_object* v___x_7186_; lean_object* v___x_7187_; 
v___x_7186_ = lean_st_ref_get(v_moduleRef_7179_);
v___x_7187_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v___x_7186_, v_ty_7180_, v___y_7181_, v___y_7182_, v___y_7183_, v___y_7184_);
if (lean_obj_tag(v___x_7187_) == 0)
{
lean_object* v_a_7188_; lean_object* v___x_7190_; uint8_t v_isShared_7191_; uint8_t v_isSharedCheck_7198_; 
v_a_7188_ = lean_ctor_get(v___x_7187_, 0);
v_isSharedCheck_7198_ = !lean_is_exclusive(v___x_7187_);
if (v_isSharedCheck_7198_ == 0)
{
v___x_7190_ = v___x_7187_;
v_isShared_7191_ = v_isSharedCheck_7198_;
goto v_resetjp_7189_;
}
else
{
lean_inc(v_a_7188_);
lean_dec(v___x_7187_);
v___x_7190_ = lean_box(0);
v_isShared_7191_ = v_isSharedCheck_7198_;
goto v_resetjp_7189_;
}
v_resetjp_7189_:
{
lean_object* v_fst_7192_; lean_object* v_snd_7193_; lean_object* v___x_7194_; lean_object* v___x_7196_; 
v_fst_7192_ = lean_ctor_get(v_a_7188_, 0);
lean_inc(v_fst_7192_);
v_snd_7193_ = lean_ctor_get(v_a_7188_, 1);
lean_inc(v_snd_7193_);
lean_dec(v_a_7188_);
v___x_7194_ = lean_st_ref_swap(v_moduleRef_7179_, v_snd_7193_);
lean_dec(v___x_7194_);
if (v_isShared_7191_ == 0)
{
lean_ctor_set(v___x_7190_, 0, v_fst_7192_);
v___x_7196_ = v___x_7190_;
goto v_reusejp_7195_;
}
else
{
lean_object* v_reuseFailAlloc_7197_; 
v_reuseFailAlloc_7197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7197_, 0, v_fst_7192_);
v___x_7196_ = v_reuseFailAlloc_7197_;
goto v_reusejp_7195_;
}
v_reusejp_7195_:
{
return v___x_7196_;
}
}
}
else
{
lean_object* v_a_7199_; lean_object* v___x_7201_; uint8_t v_isShared_7202_; uint8_t v_isSharedCheck_7206_; 
v_a_7199_ = lean_ctor_get(v___x_7187_, 0);
v_isSharedCheck_7206_ = !lean_is_exclusive(v___x_7187_);
if (v_isSharedCheck_7206_ == 0)
{
v___x_7201_ = v___x_7187_;
v_isShared_7202_ = v_isSharedCheck_7206_;
goto v_resetjp_7200_;
}
else
{
lean_inc(v_a_7199_);
lean_dec(v___x_7187_);
v___x_7201_ = lean_box(0);
v_isShared_7202_ = v_isSharedCheck_7206_;
goto v_resetjp_7200_;
}
v_resetjp_7200_:
{
lean_object* v___x_7204_; 
if (v_isShared_7202_ == 0)
{
v___x_7204_ = v___x_7201_;
goto v_reusejp_7203_;
}
else
{
lean_object* v_reuseFailAlloc_7205_; 
v_reuseFailAlloc_7205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7205_, 0, v_a_7199_);
v___x_7204_ = v_reuseFailAlloc_7205_;
goto v_reusejp_7203_;
}
v_reusejp_7203_:
{
return v___x_7204_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0___boxed(lean_object* v_moduleRef_7207_, lean_object* v_ty_7208_, lean_object* v___y_7209_, lean_object* v___y_7210_, lean_object* v___y_7211_, lean_object* v___y_7212_, lean_object* v___y_7213_){
_start:
{
lean_object* v_res_7214_; 
v_res_7214_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0(v_moduleRef_7207_, v_ty_7208_, v___y_7209_, v___y_7210_, v___y_7211_, v___y_7212_);
lean_dec(v___y_7212_);
lean_dec_ref(v___y_7211_);
lean_dec(v___y_7210_);
lean_dec_ref(v___y_7209_);
lean_dec(v_moduleRef_7207_);
return v_res_7214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(lean_object* v_moduleRef_7216_, lean_object* v_ty_7217_, lean_object* v_a_7218_, lean_object* v_a_7219_, lean_object* v_a_7220_, lean_object* v_a_7221_){
_start:
{
lean_object* v___f_7223_; lean_object* v___x_7224_; lean_object* v___x_7225_; lean_object* v___x_7226_; lean_object* v___x_7227_; 
v___f_7223_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_7223_, 0, v_moduleRef_7216_);
lean_closure_set(v___f_7223_, 1, v_ty_7217_);
v___x_7224_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_7220_);
v___x_7225_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___closed__0));
v___x_7226_ = lean_box(0);
v___x_7227_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v___x_7225_, v___x_7224_, v___f_7223_, v___x_7226_, v_a_7218_, v_a_7219_, v_a_7220_, v_a_7221_);
lean_dec_ref(v___x_7224_);
return v___x_7227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___boxed(lean_object* v_moduleRef_7228_, lean_object* v_ty_7229_, lean_object* v_a_7230_, lean_object* v_a_7231_, lean_object* v_a_7232_, lean_object* v_a_7233_, lean_object* v_a_7234_){
_start:
{
lean_object* v_res_7235_; 
v_res_7235_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(v_moduleRef_7228_, v_ty_7229_, v_a_7230_, v_a_7231_, v_a_7232_, v_a_7233_);
lean_dec(v_a_7233_);
lean_dec_ref(v_a_7232_);
lean_dec(v_a_7231_);
lean_dec_ref(v_a_7230_);
return v_res_7235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches(lean_object* v_00_u03b1_7236_, lean_object* v_moduleRef_7237_, lean_object* v_ty_7238_, lean_object* v_a_7239_, lean_object* v_a_7240_, lean_object* v_a_7241_, lean_object* v_a_7242_){
_start:
{
lean_object* v___x_7244_; 
v___x_7244_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(v_moduleRef_7237_, v_ty_7238_, v_a_7239_, v_a_7240_, v_a_7241_, v_a_7242_);
return v___x_7244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___boxed(lean_object* v_00_u03b1_7245_, lean_object* v_moduleRef_7246_, lean_object* v_ty_7247_, lean_object* v_a_7248_, lean_object* v_a_7249_, lean_object* v_a_7250_, lean_object* v_a_7251_, lean_object* v_a_7252_){
_start:
{
lean_object* v_res_7253_; 
v_res_7253_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches(v_00_u03b1_7245_, v_moduleRef_7246_, v_ty_7247_, v_a_7248_, v_a_7249_, v_a_7250_, v_a_7251_);
lean_dec(v_a_7251_);
lean_dec_ref(v_a_7250_);
lean_dec(v_a_7249_);
lean_dec_ref(v_a_7248_);
return v_res_7253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(lean_object* v_adjustResult_7254_, lean_object* v_j_7255_, size_t v_sz_7256_, size_t v_i_7257_, lean_object* v_bs_7258_){
_start:
{
uint8_t v___x_7259_; 
v___x_7259_ = lean_usize_dec_lt(v_i_7257_, v_sz_7256_);
if (v___x_7259_ == 0)
{
lean_dec(v_j_7255_);
lean_dec(v_adjustResult_7254_);
return v_bs_7258_;
}
else
{
lean_object* v_v_7260_; lean_object* v___x_7261_; lean_object* v_bs_x27_7262_; lean_object* v___x_7263_; size_t v___x_7264_; size_t v___x_7265_; lean_object* v___x_7266_; 
v_v_7260_ = lean_array_uget(v_bs_7258_, v_i_7257_);
v___x_7261_ = lean_unsigned_to_nat(0u);
v_bs_x27_7262_ = lean_array_uset(v_bs_7258_, v_i_7257_, v___x_7261_);
lean_inc(v_adjustResult_7254_);
lean_inc(v_j_7255_);
v___x_7263_ = lean_apply_2(v_adjustResult_7254_, v_j_7255_, v_v_7260_);
v___x_7264_ = ((size_t)1ULL);
v___x_7265_ = lean_usize_add(v_i_7257_, v___x_7264_);
v___x_7266_ = lean_array_uset(v_bs_x27_7262_, v_i_7257_, v___x_7263_);
v_i_7257_ = v___x_7265_;
v_bs_7258_ = v___x_7266_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg___boxed(lean_object* v_adjustResult_7268_, lean_object* v_j_7269_, lean_object* v_sz_7270_, lean_object* v_i_7271_, lean_object* v_bs_7272_){
_start:
{
size_t v_sz_boxed_7273_; size_t v_i_boxed_7274_; lean_object* v_res_7275_; 
v_sz_boxed_7273_ = lean_unbox_usize(v_sz_7270_);
lean_dec(v_sz_7270_);
v_i_boxed_7274_ = lean_unbox_usize(v_i_7271_);
lean_dec(v_i_7271_);
v_res_7275_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(v_adjustResult_7268_, v_j_7269_, v_sz_boxed_7273_, v_i_boxed_7274_, v_bs_7272_);
return v_res_7275_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(lean_object* v_adjustResult_7276_, lean_object* v_j_7277_, lean_object* v_as_7278_, size_t v_i_7279_, size_t v_stop_7280_, lean_object* v_b_7281_){
_start:
{
uint8_t v___x_7282_; 
v___x_7282_ = lean_usize_dec_eq(v_i_7279_, v_stop_7280_);
if (v___x_7282_ == 0)
{
lean_object* v___x_7283_; size_t v_sz_7284_; size_t v___x_7285_; lean_object* v___x_7286_; lean_object* v___x_7287_; size_t v___x_7288_; size_t v___x_7289_; 
v___x_7283_ = lean_array_uget_borrowed(v_as_7278_, v_i_7279_);
v_sz_7284_ = lean_array_size(v___x_7283_);
v___x_7285_ = ((size_t)0ULL);
lean_inc(v___x_7283_);
lean_inc(v_j_7277_);
lean_inc(v_adjustResult_7276_);
v___x_7286_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(v_adjustResult_7276_, v_j_7277_, v_sz_7284_, v___x_7285_, v___x_7283_);
v___x_7287_ = l_Array_append___redArg(v_b_7281_, v___x_7286_);
lean_dec_ref(v___x_7286_);
v___x_7288_ = ((size_t)1ULL);
v___x_7289_ = lean_usize_add(v_i_7279_, v___x_7288_);
v_i_7279_ = v___x_7289_;
v_b_7281_ = v___x_7287_;
goto _start;
}
else
{
lean_dec(v_j_7277_);
lean_dec(v_adjustResult_7276_);
return v_b_7281_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg___boxed(lean_object* v_adjustResult_7291_, lean_object* v_j_7292_, lean_object* v_as_7293_, lean_object* v_i_7294_, lean_object* v_stop_7295_, lean_object* v_b_7296_){
_start:
{
size_t v_i_boxed_7297_; size_t v_stop_boxed_7298_; lean_object* v_res_7299_; 
v_i_boxed_7297_ = lean_unbox_usize(v_i_7294_);
lean_dec(v_i_7294_);
v_stop_boxed_7298_ = lean_unbox_usize(v_stop_7295_);
lean_dec(v_stop_7295_);
v_res_7299_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7291_, v_j_7292_, v_as_7293_, v_i_boxed_7297_, v_stop_boxed_7298_, v_b_7296_);
lean_dec_ref(v_as_7293_);
return v_res_7299_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(lean_object* v_n_7300_, lean_object* v_aa_7301_, lean_object* v_adjustResult_7302_, lean_object* v_n_7303_, lean_object* v_j_7304_, lean_object* v_a_7305_){
_start:
{
lean_object* v_zero_7306_; uint8_t v_isZero_7307_; 
v_zero_7306_ = lean_unsigned_to_nat(0u);
v_isZero_7307_ = lean_nat_dec_eq(v_j_7304_, v_zero_7306_);
if (v_isZero_7307_ == 1)
{
lean_dec(v_j_7304_);
lean_dec(v_adjustResult_7302_);
return v_a_7305_;
}
else
{
lean_object* v_one_7308_; lean_object* v_n_7309_; lean_object* v___x_7310_; lean_object* v___x_7311_; lean_object* v_j_7312_; lean_object* v_b_7313_; lean_object* v___x_7314_; uint8_t v___x_7315_; 
v_one_7308_ = lean_unsigned_to_nat(1u);
v_n_7309_ = lean_nat_sub(v_j_7304_, v_one_7308_);
v___x_7310_ = lean_nat_sub(v_n_7303_, v_j_7304_);
lean_dec(v_j_7304_);
v___x_7311_ = lean_nat_sub(v_n_7300_, v_one_7308_);
v_j_7312_ = lean_nat_sub(v___x_7311_, v___x_7310_);
lean_dec(v___x_7310_);
lean_dec(v___x_7311_);
v_b_7313_ = lean_array_fget_borrowed(v_aa_7301_, v_j_7312_);
v___x_7314_ = lean_array_get_size(v_b_7313_);
v___x_7315_ = lean_nat_dec_lt(v_zero_7306_, v___x_7314_);
if (v___x_7315_ == 0)
{
lean_dec(v_j_7312_);
v_j_7304_ = v_n_7309_;
goto _start;
}
else
{
size_t v___x_7317_; size_t v___x_7318_; lean_object* v___x_7319_; 
v___x_7317_ = ((size_t)0ULL);
v___x_7318_ = lean_usize_of_nat(v___x_7314_);
lean_inc(v_adjustResult_7302_);
v___x_7319_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7302_, v_j_7312_, v_b_7313_, v___x_7317_, v___x_7318_, v_a_7305_);
v_j_7304_ = v_n_7309_;
v_a_7305_ = v___x_7319_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_n_7321_, lean_object* v_aa_7322_, lean_object* v_adjustResult_7323_, lean_object* v_n_7324_, lean_object* v_j_7325_, lean_object* v_a_7326_){
_start:
{
lean_object* v_res_7327_; 
v_res_7327_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7321_, v_aa_7322_, v_adjustResult_7323_, v_n_7324_, v_j_7325_, v_a_7326_);
lean_dec(v_n_7324_);
lean_dec_ref(v_aa_7322_);
lean_dec(v_n_7321_);
return v_res_7327_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(lean_object* v_n_7328_, lean_object* v_adjustResult_7329_, lean_object* v_aa_7330_, lean_object* v_n_7331_, lean_object* v_j_7332_, lean_object* v_a_7333_){
_start:
{
lean_object* v_zero_7334_; uint8_t v_isZero_7335_; 
v_zero_7334_ = lean_unsigned_to_nat(0u);
v_isZero_7335_ = lean_nat_dec_eq(v_j_7332_, v_zero_7334_);
if (v_isZero_7335_ == 1)
{
lean_dec(v_adjustResult_7329_);
return v_a_7333_;
}
else
{
lean_object* v_one_7336_; lean_object* v_n_7337_; lean_object* v___x_7338_; lean_object* v___x_7339_; lean_object* v_j_7340_; lean_object* v_b_7341_; lean_object* v___x_7342_; uint8_t v___x_7343_; 
v_one_7336_ = lean_unsigned_to_nat(1u);
v_n_7337_ = lean_nat_sub(v_j_7332_, v_one_7336_);
v___x_7338_ = lean_nat_sub(v_n_7331_, v_j_7332_);
v___x_7339_ = lean_nat_sub(v_n_7328_, v_one_7336_);
v_j_7340_ = lean_nat_sub(v___x_7339_, v___x_7338_);
lean_dec(v___x_7338_);
lean_dec(v___x_7339_);
v_b_7341_ = lean_array_fget_borrowed(v_aa_7330_, v_j_7340_);
v___x_7342_ = lean_array_get_size(v_b_7341_);
v___x_7343_ = lean_nat_dec_lt(v_zero_7334_, v___x_7342_);
if (v___x_7343_ == 0)
{
lean_object* v___x_7344_; 
lean_dec(v_j_7340_);
v___x_7344_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7328_, v_aa_7330_, v_adjustResult_7329_, v_n_7331_, v_n_7337_, v_a_7333_);
return v___x_7344_;
}
else
{
size_t v___x_7345_; size_t v___x_7346_; lean_object* v___x_7347_; lean_object* v___x_7348_; 
v___x_7345_ = ((size_t)0ULL);
v___x_7346_ = lean_usize_of_nat(v___x_7342_);
lean_inc(v_adjustResult_7329_);
v___x_7347_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7329_, v_j_7340_, v_b_7341_, v___x_7345_, v___x_7346_, v_a_7333_);
v___x_7348_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7328_, v_aa_7330_, v_adjustResult_7329_, v_n_7331_, v_n_7337_, v___x_7347_);
return v___x_7348_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg___boxed(lean_object* v_n_7349_, lean_object* v_adjustResult_7350_, lean_object* v_aa_7351_, lean_object* v_n_7352_, lean_object* v_j_7353_, lean_object* v_a_7354_){
_start:
{
lean_object* v_res_7355_; 
v_res_7355_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(v_n_7349_, v_adjustResult_7350_, v_aa_7351_, v_n_7352_, v_j_7353_, v_a_7354_);
lean_dec(v_j_7353_);
lean_dec(v_n_7352_);
lean_dec_ref(v_aa_7351_);
lean_dec(v_n_7349_);
return v_res_7355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(lean_object* v_adjustResult_7356_, lean_object* v_mr_7357_, lean_object* v_a_7358_){
_start:
{
lean_object* v_n_7359_; lean_object* v___x_7360_; 
v_n_7359_ = lean_array_get_size(v_mr_7357_);
v___x_7360_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(v_n_7359_, v_adjustResult_7356_, v_mr_7357_, v_n_7359_, v_n_7359_, v_a_7358_);
return v___x_7360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg___boxed(lean_object* v_adjustResult_7361_, lean_object* v_mr_7362_, lean_object* v_a_7363_){
_start:
{
lean_object* v_res_7364_; 
v_res_7364_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7361_, v_mr_7362_, v_a_7363_);
lean_dec_ref(v_mr_7362_);
return v_res_7364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(lean_object* v_moduleTreeRef_7365_, lean_object* v_ref_7366_, lean_object* v_addEntry_7367_, lean_object* v_droppedKeys_7368_, lean_object* v_constantsPerTask_7369_, lean_object* v_droppedEntriesRef_7370_, lean_object* v_adjustResult_7371_, lean_object* v_ty_7372_, lean_object* v_a_7373_, lean_object* v_a_7374_, lean_object* v_a_7375_, lean_object* v_a_7376_){
_start:
{
lean_object* v___x_7378_; 
lean_inc_ref(v_ty_7372_);
v___x_7378_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(v_moduleTreeRef_7365_, v_ty_7372_, v_a_7373_, v_a_7374_, v_a_7375_, v_a_7376_);
if (lean_obj_tag(v___x_7378_) == 0)
{
lean_object* v_a_7379_; lean_object* v___x_7380_; 
v_a_7379_ = lean_ctor_get(v___x_7378_, 0);
lean_inc(v_a_7379_);
lean_dec_ref_known(v___x_7378_, 1);
v___x_7380_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(v_ref_7366_, v_addEntry_7367_, v_droppedKeys_7368_, v_constantsPerTask_7369_, v_droppedEntriesRef_7370_, v_ty_7372_, v_a_7373_, v_a_7374_, v_a_7375_, v_a_7376_);
if (lean_obj_tag(v___x_7380_) == 0)
{
lean_object* v_a_7381_; lean_object* v___x_7383_; uint8_t v_isShared_7384_; uint8_t v_isSharedCheck_7394_; 
v_a_7381_ = lean_ctor_get(v___x_7380_, 0);
v_isSharedCheck_7394_ = !lean_is_exclusive(v___x_7380_);
if (v_isSharedCheck_7394_ == 0)
{
v___x_7383_ = v___x_7380_;
v_isShared_7384_ = v_isSharedCheck_7394_;
goto v_resetjp_7382_;
}
else
{
lean_inc(v_a_7381_);
lean_dec(v___x_7380_);
v___x_7383_ = lean_box(0);
v_isShared_7384_ = v_isSharedCheck_7394_;
goto v_resetjp_7382_;
}
v_resetjp_7382_:
{
lean_object* v___x_7385_; lean_object* v___x_7386_; lean_object* v___x_7387_; lean_object* v___x_7388_; lean_object* v___x_7389_; lean_object* v___x_7390_; lean_object* v___x_7392_; 
v___x_7385_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_a_7379_);
v___x_7386_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_a_7381_);
v___x_7387_ = lean_nat_add(v___x_7385_, v___x_7386_);
lean_dec(v___x_7386_);
lean_dec(v___x_7385_);
v___x_7388_ = lean_mk_empty_array_with_capacity(v___x_7387_);
lean_dec(v___x_7387_);
lean_inc(v_adjustResult_7371_);
v___x_7389_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7371_, v_a_7379_, v___x_7388_);
lean_dec(v_a_7379_);
v___x_7390_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7371_, v_a_7381_, v___x_7389_);
lean_dec(v_a_7381_);
if (v_isShared_7384_ == 0)
{
lean_ctor_set(v___x_7383_, 0, v___x_7390_);
v___x_7392_ = v___x_7383_;
goto v_reusejp_7391_;
}
else
{
lean_object* v_reuseFailAlloc_7393_; 
v_reuseFailAlloc_7393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7393_, 0, v___x_7390_);
v___x_7392_ = v_reuseFailAlloc_7393_;
goto v_reusejp_7391_;
}
v_reusejp_7391_:
{
return v___x_7392_;
}
}
}
else
{
lean_object* v_a_7395_; lean_object* v___x_7397_; uint8_t v_isShared_7398_; uint8_t v_isSharedCheck_7402_; 
lean_dec(v_a_7379_);
lean_dec(v_adjustResult_7371_);
v_a_7395_ = lean_ctor_get(v___x_7380_, 0);
v_isSharedCheck_7402_ = !lean_is_exclusive(v___x_7380_);
if (v_isSharedCheck_7402_ == 0)
{
v___x_7397_ = v___x_7380_;
v_isShared_7398_ = v_isSharedCheck_7402_;
goto v_resetjp_7396_;
}
else
{
lean_inc(v_a_7395_);
lean_dec(v___x_7380_);
v___x_7397_ = lean_box(0);
v_isShared_7398_ = v_isSharedCheck_7402_;
goto v_resetjp_7396_;
}
v_resetjp_7396_:
{
lean_object* v___x_7400_; 
if (v_isShared_7398_ == 0)
{
v___x_7400_ = v___x_7397_;
goto v_reusejp_7399_;
}
else
{
lean_object* v_reuseFailAlloc_7401_; 
v_reuseFailAlloc_7401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7401_, 0, v_a_7395_);
v___x_7400_ = v_reuseFailAlloc_7401_;
goto v_reusejp_7399_;
}
v_reusejp_7399_:
{
return v___x_7400_;
}
}
}
}
else
{
lean_object* v_a_7403_; lean_object* v___x_7405_; uint8_t v_isShared_7406_; uint8_t v_isSharedCheck_7410_; 
lean_dec_ref(v_ty_7372_);
lean_dec(v_adjustResult_7371_);
lean_dec(v_droppedEntriesRef_7370_);
lean_dec(v_constantsPerTask_7369_);
lean_dec(v_droppedKeys_7368_);
lean_dec_ref(v_addEntry_7367_);
v_a_7403_ = lean_ctor_get(v___x_7378_, 0);
v_isSharedCheck_7410_ = !lean_is_exclusive(v___x_7378_);
if (v_isSharedCheck_7410_ == 0)
{
v___x_7405_ = v___x_7378_;
v_isShared_7406_ = v_isSharedCheck_7410_;
goto v_resetjp_7404_;
}
else
{
lean_inc(v_a_7403_);
lean_dec(v___x_7378_);
v___x_7405_ = lean_box(0);
v_isShared_7406_ = v_isSharedCheck_7410_;
goto v_resetjp_7404_;
}
v_resetjp_7404_:
{
lean_object* v___x_7408_; 
if (v_isShared_7406_ == 0)
{
v___x_7408_ = v___x_7405_;
goto v_reusejp_7407_;
}
else
{
lean_object* v_reuseFailAlloc_7409_; 
v_reuseFailAlloc_7409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7409_, 0, v_a_7403_);
v___x_7408_ = v_reuseFailAlloc_7409_;
goto v_reusejp_7407_;
}
v_reusejp_7407_:
{
return v___x_7408_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg___boxed(lean_object* v_moduleTreeRef_7411_, lean_object* v_ref_7412_, lean_object* v_addEntry_7413_, lean_object* v_droppedKeys_7414_, lean_object* v_constantsPerTask_7415_, lean_object* v_droppedEntriesRef_7416_, lean_object* v_adjustResult_7417_, lean_object* v_ty_7418_, lean_object* v_a_7419_, lean_object* v_a_7420_, lean_object* v_a_7421_, lean_object* v_a_7422_, lean_object* v_a_7423_){
_start:
{
lean_object* v_res_7424_; 
v_res_7424_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_moduleTreeRef_7411_, v_ref_7412_, v_addEntry_7413_, v_droppedKeys_7414_, v_constantsPerTask_7415_, v_droppedEntriesRef_7416_, v_adjustResult_7417_, v_ty_7418_, v_a_7419_, v_a_7420_, v_a_7421_, v_a_7422_);
lean_dec(v_a_7422_);
lean_dec_ref(v_a_7421_);
lean_dec(v_a_7420_);
lean_dec_ref(v_a_7419_);
lean_dec(v_ref_7412_);
return v_res_7424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt(lean_object* v_00_u03b1_7425_, lean_object* v_00_u03b2_7426_, lean_object* v_moduleTreeRef_7427_, lean_object* v_ref_7428_, lean_object* v_addEntry_7429_, lean_object* v_droppedKeys_7430_, lean_object* v_constantsPerTask_7431_, lean_object* v_droppedEntriesRef_7432_, lean_object* v_adjustResult_7433_, lean_object* v_ty_7434_, lean_object* v_a_7435_, lean_object* v_a_7436_, lean_object* v_a_7437_, lean_object* v_a_7438_){
_start:
{
lean_object* v___x_7440_; 
v___x_7440_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_moduleTreeRef_7427_, v_ref_7428_, v_addEntry_7429_, v_droppedKeys_7430_, v_constantsPerTask_7431_, v_droppedEntriesRef_7432_, v_adjustResult_7433_, v_ty_7434_, v_a_7435_, v_a_7436_, v_a_7437_, v_a_7438_);
return v___x_7440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___boxed(lean_object* v_00_u03b1_7441_, lean_object* v_00_u03b2_7442_, lean_object* v_moduleTreeRef_7443_, lean_object* v_ref_7444_, lean_object* v_addEntry_7445_, lean_object* v_droppedKeys_7446_, lean_object* v_constantsPerTask_7447_, lean_object* v_droppedEntriesRef_7448_, lean_object* v_adjustResult_7449_, lean_object* v_ty_7450_, lean_object* v_a_7451_, lean_object* v_a_7452_, lean_object* v_a_7453_, lean_object* v_a_7454_, lean_object* v_a_7455_){
_start:
{
lean_object* v_res_7456_; 
v_res_7456_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt(v_00_u03b1_7441_, v_00_u03b2_7442_, v_moduleTreeRef_7443_, v_ref_7444_, v_addEntry_7445_, v_droppedKeys_7446_, v_constantsPerTask_7447_, v_droppedEntriesRef_7448_, v_adjustResult_7449_, v_ty_7450_, v_a_7451_, v_a_7452_, v_a_7453_, v_a_7454_);
lean_dec(v_a_7454_);
lean_dec_ref(v_a_7453_);
lean_dec(v_a_7452_);
lean_dec_ref(v_a_7451_);
lean_dec(v_ref_7444_);
return v_res_7456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0(lean_object* v_00_u03b1_7457_, lean_object* v_00_u03b2_7458_, lean_object* v_adjustResult_7459_, lean_object* v_mr_7460_, lean_object* v_a_7461_){
_start:
{
lean_object* v___x_7462_; 
v___x_7462_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7459_, v_mr_7460_, v_a_7461_);
return v___x_7462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___boxed(lean_object* v_00_u03b1_7463_, lean_object* v_00_u03b2_7464_, lean_object* v_adjustResult_7465_, lean_object* v_mr_7466_, lean_object* v_a_7467_){
_start:
{
lean_object* v_res_7468_; 
v_res_7468_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0(v_00_u03b1_7463_, v_00_u03b2_7464_, v_adjustResult_7465_, v_mr_7466_, v_a_7467_);
lean_dec_ref(v_mr_7466_);
return v_res_7468_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0(lean_object* v_00_u03b1_7469_, lean_object* v_00_u03b2_7470_, lean_object* v_adjustResult_7471_, lean_object* v_j_7472_, size_t v_sz_7473_, size_t v_i_7474_, lean_object* v_bs_7475_){
_start:
{
lean_object* v___x_7476_; 
v___x_7476_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(v_adjustResult_7471_, v_j_7472_, v_sz_7473_, v_i_7474_, v_bs_7475_);
return v___x_7476_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___boxed(lean_object* v_00_u03b1_7477_, lean_object* v_00_u03b2_7478_, lean_object* v_adjustResult_7479_, lean_object* v_j_7480_, lean_object* v_sz_7481_, lean_object* v_i_7482_, lean_object* v_bs_7483_){
_start:
{
size_t v_sz_boxed_7484_; size_t v_i_boxed_7485_; lean_object* v_res_7486_; 
v_sz_boxed_7484_ = lean_unbox_usize(v_sz_7481_);
lean_dec(v_sz_7481_);
v_i_boxed_7485_ = lean_unbox_usize(v_i_7482_);
lean_dec(v_i_7482_);
v_res_7486_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0(v_00_u03b1_7477_, v_00_u03b2_7478_, v_adjustResult_7479_, v_j_7480_, v_sz_boxed_7484_, v_i_boxed_7485_, v_bs_7483_);
return v_res_7486_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1(lean_object* v_00_u03b1_7487_, lean_object* v_00_u03b2_7488_, lean_object* v_adjustResult_7489_, lean_object* v_j_7490_, lean_object* v_as_7491_, size_t v_i_7492_, size_t v_stop_7493_, lean_object* v_b_7494_){
_start:
{
lean_object* v___x_7495_; 
v___x_7495_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7489_, v_j_7490_, v_as_7491_, v_i_7492_, v_stop_7493_, v_b_7494_);
return v___x_7495_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___boxed(lean_object* v_00_u03b1_7496_, lean_object* v_00_u03b2_7497_, lean_object* v_adjustResult_7498_, lean_object* v_j_7499_, lean_object* v_as_7500_, lean_object* v_i_7501_, lean_object* v_stop_7502_, lean_object* v_b_7503_){
_start:
{
size_t v_i_boxed_7504_; size_t v_stop_boxed_7505_; lean_object* v_res_7506_; 
v_i_boxed_7504_ = lean_unbox_usize(v_i_7501_);
lean_dec(v_i_7501_);
v_stop_boxed_7505_ = lean_unbox_usize(v_stop_7502_);
lean_dec(v_stop_7502_);
v_res_7506_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1(v_00_u03b1_7496_, v_00_u03b2_7497_, v_adjustResult_7498_, v_j_7499_, v_as_7500_, v_i_boxed_7504_, v_stop_boxed_7505_, v_b_7503_);
lean_dec_ref(v_as_7500_);
return v_res_7506_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2(lean_object* v_00_u03b2_7507_, lean_object* v_n_7508_, lean_object* v_00_u03b1_7509_, lean_object* v_adjustResult_7510_, lean_object* v_aa_7511_, lean_object* v_n_7512_, lean_object* v_j_7513_, lean_object* v_a_7514_, lean_object* v_a_7515_){
_start:
{
lean_object* v___x_7516_; 
v___x_7516_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(v_n_7508_, v_adjustResult_7510_, v_aa_7511_, v_n_7512_, v_j_7513_, v_a_7515_);
return v___x_7516_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___boxed(lean_object* v_00_u03b2_7517_, lean_object* v_n_7518_, lean_object* v_00_u03b1_7519_, lean_object* v_adjustResult_7520_, lean_object* v_aa_7521_, lean_object* v_n_7522_, lean_object* v_j_7523_, lean_object* v_a_7524_, lean_object* v_a_7525_){
_start:
{
lean_object* v_res_7526_; 
v_res_7526_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2(v_00_u03b2_7517_, v_n_7518_, v_00_u03b1_7519_, v_adjustResult_7520_, v_aa_7521_, v_n_7522_, v_j_7523_, v_a_7524_, v_a_7525_);
lean_dec(v_j_7523_);
lean_dec(v_n_7522_);
lean_dec_ref(v_aa_7521_);
lean_dec(v_n_7518_);
return v_res_7526_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_7527_, lean_object* v_n_7528_, lean_object* v_00_u03b1_7529_, lean_object* v_aa_7530_, lean_object* v_adjustResult_7531_, lean_object* v_n_7532_, lean_object* v_j_7533_, lean_object* v_a_7534_, lean_object* v_a_7535_){
_start:
{
lean_object* v___x_7536_; 
v___x_7536_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7528_, v_aa_7530_, v_adjustResult_7531_, v_n_7532_, v_j_7533_, v_a_7535_);
return v___x_7536_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b2_7537_, lean_object* v_n_7538_, lean_object* v_00_u03b1_7539_, lean_object* v_aa_7540_, lean_object* v_adjustResult_7541_, lean_object* v_n_7542_, lean_object* v_j_7543_, lean_object* v_a_7544_, lean_object* v_a_7545_){
_start:
{
lean_object* v_res_7546_; 
v_res_7546_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3(v_00_u03b2_7537_, v_n_7538_, v_00_u03b1_7539_, v_aa_7540_, v_adjustResult_7541_, v_n_7542_, v_j_7543_, v_a_7544_, v_a_7545_);
lean_dec(v_n_7542_);
lean_dec_ref(v_aa_7540_);
lean_dec(v_n_7538_);
return v_res_7546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg___lam__0(lean_object* v_x_7547_, lean_object* v_v_7548_){
_start:
{
lean_inc(v_v_7548_);
return v_v_7548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg___lam__0___boxed(lean_object* v_x_7549_, lean_object* v_v_7550_){
_start:
{
lean_object* v_res_7551_; 
v_res_7551_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg___lam__0(v_x_7549_, v_v_7550_);
lean_dec(v_v_7550_);
lean_dec(v_x_7549_);
return v_res_7551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg(lean_object* v_ref_7553_, lean_object* v_addEntry_7554_, lean_object* v_droppedKeys_7555_, lean_object* v_constantsPerTask_7556_, lean_object* v_droppedEntriesRef_7557_, lean_object* v_ty_7558_, lean_object* v_a_7559_, lean_object* v_a_7560_, lean_object* v_a_7561_, lean_object* v_a_7562_){
_start:
{
lean_object* v___f_7564_; lean_object* v___x_7565_; 
v___f_7564_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_findMatches___redArg___closed__0));
lean_inc(v_droppedEntriesRef_7557_);
lean_inc(v_droppedKeys_7555_);
lean_inc_ref(v_addEntry_7554_);
v___x_7565_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v_addEntry_7554_, v_droppedKeys_7555_, v_droppedEntriesRef_7557_, v_a_7559_, v_a_7560_, v_a_7561_, v_a_7562_);
if (lean_obj_tag(v___x_7565_) == 0)
{
lean_object* v_a_7566_; lean_object* v___x_7567_; 
v_a_7566_ = lean_ctor_get(v___x_7565_, 0);
lean_inc(v_a_7566_);
lean_dec_ref_known(v___x_7565_, 1);
v___x_7567_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_a_7566_, v_ref_7553_, v_addEntry_7554_, v_droppedKeys_7555_, v_constantsPerTask_7556_, v_droppedEntriesRef_7557_, v___f_7564_, v_ty_7558_, v_a_7559_, v_a_7560_, v_a_7561_, v_a_7562_);
return v___x_7567_;
}
else
{
lean_object* v_a_7568_; lean_object* v___x_7570_; uint8_t v_isShared_7571_; uint8_t v_isSharedCheck_7575_; 
lean_dec_ref(v_ty_7558_);
lean_dec(v_droppedEntriesRef_7557_);
lean_dec(v_constantsPerTask_7556_);
lean_dec(v_droppedKeys_7555_);
lean_dec_ref(v_addEntry_7554_);
v_a_7568_ = lean_ctor_get(v___x_7565_, 0);
v_isSharedCheck_7575_ = !lean_is_exclusive(v___x_7565_);
if (v_isSharedCheck_7575_ == 0)
{
v___x_7570_ = v___x_7565_;
v_isShared_7571_ = v_isSharedCheck_7575_;
goto v_resetjp_7569_;
}
else
{
lean_inc(v_a_7568_);
lean_dec(v___x_7565_);
v___x_7570_ = lean_box(0);
v_isShared_7571_ = v_isSharedCheck_7575_;
goto v_resetjp_7569_;
}
v_resetjp_7569_:
{
lean_object* v___x_7573_; 
if (v_isShared_7571_ == 0)
{
v___x_7573_ = v___x_7570_;
goto v_reusejp_7572_;
}
else
{
lean_object* v_reuseFailAlloc_7574_; 
v_reuseFailAlloc_7574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7574_, 0, v_a_7568_);
v___x_7573_ = v_reuseFailAlloc_7574_;
goto v_reusejp_7572_;
}
v_reusejp_7572_:
{
return v___x_7573_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg___boxed(lean_object* v_ref_7576_, lean_object* v_addEntry_7577_, lean_object* v_droppedKeys_7578_, lean_object* v_constantsPerTask_7579_, lean_object* v_droppedEntriesRef_7580_, lean_object* v_ty_7581_, lean_object* v_a_7582_, lean_object* v_a_7583_, lean_object* v_a_7584_, lean_object* v_a_7585_, lean_object* v_a_7586_){
_start:
{
lean_object* v_res_7587_; 
v_res_7587_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg(v_ref_7576_, v_addEntry_7577_, v_droppedKeys_7578_, v_constantsPerTask_7579_, v_droppedEntriesRef_7580_, v_ty_7581_, v_a_7582_, v_a_7583_, v_a_7584_, v_a_7585_);
lean_dec(v_a_7585_);
lean_dec_ref(v_a_7584_);
lean_dec(v_a_7583_);
lean_dec_ref(v_a_7582_);
lean_dec(v_ref_7576_);
return v_res_7587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches(lean_object* v_00_u03b1_7588_, lean_object* v_ref_7589_, lean_object* v_addEntry_7590_, lean_object* v_droppedKeys_7591_, lean_object* v_constantsPerTask_7592_, lean_object* v_droppedEntriesRef_7593_, lean_object* v_ty_7594_, lean_object* v_a_7595_, lean_object* v_a_7596_, lean_object* v_a_7597_, lean_object* v_a_7598_){
_start:
{
lean_object* v___x_7600_; 
v___x_7600_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg(v_ref_7589_, v_addEntry_7590_, v_droppedKeys_7591_, v_constantsPerTask_7592_, v_droppedEntriesRef_7593_, v_ty_7594_, v_a_7595_, v_a_7596_, v_a_7597_, v_a_7598_);
return v___x_7600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___boxed(lean_object* v_00_u03b1_7601_, lean_object* v_ref_7602_, lean_object* v_addEntry_7603_, lean_object* v_droppedKeys_7604_, lean_object* v_constantsPerTask_7605_, lean_object* v_droppedEntriesRef_7606_, lean_object* v_ty_7607_, lean_object* v_a_7608_, lean_object* v_a_7609_, lean_object* v_a_7610_, lean_object* v_a_7611_, lean_object* v_a_7612_){
_start:
{
lean_object* v_res_7613_; 
v_res_7613_ = l_Lean_Meta_LazyDiscrTree_findMatches(v_00_u03b1_7601_, v_ref_7602_, v_addEntry_7603_, v_droppedKeys_7604_, v_constantsPerTask_7605_, v_droppedEntriesRef_7606_, v_ty_7607_, v_a_7608_, v_a_7609_, v_a_7610_, v_a_7611_);
lean_dec(v_a_7611_);
lean_dec_ref(v_a_7610_);
lean_dec(v_a_7609_);
lean_dec_ref(v_a_7608_);
lean_dec(v_ref_7602_);
return v_res_7613_;
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
