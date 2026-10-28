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
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
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
lean_object* v___y_764_; lean_object* v___y_774_; uint8_t v___y_775_; uint8_t v___y_776_; lean_object* v___y_777_; uint16_t v___y_778_; lean_object* v___y_779_; uint8_t v___y_780_; lean_object* v_toCold_785_; lean_object* v_currRecDepth_786_; lean_object* v_ref_787_; uint16_t v_optionFlags_788_; uint8_t v_suppressElabErrors_789_; uint8_t v_checkDeprecated_790_; uint8_t v_isRecordingDeps_791_; lean_object* v_maxRecDepth_792_; lean_object* v_cancelTk_x3f_793_; 
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
v___x_782_ = lean_nat_add(v___y_777_, v___x_781_);
lean_inc_ref(v___y_774_);
v___x_783_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_783_, 0, v___y_774_);
lean_ctor_set(v___x_783_, 1, v___x_782_);
lean_ctor_set(v___x_783_, 2, v___y_779_);
lean_ctor_set_uint16(v___x_783_, sizeof(void*)*3, v___y_778_);
lean_ctor_set_uint8(v___x_783_, sizeof(void*)*3 + 2, v___y_780_);
lean_ctor_set_uint8(v___x_783_, sizeof(void*)*3 + 3, v___y_775_);
lean_ctor_set_uint8(v___x_783_, sizeof(void*)*3 + 4, v___y_776_);
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
v___y_775_ = v_checkDeprecated_790_;
v___y_776_ = v_isRecordingDeps_791_;
v___y_777_ = v_currRecDepth_786_;
v___y_778_ = v_optionFlags_788_;
v___y_779_ = v_ref_787_;
v___y_780_ = v_suppressElabErrors_789_;
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
v___y_775_ = v_checkDeprecated_790_;
v___y_776_ = v_isRecordingDeps_791_;
v___y_777_ = v_currRecDepth_786_;
v___y_778_ = v_optionFlags_788_;
v___y_779_ = v_ref_787_;
v___y_780_ = v_suppressElabErrors_789_;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_a_816_, lean_object* v_x_817_){
_start:
{
if (lean_obj_tag(v_x_817_) == 0)
{
lean_object* v___x_818_; 
v___x_818_ = lean_box(0);
return v___x_818_;
}
else
{
lean_object* v_key_819_; lean_object* v_value_820_; lean_object* v_tail_821_; uint8_t v___x_822_; 
v_key_819_ = lean_ctor_get(v_x_817_, 0);
v_value_820_ = lean_ctor_get(v_x_817_, 1);
v_tail_821_ = lean_ctor_get(v_x_817_, 2);
v___x_822_ = l_Lean_ExprStructEq_beq(v_key_819_, v_a_816_);
if (v___x_822_ == 0)
{
v_x_817_ = v_tail_821_;
goto _start;
}
else
{
lean_object* v___x_824_; 
lean_inc(v_value_820_);
v___x_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_824_, 0, v_value_820_);
return v___x_824_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_a_825_, lean_object* v_x_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg(v_a_825_, v_x_826_);
lean_dec(v_x_826_);
lean_dec_ref(v_a_825_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg(lean_object* v_m_828_, lean_object* v_a_829_){
_start:
{
lean_object* v_buckets_830_; lean_object* v___x_831_; uint64_t v___x_832_; uint64_t v___x_833_; uint64_t v___x_834_; uint64_t v_fold_835_; uint64_t v___x_836_; uint64_t v___x_837_; uint64_t v___x_838_; size_t v___x_839_; size_t v___x_840_; size_t v___x_841_; size_t v___x_842_; size_t v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v_buckets_830_ = lean_ctor_get(v_m_828_, 1);
v___x_831_ = lean_array_get_size(v_buckets_830_);
v___x_832_ = l_Lean_ExprStructEq_hash(v_a_829_);
v___x_833_ = 32ULL;
v___x_834_ = lean_uint64_shift_right(v___x_832_, v___x_833_);
v_fold_835_ = lean_uint64_xor(v___x_832_, v___x_834_);
v___x_836_ = 16ULL;
v___x_837_ = lean_uint64_shift_right(v_fold_835_, v___x_836_);
v___x_838_ = lean_uint64_xor(v_fold_835_, v___x_837_);
v___x_839_ = lean_uint64_to_usize(v___x_838_);
v___x_840_ = lean_usize_of_nat(v___x_831_);
v___x_841_ = ((size_t)1ULL);
v___x_842_ = lean_usize_sub(v___x_840_, v___x_841_);
v___x_843_ = lean_usize_land(v___x_839_, v___x_842_);
v___x_844_ = lean_array_uget_borrowed(v_buckets_830_, v___x_843_);
v___x_845_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg(v_a_829_, v___x_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_m_846_, lean_object* v_a_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg(v_m_846_, v_a_847_);
lean_dec_ref(v_a_847_);
lean_dec_ref(v_m_846_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12___redArg(lean_object* v_a_849_, lean_object* v_b_850_, lean_object* v_x_851_){
_start:
{
if (lean_obj_tag(v_x_851_) == 0)
{
lean_dec(v_b_850_);
lean_dec_ref(v_a_849_);
return v_x_851_;
}
else
{
lean_object* v_key_852_; lean_object* v_value_853_; lean_object* v_tail_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_866_; 
v_key_852_ = lean_ctor_get(v_x_851_, 0);
v_value_853_ = lean_ctor_get(v_x_851_, 1);
v_tail_854_ = lean_ctor_get(v_x_851_, 2);
v_isSharedCheck_866_ = !lean_is_exclusive(v_x_851_);
if (v_isSharedCheck_866_ == 0)
{
v___x_856_ = v_x_851_;
v_isShared_857_ = v_isSharedCheck_866_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_tail_854_);
lean_inc(v_value_853_);
lean_inc(v_key_852_);
lean_dec(v_x_851_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_866_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
uint8_t v___x_858_; 
v___x_858_ = l_Lean_ExprStructEq_beq(v_key_852_, v_a_849_);
if (v___x_858_ == 0)
{
lean_object* v___x_859_; lean_object* v___x_861_; 
v___x_859_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12___redArg(v_a_849_, v_b_850_, v_tail_854_);
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 2, v___x_859_);
v___x_861_ = v___x_856_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_key_852_);
lean_ctor_set(v_reuseFailAlloc_862_, 1, v_value_853_);
lean_ctor_set(v_reuseFailAlloc_862_, 2, v___x_859_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
else
{
lean_object* v___x_864_; 
lean_dec(v_value_853_);
lean_dec(v_key_852_);
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 1, v_b_850_);
lean_ctor_set(v___x_856_, 0, v_a_849_);
v___x_864_ = v___x_856_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_a_849_);
lean_ctor_set(v_reuseFailAlloc_865_, 1, v_b_850_);
lean_ctor_set(v_reuseFailAlloc_865_, 2, v_tail_854_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(lean_object* v_x_867_, lean_object* v_x_868_){
_start:
{
if (lean_obj_tag(v_x_868_) == 0)
{
return v_x_867_;
}
else
{
lean_object* v_key_869_; lean_object* v_value_870_; lean_object* v_tail_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_894_; 
v_key_869_ = lean_ctor_get(v_x_868_, 0);
v_value_870_ = lean_ctor_get(v_x_868_, 1);
v_tail_871_ = lean_ctor_get(v_x_868_, 2);
v_isSharedCheck_894_ = !lean_is_exclusive(v_x_868_);
if (v_isSharedCheck_894_ == 0)
{
v___x_873_ = v_x_868_;
v_isShared_874_ = v_isSharedCheck_894_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_tail_871_);
lean_inc(v_value_870_);
lean_inc(v_key_869_);
lean_dec(v_x_868_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_894_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_875_; uint64_t v___x_876_; uint64_t v___x_877_; uint64_t v___x_878_; uint64_t v_fold_879_; uint64_t v___x_880_; uint64_t v___x_881_; uint64_t v___x_882_; size_t v___x_883_; size_t v___x_884_; size_t v___x_885_; size_t v___x_886_; size_t v___x_887_; lean_object* v___x_888_; lean_object* v___x_890_; 
v___x_875_ = lean_array_get_size(v_x_867_);
v___x_876_ = l_Lean_ExprStructEq_hash(v_key_869_);
v___x_877_ = 32ULL;
v___x_878_ = lean_uint64_shift_right(v___x_876_, v___x_877_);
v_fold_879_ = lean_uint64_xor(v___x_876_, v___x_878_);
v___x_880_ = 16ULL;
v___x_881_ = lean_uint64_shift_right(v_fold_879_, v___x_880_);
v___x_882_ = lean_uint64_xor(v_fold_879_, v___x_881_);
v___x_883_ = lean_uint64_to_usize(v___x_882_);
v___x_884_ = lean_usize_of_nat(v___x_875_);
v___x_885_ = ((size_t)1ULL);
v___x_886_ = lean_usize_sub(v___x_884_, v___x_885_);
v___x_887_ = lean_usize_land(v___x_883_, v___x_886_);
v___x_888_ = lean_array_uget_borrowed(v_x_867_, v___x_887_);
lean_inc(v___x_888_);
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 2, v___x_888_);
v___x_890_ = v___x_873_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_key_869_);
lean_ctor_set(v_reuseFailAlloc_893_, 1, v_value_870_);
lean_ctor_set(v_reuseFailAlloc_893_, 2, v___x_888_);
v___x_890_ = v_reuseFailAlloc_893_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
lean_object* v___x_891_; 
v___x_891_ = lean_array_uset(v_x_867_, v___x_887_, v___x_890_);
v_x_867_ = v___x_891_;
v_x_868_ = v_tail_871_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(lean_object* v_i_895_, lean_object* v_source_896_, lean_object* v_target_897_){
_start:
{
lean_object* v___x_898_; uint8_t v___x_899_; 
v___x_898_ = lean_array_get_size(v_source_896_);
v___x_899_ = lean_nat_dec_lt(v_i_895_, v___x_898_);
if (v___x_899_ == 0)
{
lean_dec_ref(v_source_896_);
lean_dec(v_i_895_);
return v_target_897_;
}
else
{
lean_object* v_es_900_; lean_object* v___x_901_; lean_object* v_source_902_; lean_object* v_target_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v_es_900_ = lean_array_fget(v_source_896_, v_i_895_);
v___x_901_ = lean_box(0);
v_source_902_ = lean_array_fset(v_source_896_, v_i_895_, v___x_901_);
v_target_903_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_target_897_, v_es_900_);
v___x_904_ = lean_unsigned_to_nat(1u);
v___x_905_ = lean_nat_add(v_i_895_, v___x_904_);
lean_dec(v_i_895_);
v_i_895_ = v___x_905_;
v_source_896_ = v_source_902_;
v_target_897_ = v_target_903_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11___redArg(lean_object* v_data_907_){
_start:
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v_nbuckets_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_908_ = lean_array_get_size(v_data_907_);
v___x_909_ = lean_unsigned_to_nat(2u);
v_nbuckets_910_ = lean_nat_mul(v___x_908_, v___x_909_);
v___x_911_ = lean_unsigned_to_nat(0u);
v___x_912_ = lean_box(0);
v___x_913_ = lean_mk_array(v_nbuckets_910_, v___x_912_);
v___x_914_ = lean_array_propagate_mark(v_data_907_, v___x_913_);
v___x_915_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v___x_911_, v_data_907_, v___x_914_);
return v___x_915_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(lean_object* v_a_916_, lean_object* v_x_917_){
_start:
{
if (lean_obj_tag(v_x_917_) == 0)
{
uint8_t v___x_918_; 
v___x_918_ = 0;
return v___x_918_;
}
else
{
lean_object* v_key_919_; lean_object* v_tail_920_; uint8_t v___x_921_; 
v_key_919_ = lean_ctor_get(v_x_917_, 0);
v_tail_920_ = lean_ctor_get(v_x_917_, 2);
v___x_921_ = l_Lean_ExprStructEq_beq(v_key_919_, v_a_916_);
if (v___x_921_ == 0)
{
v_x_917_ = v_tail_920_;
goto _start;
}
else
{
return v___x_921_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg___boxed(lean_object* v_a_923_, lean_object* v_x_924_){
_start:
{
uint8_t v_res_925_; lean_object* v_r_926_; 
v_res_925_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(v_a_923_, v_x_924_);
lean_dec(v_x_924_);
lean_dec_ref(v_a_923_);
v_r_926_ = lean_box(v_res_925_);
return v_r_926_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6___redArg(lean_object* v_m_927_, lean_object* v_a_928_, lean_object* v_b_929_){
_start:
{
lean_object* v_size_930_; lean_object* v_buckets_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_974_; 
v_size_930_ = lean_ctor_get(v_m_927_, 0);
v_buckets_931_ = lean_ctor_get(v_m_927_, 1);
v_isSharedCheck_974_ = !lean_is_exclusive(v_m_927_);
if (v_isSharedCheck_974_ == 0)
{
v___x_933_ = v_m_927_;
v_isShared_934_ = v_isSharedCheck_974_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_buckets_931_);
lean_inc(v_size_930_);
lean_dec(v_m_927_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_974_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_935_; uint64_t v___x_936_; uint64_t v___x_937_; uint64_t v___x_938_; uint64_t v_fold_939_; uint64_t v___x_940_; uint64_t v___x_941_; uint64_t v___x_942_; size_t v___x_943_; size_t v___x_944_; size_t v___x_945_; size_t v___x_946_; size_t v___x_947_; lean_object* v_bkt_948_; uint8_t v___x_949_; 
v___x_935_ = lean_array_get_size(v_buckets_931_);
v___x_936_ = l_Lean_ExprStructEq_hash(v_a_928_);
v___x_937_ = 32ULL;
v___x_938_ = lean_uint64_shift_right(v___x_936_, v___x_937_);
v_fold_939_ = lean_uint64_xor(v___x_936_, v___x_938_);
v___x_940_ = 16ULL;
v___x_941_ = lean_uint64_shift_right(v_fold_939_, v___x_940_);
v___x_942_ = lean_uint64_xor(v_fold_939_, v___x_941_);
v___x_943_ = lean_uint64_to_usize(v___x_942_);
v___x_944_ = lean_usize_of_nat(v___x_935_);
v___x_945_ = ((size_t)1ULL);
v___x_946_ = lean_usize_sub(v___x_944_, v___x_945_);
v___x_947_ = lean_usize_land(v___x_943_, v___x_946_);
v_bkt_948_ = lean_array_uget_borrowed(v_buckets_931_, v___x_947_);
v___x_949_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(v_a_928_, v_bkt_948_);
if (v___x_949_ == 0)
{
lean_object* v___x_950_; lean_object* v_size_x27_951_; lean_object* v___x_952_; lean_object* v_buckets_x27_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; uint8_t v___x_959_; 
v___x_950_ = lean_unsigned_to_nat(1u);
v_size_x27_951_ = lean_nat_add(v_size_930_, v___x_950_);
lean_dec(v_size_930_);
lean_inc(v_bkt_948_);
v___x_952_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_952_, 0, v_a_928_);
lean_ctor_set(v___x_952_, 1, v_b_929_);
lean_ctor_set(v___x_952_, 2, v_bkt_948_);
v_buckets_x27_953_ = lean_array_uset(v_buckets_931_, v___x_947_, v___x_952_);
v___x_954_ = lean_unsigned_to_nat(4u);
v___x_955_ = lean_nat_mul(v_size_x27_951_, v___x_954_);
v___x_956_ = lean_unsigned_to_nat(3u);
v___x_957_ = lean_nat_div(v___x_955_, v___x_956_);
lean_dec(v___x_955_);
v___x_958_ = lean_array_get_size(v_buckets_x27_953_);
v___x_959_ = lean_nat_dec_le(v___x_957_, v___x_958_);
lean_dec(v___x_957_);
if (v___x_959_ == 0)
{
lean_object* v_val_960_; lean_object* v___x_962_; 
v_val_960_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11___redArg(v_buckets_x27_953_);
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 1, v_val_960_);
lean_ctor_set(v___x_933_, 0, v_size_x27_951_);
v___x_962_ = v___x_933_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_size_x27_951_);
lean_ctor_set(v_reuseFailAlloc_963_, 1, v_val_960_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
else
{
lean_object* v___x_965_; 
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 1, v_buckets_x27_953_);
lean_ctor_set(v___x_933_, 0, v_size_x27_951_);
v___x_965_ = v___x_933_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_size_x27_951_);
lean_ctor_set(v_reuseFailAlloc_966_, 1, v_buckets_x27_953_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
else
{
lean_object* v___x_967_; lean_object* v_buckets_x27_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_972_; 
lean_inc(v_bkt_948_);
v___x_967_ = lean_box(0);
v_buckets_x27_968_ = lean_array_uset(v_buckets_931_, v___x_947_, v___x_967_);
v___x_969_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12___redArg(v_a_928_, v_b_929_, v_bkt_948_);
v___x_970_ = lean_array_uset(v_buckets_x27_968_, v___x_947_, v___x_969_);
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 1, v___x_970_);
v___x_972_ = v___x_933_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_size_930_);
lean_ctor_set(v_reuseFailAlloc_973_, 1, v___x_970_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2(lean_object* v_a_975_, lean_object* v_e_976_, lean_object* v_a_977_){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_979_ = lean_st_ref_take(v_a_975_);
v___x_980_ = lean_box(0);
v___x_981_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6___redArg(v___x_979_, v_e_976_, v_a_977_);
v___x_982_ = lean_st_ref_put(v_a_975_, v___x_981_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2___boxed(lean_object* v_a_983_, lean_object* v_e_984_, lean_object* v_a_985_, lean_object* v___y_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2(v_a_983_, v_e_984_, v_a_985_);
lean_dec(v_a_983_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1(lean_object* v_pre_1004_, lean_object* v_post_1005_, size_t v_sz_1006_, size_t v_i_1007_, lean_object* v_bs_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
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
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4(lean_object* v_pre_1032_, lean_object* v_post_1033_, lean_object* v_x_1034_, lean_object* v_x_1035_, lean_object* v_x_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
if (lean_obj_tag(v_x_1034_) == 5)
{
lean_object* v_fn_1041_; lean_object* v_arg_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
v_fn_1041_ = lean_ctor_get(v_x_1034_, 0);
lean_inc_ref(v_fn_1041_);
v_arg_1042_ = lean_ctor_get(v_x_1034_, 1);
lean_inc_ref(v_arg_1042_);
lean_dec_ref_known(v_x_1034_, 2);
v___x_1043_ = lean_array_set(v_x_1035_, v_x_1036_, v_arg_1042_);
v___x_1044_ = lean_unsigned_to_nat(1u);
v___x_1045_ = lean_nat_sub(v_x_1036_, v___x_1044_);
lean_dec(v_x_1036_);
v_x_1034_ = v_fn_1041_;
v_x_1035_ = v___x_1043_;
v_x_1036_ = v___x_1045_;
goto _start;
}
else
{
lean_object* v___x_1047_; 
lean_dec(v_x_1036_);
lean_inc_ref(v_post_1033_);
lean_inc_ref(v_pre_1032_);
v___x_1047_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1032_, v_post_1033_, v_x_1034_, v___y_1037_, v___y_1038_, v___y_1039_);
if (lean_obj_tag(v___x_1047_) == 0)
{
lean_object* v_a_1048_; size_t v_sz_1049_; size_t v___x_1050_; lean_object* v___x_1051_; 
v_a_1048_ = lean_ctor_get(v___x_1047_, 0);
lean_inc(v_a_1048_);
lean_dec_ref_known(v___x_1047_, 1);
v_sz_1049_ = lean_array_size(v_x_1035_);
v___x_1050_ = ((size_t)0ULL);
lean_inc_ref(v_post_1033_);
lean_inc_ref(v_pre_1032_);
v___x_1051_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1(v_pre_1032_, v_post_1033_, v_sz_1049_, v___x_1050_, v_x_1035_, v___y_1037_, v___y_1038_, v___y_1039_);
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_object* v_a_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v_a_1052_ = lean_ctor_get(v___x_1051_, 0);
lean_inc(v_a_1052_);
lean_dec_ref_known(v___x_1051_, 1);
v___x_1053_ = l_Lean_mkAppN(v_a_1048_, v_a_1052_);
lean_dec(v_a_1052_);
v___x_1054_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1032_, v_post_1033_, v___x_1053_, v___y_1037_, v___y_1038_, v___y_1039_);
return v___x_1054_;
}
else
{
lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1062_; 
lean_dec(v_a_1048_);
lean_dec_ref(v_post_1033_);
lean_dec_ref(v_pre_1032_);
v_a_1055_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1057_ = v___x_1051_;
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v___x_1051_);
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
else
{
lean_dec_ref(v_x_1035_);
lean_dec_ref(v_post_1033_);
lean_dec_ref(v_pre_1032_);
return v___x_1047_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1(lean_object* v___x_1063_, lean_object* v_pre_1064_, lean_object* v_e_1065_, lean_object* v_post_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = l_Lean_Core_checkSystem(v___x_1063_, v___y_1068_, v___y_1069_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v___x_1072_; 
lean_dec_ref_known(v___x_1071_, 1);
lean_inc_ref(v_pre_1064_);
lean_inc(v___y_1069_);
lean_inc_ref(v___y_1068_);
lean_inc_ref(v_e_1065_);
v___x_1072_ = lean_apply_4(v_pre_1064_, v_e_1065_, v___y_1068_, v___y_1069_, lean_box(0));
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1188_; 
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1075_ = v___x_1072_;
v_isShared_1076_ = v_isSharedCheck_1188_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_1072_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1188_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___y_1078_; 
switch(lean_obj_tag(v_a_1073_))
{
case 0:
{
lean_object* v_e_1178_; lean_object* v___x_1180_; 
lean_dec_ref(v_post_1066_);
lean_dec_ref(v_e_1065_);
lean_dec_ref(v_pre_1064_);
v_e_1178_ = lean_ctor_get(v_a_1073_, 0);
lean_inc_ref(v_e_1178_);
lean_dec_ref_known(v_a_1073_, 1);
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 0, v_e_1178_);
v___x_1180_ = v___x_1075_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_e_1178_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
case 1:
{
lean_object* v_e_1182_; lean_object* v___x_1183_; 
lean_del_object(v___x_1075_);
lean_dec_ref(v_e_1065_);
v_e_1182_ = lean_ctor_get(v_a_1073_, 0);
lean_inc_ref(v_e_1182_);
lean_dec_ref_known(v_a_1073_, 1);
lean_inc_ref(v_post_1066_);
lean_inc_ref(v_pre_1064_);
v___x_1183_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1064_, v_post_1066_, v_e_1182_, v___y_1067_, v___y_1068_, v___y_1069_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v_a_1184_; lean_object* v___x_1185_; 
v_a_1184_ = lean_ctor_get(v___x_1183_, 0);
lean_inc(v_a_1184_);
lean_dec_ref_known(v___x_1183_, 1);
v___x_1185_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1064_, v_post_1066_, v_a_1184_, v___y_1067_, v___y_1068_, v___y_1069_);
return v___x_1185_;
}
else
{
lean_dec_ref(v_post_1066_);
lean_dec_ref(v_pre_1064_);
return v___x_1183_;
}
}
default: 
{
lean_object* v_e_x3f_1186_; 
lean_del_object(v___x_1075_);
v_e_x3f_1186_ = lean_ctor_get(v_a_1073_, 0);
lean_inc(v_e_x3f_1186_);
lean_dec_ref_known(v_a_1073_, 1);
if (lean_obj_tag(v_e_x3f_1186_) == 0)
{
v___y_1078_ = v_e_1065_;
goto v___jp_1077_;
}
else
{
lean_object* v_val_1187_; 
lean_dec_ref(v_e_1065_);
v_val_1187_ = lean_ctor_get(v_e_x3f_1186_, 0);
lean_inc(v_val_1187_);
lean_dec_ref_known(v_e_x3f_1186_, 1);
v___y_1078_ = v_val_1187_;
goto v___jp_1077_;
}
}
}
v___jp_1077_:
{
switch(lean_obj_tag(v___y_1078_))
{
case 7:
{
lean_object* v_binderName_1079_; lean_object* v_binderType_1080_; lean_object* v_body_1081_; uint8_t v_binderInfo_1082_; lean_object* v___x_1083_; 
v_binderName_1079_ = lean_ctor_get(v___y_1078_, 0);
v_binderType_1080_ = lean_ctor_get(v___y_1078_, 1);
v_body_1081_ = lean_ctor_get(v___y_1078_, 2);
v_binderInfo_1082_ = lean_ctor_get_uint8(v___y_1078_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1080_);
lean_inc_ref(v_post_1066_);
lean_inc_ref(v_pre_1064_);
v___x_1083_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1064_, v_post_1066_, v_binderType_1080_, v___y_1067_, v___y_1068_, v___y_1069_);
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_object* v_a_1084_; lean_object* v___x_1085_; 
v_a_1084_ = lean_ctor_get(v___x_1083_, 0);
lean_inc(v_a_1084_);
lean_dec_ref_known(v___x_1083_, 1);
lean_inc_ref(v_body_1081_);
lean_inc_ref(v_post_1066_);
lean_inc_ref(v_pre_1064_);
v___x_1085_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1064_, v_post_1066_, v_body_1081_, v___y_1067_, v___y_1068_, v___y_1069_);
if (lean_obj_tag(v___x_1085_) == 0)
{
lean_object* v_a_1086_; size_t v___x_1087_; size_t v___x_1088_; uint8_t v___x_1089_; 
v_a_1086_ = lean_ctor_get(v___x_1085_, 0);
lean_inc(v_a_1086_);
lean_dec_ref_known(v___x_1085_, 1);
v___x_1087_ = lean_ptr_addr(v_binderType_1080_);
v___x_1088_ = lean_ptr_addr(v_a_1084_);
v___x_1089_ = lean_usize_dec_eq(v___x_1087_, v___x_1088_);
if (v___x_1089_ == 0)
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
lean_inc(v_binderName_1079_);
lean_dec_ref_known(v___y_1078_, 3);
v___x_1090_ = l_Lean_Expr_forallE___override(v_binderName_1079_, v_a_1084_, v_a_1086_, v_binderInfo_1082_);
v___x_1091_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1064_, v_post_1066_, v___x_1090_, v___y_1067_, v___y_1068_, v___y_1069_);
return v___x_1091_;
}
else
{
size_t v___x_1092_; size_t v___x_1093_; uint8_t v___x_1094_; 
v___x_1092_ = lean_ptr_addr(v_body_1081_);
v___x_1093_ = lean_ptr_addr(v_a_1086_);
v___x_1094_ = lean_usize_dec_eq(v___x_1092_, v___x_1093_);
if (v___x_1094_ == 0)
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
lean_inc(v_binderName_1079_);
lean_dec_ref_known(v___y_1078_, 3);
v___x_1095_ = l_Lean_Expr_forallE___override(v_binderName_1079_, v_a_1084_, v_a_1086_, v_binderInfo_1082_);
v___x_1096_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1064_, v_post_1066_, v___x_1095_, v___y_1067_, v___y_1068_, v___y_1069_);
return v___x_1096_;
}
else
{
uint8_t v___x_1097_; 
v___x_1097_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1082_, v_binderInfo_1082_);
if (v___x_1097_ == 0)
{
lean_object* v___x_1098_; lean_object* v___x_1099_; 
lean_inc(v_binderName_1079_);
lean_dec_ref_known(v___y_1078_, 3);
v___x_1098_ = l_Lean_Expr_forallE___override(v_binderName_1079_, v_a_1084_, v_a_1086_, v_binderInfo_1082_);
v___x_1099_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1064_, v_post_1066_, v___x_1098_, v___y_1067_, v___y_1068_, v___y_1069_);
return v___x_1099_;
}
else
{
lean_object* v___x_1100_; 
lean_dec(v_a_1086_);
lean_dec(v_a_1084_);
v___x_1100_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1064_, v_post_1066_, v___y_1078_, v___y_1067_, v___y_1068_, v___y_1069_);
return v___x_1100_;
}
}
}
}
else
{
lean_dec(v_a_1084_);
lean_dec_ref_known(v___y_1078_, 3);
lean_dec_ref(v_post_1066_);
lean_dec_ref(v_pre_1064_);
return v___x_1085_;
}
}
else
{
lean_dec_ref_known(v___y_1078_, 3);
lean_dec_ref(v_post_1066_);
lean_dec_ref(v_pre_1064_);
return v___x_1083_;
}
}
case 6:
{
lean_object* v_binderName_1101_; lean_object* v_binderType_1102_; lean_object* v_body_1103_; uint8_t v_binderInfo_1104_; lean_object* v___x_1105_; 
v_binderName_1101_ = lean_ctor_get(v___y_1078_, 0);
v_binderType_1102_ = lean_ctor_get(v___y_1078_, 1);
v_body_1103_ = lean_ctor_get(v___y_1078_, 2);
v_binderInfo_1104_ = lean_ctor_get_uint8(v___y_1078_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1102_);
lean_inc_ref(v_post_1066_);
lean_inc_ref(v_pre_1064_);
v___x_1105_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1064_, v_post_1066_, v_binderType_1102_, v___y_1067_, v___y_1068_, v___y_1069_);
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_object* v_a_1106_; lean_object* v___x_1107_; 
v_a_1106_ = lean_ctor_get(v___x_1105_, 0);
lean_inc(v_a_1106_);
lean_dec_ref_known(v___x_1105_, 1);
lean_inc_ref(v_body_1103_);
lean_inc_ref(v_post_1066_);
lean_inc_ref(v_pre_1064_);
v___x_1107_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1064_, v_post_1066_, v_body_1103_, v___y_1067_, v___y_1068_, v___y_1069_);
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_object* v_a_1108_; size_t v___x_1109_; size_t v___x_1110_; uint8_t v___x_1111_; 
v_a_1108_ = lean_ctor_get(v___x_1107_, 0);
lean_inc(v_a_1108_);
lean_dec_ref_known(v___x_1107_, 1);
v___x_1109_ = lean_ptr_addr(v_binderType_1102_);
v___x_1110_ = lean_ptr_addr(v_a_1106_);
v___x_1111_ = lean_usize_dec_eq(v___x_1109_, v___x_1110_);
if (v___x_1111_ == 0)
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
lean_inc(v_binderName_1101_);
lean_dec_ref_known(v___y_1078_, 3);
v___x_1112_ = l_Lean_Expr_lam___override(v_binderName_1101_, v_a_1106_, v_a_1108_, v_binderInfo_1104_);
v___x_1113_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1064_, v_post_1066_, v___x_1112_, v___y_1067_, v___y_1068_, v___y_1069_);
return v___x_1113_;
}
else
{
size_t v___x_1114_; size_t v___x_1115_; uint8_t v___x_1116_; 
v___x_1114_ = lean_ptr_addr(v_body_1103_);
v___x_1115_ = lean_ptr_addr(v_a_1108_);
v___x_1116_ = lean_usize_dec_eq(v___x_1114_, v___x_1115_);
if (v___x_1116_ == 0)
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
lean_inc(v_binderName_1101_);
lean_dec_ref_known(v___y_1078_, 3);
v___x_1117_ = l_Lean_Expr_lam___override(v_binderName_1101_, v_a_1106_, v_a_1108_, v_binderInfo_1104_);
v___x_1118_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1064_, v_post_1066_, v___x_1117_, v___y_1067_, v___y_1068_, v___y_1069_);
return v___x_1118_;
}
else
{
uint8_t v___x_1119_; 
v___x_1119_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1104_, v_binderInfo_1104_);
if (v___x_1119_ == 0)
{
lean_object* v___x_1120_; lean_object* v___x_1121_; 
lean_inc(v_binderName_1101_);
lean_dec_ref_known(v___y_1078_, 3);
v___x_1120_ = l_Lean_Expr_lam___override(v_binderName_1101_, v_a_1106_, v_a_1108_, v_binderInfo_1104_);
v___x_1121_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1064_, v_post_1066_, v___x_1120_, v___y_1067_, v___y_1068_, v___y_1069_);
return v___x_1121_;
}
else
{
lean_object* v___x_1122_; 
lean_dec(v_a_1108_);
lean_dec(v_a_1106_);
v___x_1122_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1064_, v_post_1066_, v___y_1078_, v___y_1067_, v___y_1068_, v___y_1069_);
return v___x_1122_;
}
}
}
}
else
{
lean_dec(v_a_1106_);
lean_dec_ref_known(v___y_1078_, 3);
lean_dec_ref(v_post_1066_);
lean_dec_ref(v_pre_1064_);
return v___x_1107_;
}
}
else
{
lean_dec_ref_known(v___y_1078_, 3);
lean_dec_ref(v_post_1066_);
lean_dec_ref(v_pre_1064_);
return v___x_1105_;
}
}
case 8:
{
lean_object* v_declName_1123_; lean_object* v_type_1124_; lean_object* v_value_1125_; lean_object* v_body_1126_; uint8_t v_nondep_1127_; lean_object* v___x_1128_; 
v_declName_1123_ = lean_ctor_get(v___y_1078_, 0);
v_type_1124_ = lean_ctor_get(v___y_1078_, 1);
v_value_1125_ = lean_ctor_get(v___y_1078_, 2);
v_body_1126_ = lean_ctor_get(v___y_1078_, 3);
v_nondep_1127_ = lean_ctor_get_uint8(v___y_1078_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_1124_);
lean_inc_ref(v_post_1066_);
lean_inc_ref(v_pre_1064_);
v___x_1128_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1064_, v_post_1066_, v_type_1124_, v___y_1067_, v___y_1068_, v___y_1069_);
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_object* v_a_1129_; lean_object* v___x_1130_; 
v_a_1129_ = lean_ctor_get(v___x_1128_, 0);
lean_inc(v_a_1129_);
lean_dec_ref_known(v___x_1128_, 1);
lean_inc_ref(v_value_1125_);
lean_inc_ref(v_post_1066_);
lean_inc_ref(v_pre_1064_);
v___x_1130_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1064_, v_post_1066_, v_value_1125_, v___y_1067_, v___y_1068_, v___y_1069_);
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v_a_1131_; lean_object* v___x_1132_; 
v_a_1131_ = lean_ctor_get(v___x_1130_, 0);
lean_inc(v_a_1131_);
lean_dec_ref_known(v___x_1130_, 1);
lean_inc_ref(v_body_1126_);
lean_inc_ref(v_post_1066_);
lean_inc_ref(v_pre_1064_);
v___x_1132_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1064_, v_post_1066_, v_body_1126_, v___y_1067_, v___y_1068_, v___y_1069_);
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_object* v_a_1133_; size_t v___x_1134_; size_t v___x_1135_; uint8_t v___x_1136_; 
v_a_1133_ = lean_ctor_get(v___x_1132_, 0);
lean_inc(v_a_1133_);
lean_dec_ref_known(v___x_1132_, 1);
v___x_1134_ = lean_ptr_addr(v_type_1124_);
v___x_1135_ = lean_ptr_addr(v_a_1129_);
v___x_1136_ = lean_usize_dec_eq(v___x_1134_, v___x_1135_);
if (v___x_1136_ == 0)
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
lean_inc(v_declName_1123_);
lean_dec_ref_known(v___y_1078_, 4);
v___x_1137_ = l_Lean_Expr_letE___override(v_declName_1123_, v_a_1129_, v_a_1131_, v_a_1133_, v_nondep_1127_);
v___x_1138_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1064_, v_post_1066_, v___x_1137_, v___y_1067_, v___y_1068_, v___y_1069_);
return v___x_1138_;
}
else
{
size_t v___x_1139_; size_t v___x_1140_; uint8_t v___x_1141_; 
v___x_1139_ = lean_ptr_addr(v_value_1125_);
v___x_1140_ = lean_ptr_addr(v_a_1131_);
v___x_1141_ = lean_usize_dec_eq(v___x_1139_, v___x_1140_);
if (v___x_1141_ == 0)
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
lean_inc(v_declName_1123_);
lean_dec_ref_known(v___y_1078_, 4);
v___x_1142_ = l_Lean_Expr_letE___override(v_declName_1123_, v_a_1129_, v_a_1131_, v_a_1133_, v_nondep_1127_);
v___x_1143_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1064_, v_post_1066_, v___x_1142_, v___y_1067_, v___y_1068_, v___y_1069_);
return v___x_1143_;
}
else
{
size_t v___x_1144_; size_t v___x_1145_; uint8_t v___x_1146_; 
v___x_1144_ = lean_ptr_addr(v_body_1126_);
v___x_1145_ = lean_ptr_addr(v_a_1133_);
v___x_1146_ = lean_usize_dec_eq(v___x_1144_, v___x_1145_);
if (v___x_1146_ == 0)
{
lean_object* v___x_1147_; lean_object* v___x_1148_; 
lean_inc(v_declName_1123_);
lean_dec_ref_known(v___y_1078_, 4);
v___x_1147_ = l_Lean_Expr_letE___override(v_declName_1123_, v_a_1129_, v_a_1131_, v_a_1133_, v_nondep_1127_);
v___x_1148_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1064_, v_post_1066_, v___x_1147_, v___y_1067_, v___y_1068_, v___y_1069_);
return v___x_1148_;
}
else
{
lean_object* v___x_1149_; 
lean_dec(v_a_1133_);
lean_dec(v_a_1131_);
lean_dec(v_a_1129_);
v___x_1149_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1064_, v_post_1066_, v___y_1078_, v___y_1067_, v___y_1068_, v___y_1069_);
return v___x_1149_;
}
}
}
}
else
{
lean_dec(v_a_1131_);
lean_dec(v_a_1129_);
lean_dec_ref_known(v___y_1078_, 4);
lean_dec_ref(v_post_1066_);
lean_dec_ref(v_pre_1064_);
return v___x_1132_;
}
}
else
{
lean_dec(v_a_1129_);
lean_dec_ref_known(v___y_1078_, 4);
lean_dec_ref(v_post_1066_);
lean_dec_ref(v_pre_1064_);
return v___x_1130_;
}
}
else
{
lean_dec_ref_known(v___y_1078_, 4);
lean_dec_ref(v_post_1066_);
lean_dec_ref(v_pre_1064_);
return v___x_1128_;
}
}
case 5:
{
lean_object* v_dummy_1150_; lean_object* v_nargs_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; 
v_dummy_1150_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0);
v_nargs_1151_ = l_Lean_Expr_getAppNumArgs(v___y_1078_);
lean_inc(v_nargs_1151_);
v___x_1152_ = lean_mk_array(v_nargs_1151_, v_dummy_1150_);
v___x_1153_ = lean_unsigned_to_nat(1u);
v___x_1154_ = lean_nat_sub(v_nargs_1151_, v___x_1153_);
lean_dec(v_nargs_1151_);
v___x_1155_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4(v_pre_1064_, v_post_1066_, v___y_1078_, v___x_1152_, v___x_1154_, v___y_1067_, v___y_1068_, v___y_1069_);
return v___x_1155_;
}
case 10:
{
lean_object* v_data_1156_; lean_object* v_expr_1157_; lean_object* v___x_1158_; 
v_data_1156_ = lean_ctor_get(v___y_1078_, 0);
v_expr_1157_ = lean_ctor_get(v___y_1078_, 1);
lean_inc_ref(v_expr_1157_);
lean_inc_ref(v_post_1066_);
lean_inc_ref(v_pre_1064_);
v___x_1158_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1064_, v_post_1066_, v_expr_1157_, v___y_1067_, v___y_1068_, v___y_1069_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v_a_1159_; size_t v___x_1160_; size_t v___x_1161_; uint8_t v___x_1162_; 
v_a_1159_ = lean_ctor_get(v___x_1158_, 0);
lean_inc(v_a_1159_);
lean_dec_ref_known(v___x_1158_, 1);
v___x_1160_ = lean_ptr_addr(v_expr_1157_);
v___x_1161_ = lean_ptr_addr(v_a_1159_);
v___x_1162_ = lean_usize_dec_eq(v___x_1160_, v___x_1161_);
if (v___x_1162_ == 0)
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
lean_inc(v_data_1156_);
lean_dec_ref_known(v___y_1078_, 2);
v___x_1163_ = l_Lean_Expr_mdata___override(v_data_1156_, v_a_1159_);
v___x_1164_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1064_, v_post_1066_, v___x_1163_, v___y_1067_, v___y_1068_, v___y_1069_);
return v___x_1164_;
}
else
{
lean_object* v___x_1165_; 
lean_dec(v_a_1159_);
v___x_1165_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1064_, v_post_1066_, v___y_1078_, v___y_1067_, v___y_1068_, v___y_1069_);
return v___x_1165_;
}
}
else
{
lean_dec_ref_known(v___y_1078_, 2);
lean_dec_ref(v_post_1066_);
lean_dec_ref(v_pre_1064_);
return v___x_1158_;
}
}
case 11:
{
lean_object* v_typeName_1166_; lean_object* v_idx_1167_; lean_object* v_struct_1168_; lean_object* v___x_1169_; 
v_typeName_1166_ = lean_ctor_get(v___y_1078_, 0);
v_idx_1167_ = lean_ctor_get(v___y_1078_, 1);
v_struct_1168_ = lean_ctor_get(v___y_1078_, 2);
lean_inc_ref(v_struct_1168_);
lean_inc_ref(v_post_1066_);
lean_inc_ref(v_pre_1064_);
v___x_1169_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1064_, v_post_1066_, v_struct_1168_, v___y_1067_, v___y_1068_, v___y_1069_);
if (lean_obj_tag(v___x_1169_) == 0)
{
lean_object* v_a_1170_; size_t v___x_1171_; size_t v___x_1172_; uint8_t v___x_1173_; 
v_a_1170_ = lean_ctor_get(v___x_1169_, 0);
lean_inc(v_a_1170_);
lean_dec_ref_known(v___x_1169_, 1);
v___x_1171_ = lean_ptr_addr(v_struct_1168_);
v___x_1172_ = lean_ptr_addr(v_a_1170_);
v___x_1173_ = lean_usize_dec_eq(v___x_1171_, v___x_1172_);
if (v___x_1173_ == 0)
{
lean_object* v___x_1174_; lean_object* v___x_1175_; 
lean_inc(v_idx_1167_);
lean_inc(v_typeName_1166_);
lean_dec_ref_known(v___y_1078_, 3);
v___x_1174_ = l_Lean_Expr_proj___override(v_typeName_1166_, v_idx_1167_, v_a_1170_);
v___x_1175_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1064_, v_post_1066_, v___x_1174_, v___y_1067_, v___y_1068_, v___y_1069_);
return v___x_1175_;
}
else
{
lean_object* v___x_1176_; 
lean_dec(v_a_1170_);
v___x_1176_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1064_, v_post_1066_, v___y_1078_, v___y_1067_, v___y_1068_, v___y_1069_);
return v___x_1176_;
}
}
else
{
lean_dec_ref_known(v___y_1078_, 3);
lean_dec_ref(v_post_1066_);
lean_dec_ref(v_pre_1064_);
return v___x_1169_;
}
}
default: 
{
lean_object* v___x_1177_; 
v___x_1177_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1064_, v_post_1066_, v___y_1078_, v___y_1067_, v___y_1068_, v___y_1069_);
return v___x_1177_;
}
}
}
}
}
else
{
lean_object* v_a_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1196_; 
lean_dec_ref(v_post_1066_);
lean_dec_ref(v_e_1065_);
lean_dec_ref(v_pre_1064_);
v_a_1189_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1191_ = v___x_1072_;
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_a_1189_);
lean_dec(v___x_1072_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v___x_1194_; 
if (v_isShared_1192_ == 0)
{
v___x_1194_ = v___x_1191_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_a_1189_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
}
else
{
lean_object* v_a_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1204_; 
lean_dec_ref(v_post_1066_);
lean_dec_ref(v_e_1065_);
lean_dec_ref(v_pre_1064_);
v_a_1197_ = lean_ctor_get(v___x_1071_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1199_ = v___x_1071_;
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_a_1197_);
lean_dec(v___x_1071_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___boxed(lean_object* v___x_1205_, lean_object* v_pre_1206_, lean_object* v_e_1207_, lean_object* v_post_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1(v___x_1205_, v_pre_1206_, v_e_1207_, v_post_1208_, v___y_1209_, v___y_1210_, v___y_1211_);
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_dec(v___y_1209_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(lean_object* v_pre_1214_, lean_object* v_post_1215_, lean_object* v_e_1216_, lean_object* v_a_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_){
_start:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
lean_inc(v_a_1217_);
v___x_1221_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1221_, 0, lean_box(0));
lean_closure_set(v___x_1221_, 1, lean_box(0));
lean_closure_set(v___x_1221_, 2, v_a_1217_);
v___x_1222_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(lean_box(0), v___x_1221_, v___y_1218_, v___y_1219_);
if (lean_obj_tag(v___x_1222_) == 0)
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1254_; 
v_a_1223_ = lean_ctor_get(v___x_1222_, 0);
v_isSharedCheck_1254_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1225_ = v___x_1222_;
v_isShared_1226_ = v_isSharedCheck_1254_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1222_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1254_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1227_; 
v___x_1227_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg(v_a_1223_, v_e_1216_);
lean_dec(v_a_1223_);
if (lean_obj_tag(v___x_1227_) == 0)
{
lean_object* v___x_1228_; lean_object* v___f_1229_; lean_object* v___x_1230_; 
lean_del_object(v___x_1225_);
v___x_1228_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___closed__0));
lean_inc_ref(v_e_1216_);
v___f_1229_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___boxed), 8, 4);
lean_closure_set(v___f_1229_, 0, v___x_1228_);
lean_closure_set(v___f_1229_, 1, v_pre_1214_);
lean_closure_set(v___f_1229_, 2, v_e_1216_);
lean_closure_set(v___f_1229_, 3, v_post_1215_);
v___x_1230_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg(v___f_1229_, v_a_1217_, v___y_1218_, v___y_1219_);
if (lean_obj_tag(v___x_1230_) == 0)
{
lean_object* v_a_1231_; lean_object* v___f_1232_; lean_object* v___x_1233_; 
v_a_1231_ = lean_ctor_get(v___x_1230_, 0);
lean_inc_n(v_a_1231_, 2);
lean_dec_ref_known(v___x_1230_, 1);
lean_inc(v_a_1217_);
v___f_1232_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1232_, 0, v_a_1217_);
lean_closure_set(v___f_1232_, 1, v_e_1216_);
lean_closure_set(v___f_1232_, 2, v_a_1231_);
v___x_1233_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(lean_box(0), v___f_1232_, v___y_1218_, v___y_1219_);
if (lean_obj_tag(v___x_1233_) == 0)
{
lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1240_; 
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1240_ == 0)
{
lean_object* v_unused_1241_; 
v_unused_1241_ = lean_ctor_get(v___x_1233_, 0);
lean_dec(v_unused_1241_);
v___x_1235_ = v___x_1233_;
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
else
{
lean_dec(v___x_1233_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1238_; 
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 0, v_a_1231_);
v___x_1238_ = v___x_1235_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_a_1231_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
}
else
{
lean_object* v_a_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1249_; 
lean_dec(v_a_1231_);
v_a_1242_ = lean_ctor_get(v___x_1233_, 0);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1244_ = v___x_1233_;
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_a_1242_);
lean_dec(v___x_1233_);
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
lean_dec_ref(v_e_1216_);
return v___x_1230_;
}
}
else
{
lean_object* v_val_1250_; lean_object* v___x_1252_; 
lean_dec_ref(v_e_1216_);
lean_dec_ref(v_post_1215_);
lean_dec_ref(v_pre_1214_);
v_val_1250_ = lean_ctor_get(v___x_1227_, 0);
lean_inc(v_val_1250_);
lean_dec_ref_known(v___x_1227_, 1);
if (v_isShared_1226_ == 0)
{
lean_ctor_set(v___x_1225_, 0, v_val_1250_);
v___x_1252_ = v___x_1225_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_val_1250_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
return v___x_1252_;
}
}
}
}
else
{
lean_object* v_a_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1262_; 
lean_dec_ref(v_e_1216_);
lean_dec_ref(v_post_1215_);
lean_dec_ref(v_pre_1214_);
v_a_1255_ = lean_ctor_get(v___x_1222_, 0);
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1257_ = v___x_1222_;
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_a_1255_);
lean_dec(v___x_1222_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1260_; 
if (v_isShared_1258_ == 0)
{
v___x_1260_ = v___x_1257_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v_a_1255_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(lean_object* v_pre_1263_, lean_object* v_post_1264_, lean_object* v_e_1265_, lean_object* v_a_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_){
_start:
{
lean_object* v___x_1270_; 
lean_inc_ref(v_post_1264_);
lean_inc(v___y_1268_);
lean_inc_ref(v___y_1267_);
lean_inc_ref(v_e_1265_);
v___x_1270_ = lean_apply_4(v_post_1264_, v_e_1265_, v___y_1267_, v___y_1268_, lean_box(0));
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_object* v_a_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1289_; 
v_a_1271_ = lean_ctor_get(v___x_1270_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1273_ = v___x_1270_;
v_isShared_1274_ = v_isSharedCheck_1289_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_a_1271_);
lean_dec(v___x_1270_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1289_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
switch(lean_obj_tag(v_a_1271_))
{
case 0:
{
lean_object* v_e_1275_; lean_object* v___x_1277_; 
lean_dec_ref(v_e_1265_);
lean_dec_ref(v_post_1264_);
lean_dec_ref(v_pre_1263_);
v_e_1275_ = lean_ctor_get(v_a_1271_, 0);
lean_inc_ref(v_e_1275_);
lean_dec_ref_known(v_a_1271_, 1);
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 0, v_e_1275_);
v___x_1277_ = v___x_1273_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_e_1275_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
case 1:
{
lean_object* v_e_1279_; lean_object* v___x_1280_; 
lean_del_object(v___x_1273_);
lean_dec_ref(v_e_1265_);
v_e_1279_ = lean_ctor_get(v_a_1271_, 0);
lean_inc_ref(v_e_1279_);
lean_dec_ref_known(v_a_1271_, 1);
v___x_1280_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1263_, v_post_1264_, v_e_1279_, v_a_1266_, v___y_1267_, v___y_1268_);
return v___x_1280_;
}
default: 
{
lean_object* v_e_x3f_1281_; 
lean_dec_ref(v_post_1264_);
lean_dec_ref(v_pre_1263_);
v_e_x3f_1281_ = lean_ctor_get(v_a_1271_, 0);
lean_inc(v_e_x3f_1281_);
lean_dec_ref_known(v_a_1271_, 1);
if (lean_obj_tag(v_e_x3f_1281_) == 0)
{
lean_object* v___x_1283_; 
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 0, v_e_1265_);
v___x_1283_ = v___x_1273_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_e_1265_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
else
{
lean_object* v_val_1285_; lean_object* v___x_1287_; 
lean_dec_ref(v_e_1265_);
v_val_1285_ = lean_ctor_get(v_e_x3f_1281_, 0);
lean_inc(v_val_1285_);
lean_dec_ref_known(v_e_x3f_1281_, 1);
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 0, v_val_1285_);
v___x_1287_ = v___x_1273_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_val_1285_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
}
}
}
}
else
{
lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1297_; 
lean_dec_ref(v_e_1265_);
lean_dec_ref(v_post_1264_);
lean_dec_ref(v_pre_1263_);
v_a_1290_ = lean_ctor_get(v___x_1270_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1292_ = v___x_1270_;
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v___x_1270_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1295_; 
if (v_isShared_1293_ == 0)
{
v___x_1295_ = v___x_1292_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_a_1290_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_1298_, lean_object* v_post_1299_, lean_object* v_e_1300_, lean_object* v_a_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_){
_start:
{
lean_object* v_res_1305_; 
v_res_1305_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1298_, v_post_1299_, v_e_1300_, v_a_1301_, v___y_1302_, v___y_1303_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
lean_dec(v_a_1301_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_1306_, lean_object* v_post_1307_, lean_object* v_sz_1308_, lean_object* v_i_1309_, lean_object* v_bs_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_){
_start:
{
size_t v_sz_boxed_1315_; size_t v_i_boxed_1316_; lean_object* v_res_1317_; 
v_sz_boxed_1315_ = lean_unbox_usize(v_sz_1308_);
lean_dec(v_sz_1308_);
v_i_boxed_1316_ = lean_unbox_usize(v_i_1309_);
lean_dec(v_i_1309_);
v_res_1317_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1(v_pre_1306_, v_post_1307_, v_sz_boxed_1315_, v_i_boxed_1316_, v_bs_1310_, v___y_1311_, v___y_1312_, v___y_1313_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
lean_dec(v___y_1311_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_1318_, lean_object* v_post_1319_, lean_object* v_x_1320_, lean_object* v_x_1321_, lean_object* v_x_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4(v_pre_1318_, v_post_1319_, v_x_1320_, v_x_1321_, v_x_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec(v___y_1323_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___boxed(lean_object* v_pre_1328_, lean_object* v_post_1329_, lean_object* v_e_1330_, lean_object* v_a_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1328_, v_post_1329_, v_e_1330_, v_a_1331_, v___y_1332_, v___y_1333_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v_a_1331_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(lean_object* v_00_u03b1_1336_, lean_object* v_x_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_){
_start:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1341_ = lean_apply_1(v_x_1337_, lean_box(0));
v___x_1342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1341_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1343_, lean_object* v_x_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_){
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(v_00_u03b1_1343_, v_x_1344_, v___y_1345_, v___y_1346_);
lean_dec(v___y_1346_);
lean_dec_ref(v___y_1345_);
return v_res_1348_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; 
v___x_1349_ = lean_box(0);
v___x_1350_ = lean_unsigned_to_nat(16u);
v___x_1351_ = lean_mk_array(v___x_1350_, v___x_1349_);
return v___x_1351_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
v___x_1352_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0, &l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0);
v___x_1353_ = lean_unsigned_to_nat(0u);
v___x_1354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1354_, 0, v___x_1353_);
lean_ctor_set(v___x_1354_, 1, v___x_1352_);
return v___x_1354_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1355_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1, &l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1_once, _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1);
v___x_1356_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1356_, 0, lean_box(0));
lean_closure_set(v___x_1356_, 1, lean_box(0));
lean_closure_set(v___x_1356_, 2, v___x_1355_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0(lean_object* v_input_1357_, lean_object* v_pre_1358_, lean_object* v_post_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_){
_start:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v_a_1365_; lean_object* v___x_1366_; 
v___x_1363_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2);
v___x_1364_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(lean_box(0), v___x_1363_, v___y_1360_, v___y_1361_);
v_a_1365_ = lean_ctor_get(v___x_1364_, 0);
lean_inc(v_a_1365_);
lean_dec_ref(v___x_1364_);
v___x_1366_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1358_, v_post_1359_, v_input_1357_, v_a_1365_, v___y_1360_, v___y_1361_);
if (lean_obj_tag(v___x_1366_) == 0)
{
lean_object* v_a_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1376_; 
v_a_1367_ = lean_ctor_get(v___x_1366_, 0);
lean_inc(v_a_1367_);
lean_dec_ref_known(v___x_1366_, 1);
v___x_1368_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1368_, 0, lean_box(0));
lean_closure_set(v___x_1368_, 1, lean_box(0));
lean_closure_set(v___x_1368_, 2, v_a_1365_);
v___x_1369_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(lean_box(0), v___x_1368_, v___y_1360_, v___y_1361_);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1376_ == 0)
{
lean_object* v_unused_1377_; 
v_unused_1377_ = lean_ctor_get(v___x_1369_, 0);
lean_dec(v_unused_1377_);
v___x_1371_ = v___x_1369_;
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
else
{
lean_dec(v___x_1369_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1374_; 
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 0, v_a_1367_);
v___x_1374_ = v___x_1371_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_a_1367_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
else
{
lean_dec(v_a_1365_);
return v___x_1366_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___boxed(lean_object* v_input_1378_, lean_object* v_pre_1379_, lean_object* v_post_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0(v_input_1378_, v_pre_1379_, v_post_1380_, v___y_1381_, v___y_1382_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(lean_object* v_e_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_){
_start:
{
lean_object* v___f_1391_; lean_object* v___f_1392_; lean_object* v___x_1393_; 
v___f_1391_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___closed__0));
v___f_1392_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___closed__1));
v___x_1393_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0(v_e_1387_, v___f_1391_, v___f_1392_, v_a_1388_, v_a_1389_);
return v___x_1393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___boxed(lean_object* v_e_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_){
_start:
{
lean_object* v_res_1398_; 
v_res_1398_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(v_e_1394_, v_a_1395_, v_a_1396_);
lean_dec(v_a_1396_);
lean_dec_ref(v_a_1395_);
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1399_, lean_object* v_m_1400_, lean_object* v_a_1401_){
_start:
{
lean_object* v___x_1402_; 
v___x_1402_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg(v_m_1400_, v_a_1401_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1403_, lean_object* v_m_1404_, lean_object* v_a_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3(v_00_u03b2_1403_, v_m_1404_, v_a_1405_);
lean_dec_ref(v_a_1405_);
lean_dec_ref(v_m_1404_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_1407_, lean_object* v_ref_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_){
_start:
{
lean_object* v___x_1412_; 
v___x_1412_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1408_);
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1413_, lean_object* v_ref_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
lean_object* v_res_1418_; 
v_res_1418_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_1413_, v_ref_1414_, v___y_1415_, v___y_1416_);
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8(lean_object* v_00_u03b1_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v___x_1423_; 
v___x_1423_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg();
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_){
_start:
{
lean_object* v_res_1428_; 
v_res_1428_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8(v_00_u03b1_1424_, v___y_1425_, v___y_1426_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
return v_res_1428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_1429_, lean_object* v_x_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_){
_start:
{
lean_object* v___x_1435_; 
v___x_1435_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg(v_x_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_1436_, lean_object* v_x_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5(v_00_u03b1_1436_, v_x_1437_, v___y_1438_, v___y_1439_, v___y_1440_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
lean_dec(v___y_1438_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_1443_, lean_object* v_m_1444_, lean_object* v_a_1445_, lean_object* v_b_1446_){
_start:
{
lean_object* v___x_1447_; 
v___x_1447_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6___redArg(v_m_1444_, v_a_1445_, v_b_1446_);
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_1448_, lean_object* v_a_1449_, lean_object* v_x_1450_){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1449_, v_x_1450_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1452_, lean_object* v_a_1453_, lean_object* v_x_1454_){
_start:
{
lean_object* v_res_1455_; 
v_res_1455_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_1452_, v_a_1453_, v_x_1454_);
lean_dec(v_x_1454_);
lean_dec_ref(v_a_1453_);
return v_res_1455_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_1456_, lean_object* v_a_1457_, lean_object* v_x_1458_){
_start:
{
uint8_t v___x_1459_; 
v___x_1459_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1457_, v_x_1458_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___boxed(lean_object* v_00_u03b2_1460_, lean_object* v_a_1461_, lean_object* v_x_1462_){
_start:
{
uint8_t v_res_1463_; lean_object* v_r_1464_; 
v_res_1463_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10(v_00_u03b2_1460_, v_a_1461_, v_x_1462_);
lean_dec(v_x_1462_);
lean_dec_ref(v_a_1461_);
v_r_1464_ = lean_box(v_res_1463_);
return v_r_1464_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_1465_, lean_object* v_data_1466_){
_start:
{
lean_object* v___x_1467_; 
v___x_1467_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11___redArg(v_data_1466_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12(lean_object* v_00_u03b2_1468_, lean_object* v_a_1469_, lean_object* v_b_1470_, lean_object* v_x_1471_){
_start:
{
lean_object* v___x_1472_; 
v___x_1472_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1469_, v_b_1470_, v_x_1471_);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12(lean_object* v_00_u03b2_1473_, lean_object* v_i_1474_, lean_object* v_source_1475_, lean_object* v_target_1476_){
_start:
{
lean_object* v___x_1477_; 
v___x_1477_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v_i_1474_, v_source_1475_, v_target_1476_);
return v___x_1477_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_1478_, lean_object* v_x_1479_, lean_object* v_x_1480_){
_start:
{
lean_object* v___x_1481_; 
v___x_1481_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_x_1479_, v_x_1480_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(lean_object* v_declName_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v___x_1485_; lean_object* v_env_1486_; uint8_t v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1485_ = lean_st_ref_get(v___y_1483_);
v_env_1486_ = lean_ctor_get(v___x_1485_, 0);
lean_inc_ref(v_env_1486_);
lean_dec(v___x_1485_);
v___x_1487_ = l_Lean_isRecCore(v_env_1486_, v_declName_1482_);
v___x_1488_ = lean_box(v___x_1487_);
v___x_1489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1488_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg___boxed(lean_object* v_declName_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(v_declName_1490_, v___y_1491_);
lean_dec(v___y_1491_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2(lean_object* v_declName_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
lean_object* v___x_1500_; 
v___x_1500_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(v_declName_1494_, v___y_1498_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___boxed(lean_object* v_declName_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_){
_start:
{
lean_object* v_res_1507_; 
v_res_1507_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2(v_declName_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(lean_object* v_declName_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v___x_1511_; lean_object* v_env_1512_; uint8_t v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1511_ = lean_st_ref_get(v___y_1509_);
v_env_1512_ = lean_ctor_get(v___x_1511_, 0);
lean_inc_ref(v_env_1512_);
lean_dec(v___x_1511_);
v___x_1513_ = l_Lean_getReducibilityStatusCore(v_env_1512_, v_declName_1508_);
v___x_1514_ = lean_box(v___x_1513_);
v___x_1515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1515_, 0, v___x_1514_);
return v___x_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg___boxed(lean_object* v_declName_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(v_declName_1516_, v___y_1517_);
lean_dec(v___y_1517_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0(lean_object* v_declName_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_){
_start:
{
lean_object* v___x_1526_; lean_object* v_a_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1542_; 
v___x_1526_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(v_declName_1520_, v___y_1524_);
v_a_1527_ = lean_ctor_get(v___x_1526_, 0);
v_isSharedCheck_1542_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1529_ = v___x_1526_;
v_isShared_1530_ = v_isSharedCheck_1542_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_a_1527_);
lean_dec(v___x_1526_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1542_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
uint8_t v___x_1531_; 
v___x_1531_ = lean_unbox(v_a_1527_);
lean_dec(v_a_1527_);
if (v___x_1531_ == 0)
{
uint8_t v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1535_; 
v___x_1532_ = 1;
v___x_1533_ = lean_box(v___x_1532_);
if (v_isShared_1530_ == 0)
{
lean_ctor_set(v___x_1529_, 0, v___x_1533_);
v___x_1535_ = v___x_1529_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v___x_1533_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
else
{
uint8_t v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1540_; 
v___x_1537_ = 0;
v___x_1538_ = lean_box(v___x_1537_);
if (v_isShared_1530_ == 0)
{
lean_ctor_set(v___x_1529_, 0, v___x_1538_);
v___x_1540_ = v___x_1529_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v___x_1538_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0___boxed(lean_object* v_declName_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_){
_start:
{
lean_object* v_res_1549_; 
v_res_1549_ = l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0(v_declName_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
lean_dec(v___y_1545_);
lean_dec_ref(v___y_1544_);
return v_res_1549_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(lean_object* v_a_1550_, lean_object* v_b_1551_){
_start:
{
lean_object* v_array_1553_; lean_object* v_start_1554_; lean_object* v_stop_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1572_; 
v_array_1553_ = lean_ctor_get(v_a_1550_, 0);
v_start_1554_ = lean_ctor_get(v_a_1550_, 1);
v_stop_1555_ = lean_ctor_get(v_a_1550_, 2);
v_isSharedCheck_1572_ = !lean_is_exclusive(v_a_1550_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1557_ = v_a_1550_;
v_isShared_1558_ = v_isSharedCheck_1572_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_stop_1555_);
lean_inc(v_start_1554_);
lean_inc(v_array_1553_);
lean_dec(v_a_1550_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1572_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
uint8_t v___x_1559_; 
v___x_1559_ = lean_nat_dec_lt(v_start_1554_, v_stop_1555_);
if (v___x_1559_ == 0)
{
lean_object* v___x_1560_; 
lean_del_object(v___x_1557_);
lean_dec(v_stop_1555_);
lean_dec(v_start_1554_);
lean_dec_ref(v_array_1553_);
v___x_1560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1560_, 0, v_b_1551_);
return v___x_1560_;
}
else
{
lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1565_; 
v___x_1561_ = lean_box(0);
v___x_1562_ = lean_unsigned_to_nat(1u);
v___x_1563_ = lean_nat_add(v_start_1554_, v___x_1562_);
lean_inc_ref(v_array_1553_);
if (v_isShared_1558_ == 0)
{
lean_ctor_set(v___x_1557_, 1, v___x_1563_);
v___x_1565_ = v___x_1557_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_array_1553_);
lean_ctor_set(v_reuseFailAlloc_1571_, 1, v___x_1563_);
lean_ctor_set(v_reuseFailAlloc_1571_, 2, v_stop_1555_);
v___x_1565_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
lean_object* v___x_1566_; uint8_t v___x_1567_; 
v___x_1566_ = lean_array_fget(v_array_1553_, v_start_1554_);
lean_dec(v_start_1554_);
lean_dec_ref(v_array_1553_);
v___x_1567_ = l_Lean_Expr_hasExprMVar(v___x_1566_);
lean_dec(v___x_1566_);
if (v___x_1567_ == 0)
{
v_a_1550_ = v___x_1565_;
v_b_1551_ = v___x_1561_;
goto _start;
}
else
{
lean_object* v___x_1569_; 
v___x_1569_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_dec_ref_known(v___x_1569_, 1);
v_a_1550_ = v___x_1565_;
v_b_1551_ = v___x_1561_;
goto _start;
}
else
{
lean_dec_ref(v___x_1565_);
return v___x_1569_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg___boxed(lean_object* v_a_1573_, lean_object* v_b_1574_, lean_object* v___y_1575_){
_start:
{
lean_object* v_res_1576_; 
v_res_1576_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(v_a_1573_, v_b_1574_);
return v_res_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(lean_object* v_e_1585_, uint8_t v_isMatch_1586_, uint8_t v_root_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_){
_start:
{
lean_object* v___y_1594_; lean_object* v_b_1595_; lean_object* v___x_1606_; 
v___x_1606_ = l_Lean_Meta_DiscrTree_reduceDT(v_e_1585_, v_root_1587_, v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_);
if (lean_obj_tag(v___x_1606_) == 0)
{
lean_object* v_a_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1769_; 
v_a_1607_ = lean_ctor_get(v___x_1606_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1609_ = v___x_1606_;
v_isShared_1610_ = v_isSharedCheck_1769_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_dec(v___x_1606_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1769_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___y_1612_; lean_object* v___y_1622_; lean_object* v___y_1623_; lean_object* v___y_1624_; lean_object* v___y_1625_; 
if (v_root_1587_ == 0)
{
lean_object* v___x_1757_; 
lean_inc(v_a_1607_);
v___x_1757_ = l_Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f(v_a_1607_);
if (lean_obj_tag(v___x_1757_) == 1)
{
lean_object* v_val_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1768_; 
lean_del_object(v___x_1609_);
lean_dec(v_a_1607_);
v_val_1758_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1760_ = v___x_1757_;
v_isShared_1761_ = v_isSharedCheck_1768_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_val_1758_);
lean_dec(v___x_1757_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1768_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1763_; 
if (v_isShared_1761_ == 0)
{
lean_ctor_set_tag(v___x_1760_, 2);
v___x_1763_ = v___x_1760_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_val_1758_);
v___x_1763_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1764_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
v___x_1765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1763_);
lean_ctor_set(v___x_1765_, 1, v___x_1764_);
v___x_1766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1766_, 0, v___x_1765_);
return v___x_1766_;
}
}
}
else
{
lean_dec(v___x_1757_);
v___y_1622_ = v_a_1588_;
v___y_1623_ = v_a_1589_;
v___y_1624_ = v_a_1590_;
v___y_1625_ = v_a_1591_;
goto v___jp_1621_;
}
}
else
{
v___y_1622_ = v_a_1588_;
v___y_1623_ = v_a_1589_;
v___y_1624_ = v_a_1590_;
v___y_1625_ = v_a_1591_;
goto v___jp_1621_;
}
v___jp_1611_:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1619_; 
v___x_1613_ = l_Lean_Expr_getAppNumArgs(v_a_1607_);
lean_inc(v___x_1613_);
v___x_1614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1614_, 0, v___y_1612_);
lean_ctor_set(v___x_1614_, 1, v___x_1613_);
v___x_1615_ = lean_mk_empty_array_with_capacity(v___x_1613_);
lean_dec(v___x_1613_);
v___x_1616_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1607_, v___x_1615_);
v___x_1617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1614_);
lean_ctor_set(v___x_1617_, 1, v___x_1616_);
if (v_isShared_1610_ == 0)
{
lean_ctor_set(v___x_1609_, 0, v___x_1617_);
v___x_1619_ = v___x_1609_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v___x_1617_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
v___jp_1621_:
{
lean_object* v___x_1626_; 
v___x_1626_ = l_Lean_Expr_getAppFn(v_a_1607_);
switch(lean_obj_tag(v___x_1626_))
{
case 1:
{
lean_object* v_fvarId_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
lean_del_object(v___x_1609_);
v_fvarId_1627_ = lean_ctor_get(v___x_1626_, 0);
lean_inc(v_fvarId_1627_);
lean_dec_ref_known(v___x_1626_, 1);
v___x_1628_ = l_Lean_Expr_getAppNumArgs(v_a_1607_);
lean_inc(v___x_1628_);
v___x_1629_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1629_, 0, v_fvarId_1627_);
lean_ctor_set(v___x_1629_, 1, v___x_1628_);
v___x_1630_ = lean_mk_empty_array_with_capacity(v___x_1628_);
lean_dec(v___x_1628_);
v___x_1631_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1607_, v___x_1630_);
v___x_1632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1629_);
lean_ctor_set(v___x_1632_, 1, v___x_1631_);
v___x_1633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1632_);
return v___x_1633_;
}
case 2:
{
lean_del_object(v___x_1609_);
lean_dec(v_a_1607_);
if (v_isMatch_1586_ == 0)
{
lean_object* v_mvarId_1634_; lean_object* v___x_1635_; uint8_t v_isDefEqStuckEx_1636_; 
v_mvarId_1634_ = lean_ctor_get(v___x_1626_, 0);
lean_inc(v_mvarId_1634_);
lean_dec_ref_known(v___x_1626_, 1);
v___x_1635_ = l_Lean_Meta_Context_config(v___y_1622_);
v_isDefEqStuckEx_1636_ = lean_ctor_get_uint8(v___x_1635_, 4);
lean_dec_ref(v___x_1635_);
if (v_isDefEqStuckEx_1636_ == 0)
{
lean_object* v___x_1637_; 
v___x_1637_ = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(v_mvarId_1634_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
if (lean_obj_tag(v___x_1637_) == 0)
{
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1651_; 
v_a_1638_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1640_ = v___x_1637_;
v_isShared_1641_ = v_isSharedCheck_1651_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1637_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1651_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
uint8_t v___x_1642_; 
v___x_1642_ = lean_unbox(v_a_1638_);
lean_dec(v_a_1638_);
if (v___x_1642_ == 0)
{
lean_object* v___x_1643_; lean_object* v___x_1645_; 
v___x_1643_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__2));
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 0, v___x_1643_);
v___x_1645_ = v___x_1640_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v___x_1643_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
else
{
lean_object* v___x_1647_; lean_object* v___x_1649_; 
v___x_1647_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 0, v___x_1647_);
v___x_1649_ = v___x_1640_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v___x_1647_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
}
else
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1659_; 
v_a_1652_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1654_ = v___x_1637_;
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1637_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1657_; 
if (v_isShared_1655_ == 0)
{
v___x_1657_ = v___x_1654_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_a_1652_);
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
lean_object* v___x_1660_; lean_object* v___x_1661_; 
lean_dec(v_mvarId_1634_);
v___x_1660_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__2));
v___x_1661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1661_, 0, v___x_1660_);
return v___x_1661_;
}
}
else
{
lean_object* v___x_1662_; lean_object* v___x_1663_; 
lean_dec_ref_known(v___x_1626_, 1);
v___x_1662_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
v___x_1663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1662_);
return v___x_1663_;
}
}
case 4:
{
lean_object* v_declName_1664_; lean_object* v___x_1665_; uint8_t v_isDefEqStuckEx_1666_; 
v_declName_1664_ = lean_ctor_get(v___x_1626_, 0);
lean_inc(v_declName_1664_);
lean_dec_ref_known(v___x_1626_, 2);
v___x_1665_ = l_Lean_Meta_Context_config(v___y_1622_);
v_isDefEqStuckEx_1666_ = lean_ctor_get_uint8(v___x_1665_, 4);
lean_dec_ref(v___x_1665_);
if (v_isDefEqStuckEx_1666_ == 0)
{
v___y_1612_ = v_declName_1664_;
goto v___jp_1611_;
}
else
{
uint8_t v___x_1667_; 
v___x_1667_ = l_Lean_Expr_hasExprMVar(v_a_1607_);
if (v___x_1667_ == 0)
{
v___y_1612_ = v_declName_1664_;
goto v___jp_1611_;
}
else
{
lean_object* v___x_1668_; 
lean_inc(v_declName_1664_);
v___x_1668_ = l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0(v_declName_1664_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_object* v_a_1669_; uint8_t v___x_1670_; 
v_a_1669_ = lean_ctor_get(v___x_1668_, 0);
lean_inc(v_a_1669_);
lean_dec_ref_known(v___x_1668_, 1);
v___x_1670_ = lean_unbox(v_a_1669_);
lean_dec(v_a_1669_);
if (v___x_1670_ == 0)
{
lean_object* v___x_1671_; lean_object* v_env_1672_; lean_object* v___x_1673_; 
v___x_1671_ = lean_st_ref_get(v___y_1625_);
v_env_1672_ = lean_ctor_get(v___x_1671_, 0);
lean_inc_ref(v_env_1672_);
lean_dec(v___x_1671_);
v___x_1673_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_1672_, v_a_1607_);
if (lean_obj_tag(v___x_1673_) == 1)
{
lean_object* v_val_1674_; lean_object* v_numDiscrs_1675_; lean_object* v_nargs_1676_; lean_object* v_dummy_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
v_val_1674_ = lean_ctor_get(v___x_1673_, 0);
lean_inc(v_val_1674_);
lean_dec_ref_known(v___x_1673_, 1);
v_numDiscrs_1675_ = lean_ctor_get(v_val_1674_, 1);
lean_inc(v_numDiscrs_1675_);
v_nargs_1676_ = l_Lean_Expr_getAppNumArgs(v_a_1607_);
v_dummy_1677_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0);
lean_inc(v_nargs_1676_);
v___x_1678_ = lean_mk_array(v_nargs_1676_, v_dummy_1677_);
v___x_1679_ = lean_unsigned_to_nat(1u);
v___x_1680_ = lean_nat_sub(v_nargs_1676_, v___x_1679_);
lean_dec(v_nargs_1676_);
lean_inc(v_a_1607_);
v___x_1681_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1607_, v___x_1678_, v___x_1680_);
v___x_1682_ = l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(v_val_1674_);
lean_dec(v_val_1674_);
v___x_1683_ = lean_nat_add(v___x_1682_, v_numDiscrs_1675_);
lean_dec(v_numDiscrs_1675_);
v___x_1684_ = l_Array_toSubarray___redArg(v___x_1681_, v___x_1682_, v___x_1683_);
v___x_1685_ = lean_box(0);
v___x_1686_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(v___x_1684_, v___x_1685_);
if (lean_obj_tag(v___x_1686_) == 0)
{
lean_dec_ref_known(v___x_1686_, 1);
v___y_1612_ = v_declName_1664_;
goto v___jp_1611_;
}
else
{
lean_object* v_a_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1694_; 
lean_dec(v_declName_1664_);
lean_del_object(v___x_1609_);
lean_dec(v_a_1607_);
v_a_1687_ = lean_ctor_get(v___x_1686_, 0);
v_isSharedCheck_1694_ = !lean_is_exclusive(v___x_1686_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1689_ = v___x_1686_;
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_a_1687_);
lean_dec(v___x_1686_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v___x_1692_; 
if (v_isShared_1690_ == 0)
{
v___x_1692_ = v___x_1689_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_a_1687_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
}
}
else
{
lean_object* v___x_1695_; lean_object* v_a_1696_; uint8_t v___x_1697_; 
lean_dec(v___x_1673_);
lean_inc(v_declName_1664_);
v___x_1695_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(v_declName_1664_, v___y_1625_);
v_a_1696_ = lean_ctor_get(v___x_1695_, 0);
lean_inc(v_a_1696_);
lean_dec_ref(v___x_1695_);
v___x_1697_ = lean_unbox(v_a_1696_);
lean_dec(v_a_1696_);
if (v___x_1697_ == 0)
{
v___y_1612_ = v_declName_1664_;
goto v___jp_1611_;
}
else
{
lean_object* v___x_1698_; 
v___x_1698_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1698_) == 0)
{
lean_dec_ref_known(v___x_1698_, 1);
v___y_1612_ = v_declName_1664_;
goto v___jp_1611_;
}
else
{
lean_object* v_a_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1706_; 
lean_dec(v_declName_1664_);
lean_del_object(v___x_1609_);
lean_dec(v_a_1607_);
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
}
}
else
{
lean_object* v___x_1707_; 
v___x_1707_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_dec_ref_known(v___x_1707_, 1);
v___y_1612_ = v_declName_1664_;
goto v___jp_1611_;
}
else
{
lean_object* v_a_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1715_; 
lean_dec(v_declName_1664_);
lean_del_object(v___x_1609_);
lean_dec(v_a_1607_);
v_a_1708_ = lean_ctor_get(v___x_1707_, 0);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1710_ = v___x_1707_;
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_a_1708_);
lean_dec(v___x_1707_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1713_; 
if (v_isShared_1711_ == 0)
{
v___x_1713_ = v___x_1710_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_a_1708_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
}
}
}
else
{
lean_object* v_a_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1723_; 
lean_dec(v_declName_1664_);
lean_del_object(v___x_1609_);
lean_dec(v_a_1607_);
v_a_1716_ = lean_ctor_get(v___x_1668_, 0);
v_isSharedCheck_1723_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1723_ == 0)
{
v___x_1718_ = v___x_1668_;
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_a_1716_);
lean_dec(v___x_1668_);
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
}
case 7:
{
lean_object* v_binderType_1724_; lean_object* v_body_1725_; uint8_t v___x_1726_; 
lean_del_object(v___x_1609_);
lean_dec(v_a_1607_);
v_binderType_1724_ = lean_ctor_get(v___x_1626_, 1);
lean_inc_ref(v_binderType_1724_);
v_body_1725_ = lean_ctor_get(v___x_1626_, 2);
lean_inc_ref(v_body_1725_);
lean_dec_ref_known(v___x_1626_, 3);
v___x_1726_ = l_Lean_Expr_hasLooseBVars(v_body_1725_);
if (v___x_1726_ == 0)
{
v___y_1594_ = v_binderType_1724_;
v_b_1595_ = v_body_1725_;
goto v___jp_1593_;
}
else
{
lean_object* v___x_1727_; 
v___x_1727_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(v_body_1725_, v___y_1624_, v___y_1625_);
if (lean_obj_tag(v___x_1727_) == 0)
{
lean_object* v_a_1728_; 
v_a_1728_ = lean_ctor_get(v___x_1727_, 0);
lean_inc(v_a_1728_);
lean_dec_ref_known(v___x_1727_, 1);
v___y_1594_ = v_binderType_1724_;
v_b_1595_ = v_a_1728_;
goto v___jp_1593_;
}
else
{
lean_object* v_a_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1736_; 
lean_dec_ref(v_binderType_1724_);
v_a_1729_ = lean_ctor_get(v___x_1727_, 0);
v_isSharedCheck_1736_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1731_ = v___x_1727_;
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_a_1729_);
lean_dec(v___x_1727_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1734_; 
if (v_isShared_1732_ == 0)
{
v___x_1734_ = v___x_1731_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_a_1729_);
v___x_1734_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
return v___x_1734_;
}
}
}
}
}
case 9:
{
lean_object* v_a_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; 
lean_del_object(v___x_1609_);
lean_dec(v_a_1607_);
v_a_1737_ = lean_ctor_get(v___x_1626_, 0);
lean_inc_ref(v_a_1737_);
lean_dec_ref_known(v___x_1626_, 1);
v___x_1738_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1738_, 0, v_a_1737_);
v___x_1739_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
v___x_1740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1740_, 0, v___x_1738_);
lean_ctor_set(v___x_1740_, 1, v___x_1739_);
v___x_1741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1741_, 0, v___x_1740_);
return v___x_1741_;
}
case 11:
{
lean_object* v_typeName_1742_; lean_object* v_idx_1743_; lean_object* v_struct_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
lean_del_object(v___x_1609_);
v_typeName_1742_ = lean_ctor_get(v___x_1626_, 0);
lean_inc(v_typeName_1742_);
v_idx_1743_ = lean_ctor_get(v___x_1626_, 1);
lean_inc(v_idx_1743_);
v_struct_1744_ = lean_ctor_get(v___x_1626_, 2);
lean_inc_ref(v_struct_1744_);
lean_dec_ref_known(v___x_1626_, 3);
v___x_1745_ = l_Lean_Expr_getAppNumArgs(v_a_1607_);
lean_inc(v___x_1745_);
v___x_1746_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_1746_, 0, v_typeName_1742_);
lean_ctor_set(v___x_1746_, 1, v_idx_1743_);
lean_ctor_set(v___x_1746_, 2, v___x_1745_);
v___x_1747_ = lean_unsigned_to_nat(1u);
v___x_1748_ = lean_mk_empty_array_with_capacity(v___x_1747_);
v___x_1749_ = lean_array_push(v___x_1748_, v_struct_1744_);
v___x_1750_ = lean_mk_empty_array_with_capacity(v___x_1745_);
lean_dec(v___x_1745_);
v___x_1751_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1607_, v___x_1750_);
v___x_1752_ = l_Array_append___redArg(v___x_1749_, v___x_1751_);
lean_dec_ref(v___x_1751_);
v___x_1753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1746_);
lean_ctor_set(v___x_1753_, 1, v___x_1752_);
v___x_1754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1753_);
return v___x_1754_;
}
default: 
{
lean_object* v___x_1755_; lean_object* v___x_1756_; 
lean_dec_ref(v___x_1626_);
lean_del_object(v___x_1609_);
lean_dec(v_a_1607_);
v___x_1755_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
v___x_1756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1755_);
return v___x_1756_;
}
}
}
}
}
else
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1777_; 
v_a_1770_ = lean_ctor_get(v___x_1606_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1772_ = v___x_1606_;
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1606_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1775_; 
if (v_isShared_1773_ == 0)
{
v___x_1775_ = v___x_1772_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_a_1770_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
v___jp_1593_:
{
uint8_t v___x_1596_; 
v___x_1596_ = l_Lean_Expr_hasLooseBVars(v_b_1595_);
if (v___x_1596_ == 0)
{
lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; 
v___x_1597_ = lean_box(5);
v___x_1598_ = lean_unsigned_to_nat(2u);
v___x_1599_ = lean_mk_empty_array_with_capacity(v___x_1598_);
v___x_1600_ = lean_array_push(v___x_1599_, v___y_1594_);
v___x_1601_ = lean_array_push(v___x_1600_, v_b_1595_);
v___x_1602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1602_, 0, v___x_1597_);
lean_ctor_set(v___x_1602_, 1, v___x_1601_);
v___x_1603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1602_);
return v___x_1603_;
}
else
{
lean_object* v___x_1604_; lean_object* v___x_1605_; 
lean_dec_ref(v_b_1595_);
lean_dec_ref(v___y_1594_);
v___x_1604_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
v___x_1605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1604_);
return v___x_1605_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___boxed(lean_object* v_e_1778_, lean_object* v_isMatch_1779_, lean_object* v_root_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_){
_start:
{
uint8_t v_isMatch_boxed_1786_; uint8_t v_root_boxed_1787_; lean_object* v_res_1788_; 
v_isMatch_boxed_1786_ = lean_unbox(v_isMatch_1779_);
v_root_boxed_1787_ = lean_unbox(v_root_1780_);
v_res_1788_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_1778_, v_isMatch_boxed_1786_, v_root_boxed_1787_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_);
lean_dec(v_a_1784_);
lean_dec_ref(v_a_1783_);
lean_dec(v_a_1782_);
lean_dec_ref(v_a_1781_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0(lean_object* v_declName_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_){
_start:
{
lean_object* v___x_1795_; 
v___x_1795_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(v_declName_1789_, v___y_1793_);
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___boxed(lean_object* v_declName_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_){
_start:
{
lean_object* v_res_1802_; 
v_res_1802_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0(v_declName_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_);
lean_dec(v___y_1800_);
lean_dec_ref(v___y_1799_);
lean_dec(v___y_1798_);
lean_dec_ref(v___y_1797_);
return v_res_1802_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1(lean_object* v_inst_1803_, lean_object* v_R_1804_, lean_object* v_a_1805_, lean_object* v_b_1806_, lean_object* v_c_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_){
_start:
{
lean_object* v___x_1813_; 
v___x_1813_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(v_a_1805_, v_b_1806_);
return v___x_1813_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___boxed(lean_object* v_inst_1814_, lean_object* v_R_1815_, lean_object* v_a_1816_, lean_object* v_b_1817_, lean_object* v_c_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_){
_start:
{
lean_object* v_res_1824_; 
v_res_1824_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1(v_inst_1814_, v_R_1815_, v_a_1816_, v_b_1817_, v_c_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
lean_dec(v___y_1820_);
lean_dec_ref(v___y_1819_);
return v_res_1824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getMatchKeyArgs(lean_object* v_e_1825_, uint8_t v_root_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_){
_start:
{
uint8_t v___x_1832_; lean_object* v___x_1833_; 
v___x_1832_ = 1;
v___x_1833_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_1825_, v___x_1832_, v_root_1826_, v_a_1827_, v_a_1828_, v_a_1829_, v_a_1830_);
return v___x_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getMatchKeyArgs___boxed(lean_object* v_e_1834_, lean_object* v_root_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_){
_start:
{
uint8_t v_root_boxed_1841_; lean_object* v_res_1842_; 
v_root_boxed_1841_ = lean_unbox(v_root_1835_);
v_res_1842_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getMatchKeyArgs(v_e_1834_, v_root_boxed_1841_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
lean_dec(v_a_1839_);
lean_dec_ref(v_a_1838_);
lean_dec(v_a_1837_);
lean_dec_ref(v_a_1836_);
return v_res_1842_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__1(void){
_start:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1845_ = lean_box(0);
v___x_1846_ = lean_unsigned_to_nat(16u);
v___x_1847_ = lean_mk_array(v___x_1846_, v___x_1845_);
return v___x_1847_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2(void){
_start:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1848_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__1);
v___x_1849_ = lean_unsigned_to_nat(0u);
v___x_1850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1849_);
lean_ctor_set(v___x_1850_, 1, v___x_1848_);
return v___x_1850_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__4(void){
_start:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1853_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__3));
v___x_1854_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2);
v___x_1855_ = lean_unsigned_to_nat(0u);
v___x_1856_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__0));
v___x_1857_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1856_);
lean_ctor_set(v___x_1857_, 1, v___x_1855_);
lean_ctor_set(v___x_1857_, 2, v___x_1854_);
lean_ctor_set(v___x_1857_, 3, v___x_1853_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg(){
_start:
{
lean_object* v___x_1859_; 
v___x_1859_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__4);
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___boxed(lean_object* v___dummy_1860_){
_start:
{
lean_object* v_res_1861_; 
v_res_1861_ = l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg();
return v_res_1861_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0(void){
_start:
{
lean_object* v___x_1862_; 
v___x_1862_ = l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg();
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default(lean_object* v_00_u03b1_1863_){
_start:
{
lean_object* v___x_1864_; 
v___x_1864_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___redArg(){
_start:
{
lean_object* v___x_1866_; 
v___x_1866_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___redArg___boxed(lean_object* v___dummy_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___redArg();
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie(lean_object* v_a_1869_){
_start:
{
lean_object* v___x_1870_; 
v___x_1870_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0);
return v___x_1870_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__1(void){
_start:
{
lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1873_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2);
v___x_1874_ = lean_unsigned_to_nat(0u);
v___x_1875_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___x_1876_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1875_);
lean_ctor_set(v___x_1876_, 1, v___x_1874_);
lean_ctor_set(v___x_1876_, 2, v___x_1873_);
lean_ctor_set(v___x_1876_, 3, v___x_1875_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg(){
_start:
{
lean_object* v___x_1878_; 
v___x_1878_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__1);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___boxed(lean_object* v___dummy_1879_){
_start:
{
lean_object* v_res_1880_; 
v_res_1880_ = l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg();
return v_res_1880_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0(void){
_start:
{
lean_object* v___x_1881_; 
v___x_1881_ = l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg();
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie(lean_object* v_00_u03b1_1882_){
_start:
{
lean_object* v___x_1883_; 
v___x_1883_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0, &l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Trie_pushPending___redArg(lean_object* v_x_1884_, lean_object* v_x_1885_){
_start:
{
lean_object* v_values_1886_; lean_object* v_star_1887_; lean_object* v_children_1888_; lean_object* v_pending_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1897_; 
v_values_1886_ = lean_ctor_get(v_x_1884_, 0);
v_star_1887_ = lean_ctor_get(v_x_1884_, 1);
v_children_1888_ = lean_ctor_get(v_x_1884_, 2);
v_pending_1889_ = lean_ctor_get(v_x_1884_, 3);
v_isSharedCheck_1897_ = !lean_is_exclusive(v_x_1884_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1891_ = v_x_1884_;
v_isShared_1892_ = v_isSharedCheck_1897_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_pending_1889_);
lean_inc(v_children_1888_);
lean_inc(v_star_1887_);
lean_inc(v_values_1886_);
lean_dec(v_x_1884_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1897_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1893_; lean_object* v___x_1895_; 
v___x_1893_ = lean_array_push(v_pending_1889_, v_x_1885_);
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 3, v___x_1893_);
v___x_1895_ = v___x_1891_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_values_1886_);
lean_ctor_set(v_reuseFailAlloc_1896_, 1, v_star_1887_);
lean_ctor_set(v_reuseFailAlloc_1896_, 2, v_children_1888_);
lean_ctor_set(v_reuseFailAlloc_1896_, 3, v___x_1893_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Trie_pushPending(lean_object* v_00_u03b1_1898_, lean_object* v_x_1899_, lean_object* v_x_1900_){
_start:
{
lean_object* v___x_1901_; 
v___x_1901_ = l_Lean_Meta_LazyDiscrTree_Trie_pushPending___redArg(v_x_1899_, v_x_1900_);
return v___x_1901_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__0(void){
_start:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1902_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0);
v___x_1903_ = lean_unsigned_to_nat(1u);
v___x_1904_ = lean_mk_empty_array_with_capacity(v___x_1903_);
v___x_1905_ = lean_array_push(v___x_1904_, v___x_1902_);
return v___x_1905_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__1(void){
_start:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1906_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2);
v___x_1907_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__0);
v___x_1908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1907_);
lean_ctor_set(v___x_1908_, 1, v___x_1906_);
return v___x_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabited___redArg(){
_start:
{
lean_object* v___x_1910_; 
v___x_1910_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__1);
return v___x_1910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___boxed(lean_object* v___dummy_1911_){
_start:
{
lean_object* v_res_1912_; 
v_res_1912_ = l_Lean_Meta_LazyDiscrTree_instInhabited___redArg();
return v_res_1912_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_1913_; 
v___x_1913_ = l_Lean_Meta_LazyDiscrTree_instInhabited___redArg();
return v___x_1913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabited(lean_object* v_00_u03b1_1914_){
_start:
{
lean_object* v___x_1915_; 
v___x_1915_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0);
return v___x_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(lean_object* v_msgData_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_){
_start:
{
lean_object* v___x_1922_; lean_object* v_env_1923_; uint8_t v___x_1924_; lean_object* v_env_1925_; lean_object* v___x_1926_; lean_object* v_toCold_1927_; lean_object* v_mctx_1928_; lean_object* v_lctx_1929_; lean_object* v_options_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; 
v___x_1922_ = lean_st_ref_get(v___y_1920_);
v_env_1923_ = lean_ctor_get(v___x_1922_, 0);
lean_inc_ref(v_env_1923_);
lean_dec(v___x_1922_);
v___x_1924_ = 0;
v_env_1925_ = l_Lean_Environment_setRecordingDeps(v_env_1923_, v___x_1924_);
v___x_1926_ = lean_st_ref_get(v___y_1918_);
v_toCold_1927_ = lean_ctor_get(v___y_1919_, 0);
v_mctx_1928_ = lean_ctor_get(v___x_1926_, 0);
lean_inc_ref(v_mctx_1928_);
lean_dec(v___x_1926_);
v_lctx_1929_ = lean_ctor_get(v___y_1917_, 2);
v_options_1930_ = lean_ctor_get(v_toCold_1927_, 2);
lean_inc_ref(v_options_1930_);
lean_inc_ref(v_lctx_1929_);
v___x_1931_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1931_, 0, v_env_1925_);
lean_ctor_set(v___x_1931_, 1, v_mctx_1928_);
lean_ctor_set(v___x_1931_, 2, v_lctx_1929_);
lean_ctor_set(v___x_1931_, 3, v_options_1930_);
v___x_1932_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1931_);
lean_ctor_set(v___x_1932_, 1, v_msgData_1916_);
v___x_1933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1932_);
return v___x_1933_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0___boxed(lean_object* v_msgData_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_){
_start:
{
lean_object* v_res_1940_; 
v_res_1940_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(v_msgData_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
lean_dec(v___y_1938_);
lean_dec_ref(v___y_1937_);
lean_dec(v___y_1936_);
lean_dec_ref(v___y_1935_);
return v_res_1940_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(lean_object* v_msg_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_){
_start:
{
lean_object* v_ref_1947_; lean_object* v___x_1948_; lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1957_; 
v_ref_1947_ = lean_ctor_get(v___y_1944_, 2);
v___x_1948_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(v_msg_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_);
v_a_1949_ = lean_ctor_get(v___x_1948_, 0);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1948_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1951_ = v___x_1948_;
v_isShared_1952_ = v_isSharedCheck_1957_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___x_1948_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1957_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1953_; lean_object* v___x_1955_; 
lean_inc(v_ref_1947_);
v___x_1953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1953_, 0, v_ref_1947_);
lean_ctor_set(v___x_1953_, 1, v_a_1949_);
if (v_isShared_1952_ == 0)
{
lean_ctor_set_tag(v___x_1951_, 1);
lean_ctor_set(v___x_1951_, 0, v___x_1953_);
v___x_1955_ = v___x_1951_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v___x_1953_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg___boxed(lean_object* v_msg_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
lean_object* v_res_1964_; 
v_res_1964_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(v_msg_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
return v_res_1964_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1(void){
_start:
{
lean_object* v___x_1966_; lean_object* v___x_1967_; 
v___x_1966_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_pushArgs___closed__0));
v___x_1967_ = l_Lean_stringToMessageData(v___x_1966_);
return v___x_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushArgs(uint8_t v_root_1968_, lean_object* v_todo_1969_, lean_object* v_e_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_){
_start:
{
lean_object* v_v_1977_; uint8_t v___x_1981_; 
v___x_1981_ = l_Lean_Meta_DiscrTree_hasNoindexAnnotation(v_e_1970_);
if (v___x_1981_ == 0)
{
lean_object* v___x_1982_; 
v___x_1982_ = l_Lean_Meta_DiscrTree_reduceDT(v_e_1970_, v_root_1968_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_);
if (lean_obj_tag(v___x_1982_) == 0)
{
lean_object* v_a_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_2125_; 
v_a_1983_ = lean_ctor_get(v___x_1982_, 0);
v_isSharedCheck_2125_ = !lean_is_exclusive(v___x_1982_);
if (v_isSharedCheck_2125_ == 0)
{
v___x_1985_ = v___x_1982_;
v_isShared_1986_ = v_isSharedCheck_2125_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_a_1983_);
lean_dec(v___x_1982_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_2125_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1987_; lean_object* v_k_1989_; lean_object* v_nargs_1990_; lean_object* v_todo_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; 
v___x_1987_ = l_Lean_Expr_getAppFn(v_a_1983_);
switch(lean_obj_tag(v___x_1987_))
{
case 9:
{
lean_object* v_a_2034_; 
lean_del_object(v___x_1985_);
lean_dec(v_a_1983_);
v_a_2034_ = lean_ctor_get(v___x_1987_, 0);
lean_inc_ref(v_a_2034_);
lean_dec_ref_known(v___x_1987_, 1);
v_v_1977_ = v_a_2034_;
goto v___jp_1976_;
}
case 4:
{
lean_object* v_declName_2035_; lean_object* v___y_2037_; lean_object* v___y_2038_; lean_object* v___y_2039_; lean_object* v___y_2040_; 
lean_del_object(v___x_1985_);
v_declName_2035_ = lean_ctor_get(v___x_1987_, 0);
if (v_root_1968_ == 0)
{
lean_object* v___x_2043_; 
lean_inc(v_a_1983_);
v___x_2043_ = l_Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f(v_a_1983_);
if (lean_obj_tag(v___x_2043_) == 1)
{
lean_object* v_val_2044_; 
lean_dec_ref_known(v___x_1987_, 2);
lean_dec(v_a_1983_);
v_val_2044_ = lean_ctor_get(v___x_2043_, 0);
lean_inc(v_val_2044_);
lean_dec_ref_known(v___x_2043_, 1);
v_v_1977_ = v_val_2044_;
goto v___jp_1976_;
}
else
{
lean_object* v___x_2045_; 
lean_dec(v___x_2043_);
v___x_2045_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset(v_declName_2035_, v_a_1983_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_);
if (lean_obj_tag(v___x_2045_) == 0)
{
lean_object* v_a_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2056_; 
v_a_2046_ = lean_ctor_get(v___x_2045_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2048_ = v___x_2045_;
v_isShared_2049_ = v_isSharedCheck_2056_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_a_2046_);
lean_dec(v___x_2045_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2056_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
uint8_t v___x_2050_; 
v___x_2050_ = lean_unbox(v_a_2046_);
lean_dec(v_a_2046_);
if (v___x_2050_ == 0)
{
lean_del_object(v___x_2048_);
v___y_2037_ = v_a_1971_;
v___y_2038_ = v_a_1972_;
v___y_2039_ = v_a_1973_;
v___y_2040_ = v_a_1974_;
goto v___jp_2036_;
}
else
{
lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2054_; 
lean_dec_ref_known(v___x_1987_, 2);
lean_dec(v_a_1983_);
v___x_2051_ = lean_box(3);
v___x_2052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2052_, 0, v___x_2051_);
lean_ctor_set(v___x_2052_, 1, v_todo_1969_);
if (v_isShared_2049_ == 0)
{
lean_ctor_set(v___x_2048_, 0, v___x_2052_);
v___x_2054_ = v___x_2048_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v___x_2052_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
}
else
{
lean_object* v_a_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2064_; 
lean_dec_ref_known(v___x_1987_, 2);
lean_dec(v_a_1983_);
lean_dec_ref(v_todo_1969_);
v_a_2057_ = lean_ctor_get(v___x_2045_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2059_ = v___x_2045_;
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___x_2045_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2062_; 
if (v_isShared_2060_ == 0)
{
v___x_2062_ = v___x_2059_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_a_2057_);
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
}
else
{
v___y_2037_ = v_a_1971_;
v___y_2038_ = v_a_1972_;
v___y_2039_ = v_a_1973_;
v___y_2040_ = v_a_1974_;
goto v___jp_2036_;
}
v___jp_2036_:
{
lean_object* v___x_2041_; lean_object* v___x_2042_; 
v___x_2041_ = l_Lean_Expr_getAppNumArgs(v_a_1983_);
lean_inc(v___x_2041_);
lean_inc(v_declName_2035_);
v___x_2042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2042_, 0, v_declName_2035_);
lean_ctor_set(v___x_2042_, 1, v___x_2041_);
v_k_1989_ = v___x_2042_;
v_nargs_1990_ = v___x_2041_;
v_todo_1991_ = v_todo_1969_;
v___y_1992_ = v___y_2037_;
v___y_1993_ = v___y_2038_;
v___y_1994_ = v___y_2039_;
v___y_1995_ = v___y_2040_;
goto v___jp_1988_;
}
}
case 11:
{
lean_object* v_typeName_2065_; lean_object* v_idx_2066_; lean_object* v_struct_2067_; lean_object* v___x_2068_; lean_object* v___y_2070_; lean_object* v_env_2074_; uint8_t v___x_2075_; 
lean_del_object(v___x_1985_);
v_typeName_2065_ = lean_ctor_get(v___x_1987_, 0);
v_idx_2066_ = lean_ctor_get(v___x_1987_, 1);
v_struct_2067_ = lean_ctor_get(v___x_1987_, 2);
v___x_2068_ = lean_st_ref_get(v_a_1974_);
v_env_2074_ = lean_ctor_get(v___x_2068_, 0);
lean_inc_ref(v_env_2074_);
lean_dec(v___x_2068_);
v___x_2075_ = l_Lean_isClass(v_env_2074_, v_typeName_2065_);
if (v___x_2075_ == 0)
{
lean_inc_ref(v_struct_2067_);
v___y_2070_ = v_struct_2067_;
goto v___jp_2069_;
}
else
{
lean_object* v___x_2076_; 
lean_inc_ref(v_struct_2067_);
v___x_2076_ = l_Lean_Meta_DiscrTree_mkNoindexAnnotation(v_struct_2067_);
v___y_2070_ = v___x_2076_;
goto v___jp_2069_;
}
v___jp_2069_:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; 
v___x_2071_ = l_Lean_Expr_getAppNumArgs(v_a_1983_);
lean_inc(v___x_2071_);
lean_inc(v_idx_2066_);
lean_inc(v_typeName_2065_);
v___x_2072_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_2072_, 0, v_typeName_2065_);
lean_ctor_set(v___x_2072_, 1, v_idx_2066_);
lean_ctor_set(v___x_2072_, 2, v___x_2071_);
v___x_2073_ = lean_array_push(v_todo_1969_, v___y_2070_);
v_k_1989_ = v___x_2072_;
v_nargs_1990_ = v___x_2071_;
v_todo_1991_ = v___x_2073_;
v___y_1992_ = v_a_1971_;
v___y_1993_ = v_a_1972_;
v___y_1994_ = v_a_1973_;
v___y_1995_ = v_a_1974_;
goto v___jp_1988_;
}
}
case 1:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2080_; 
lean_dec_ref_known(v___x_1987_, 1);
lean_dec(v_a_1983_);
v___x_2077_ = lean_box(3);
v___x_2078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2077_);
lean_ctor_set(v___x_2078_, 1, v_todo_1969_);
if (v_isShared_1986_ == 0)
{
lean_ctor_set(v___x_1985_, 0, v___x_2078_);
v___x_2080_ = v___x_1985_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v___x_2078_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
case 2:
{
lean_object* v_mvarId_2082_; lean_object* v___x_2083_; uint8_t v___x_2084_; 
lean_dec(v_a_1983_);
v_mvarId_2082_ = lean_ctor_get(v___x_1987_, 0);
lean_inc(v_mvarId_2082_);
lean_dec_ref_known(v___x_1987_, 1);
v___x_2083_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_tmpMVarId));
v___x_2084_ = l_Lean_instBEqMVarId_beq(v_mvarId_2082_, v___x_2083_);
lean_dec(v_mvarId_2082_);
if (v___x_2084_ == 0)
{
lean_object* v___x_2085_; lean_object* v___x_2086_; 
lean_del_object(v___x_1985_);
lean_dec_ref(v_todo_1969_);
v___x_2085_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1, &l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1);
v___x_2086_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(v___x_2085_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_);
return v___x_2086_;
}
else
{
lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2090_; 
v___x_2087_ = lean_box(3);
v___x_2088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2087_);
lean_ctor_set(v___x_2088_, 1, v_todo_1969_);
if (v_isShared_1986_ == 0)
{
lean_ctor_set(v___x_1985_, 0, v___x_2088_);
v___x_2090_ = v___x_1985_;
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
}
case 7:
{
lean_object* v_binderType_2092_; lean_object* v_body_2093_; lean_object* v_b_2095_; uint8_t v___x_2109_; 
lean_dec(v_a_1983_);
v_binderType_2092_ = lean_ctor_get(v___x_1987_, 1);
lean_inc_ref(v_binderType_2092_);
v_body_2093_ = lean_ctor_get(v___x_1987_, 2);
lean_inc_ref(v_body_2093_);
lean_dec_ref_known(v___x_1987_, 3);
v___x_2109_ = l_Lean_Expr_hasLooseBVars(v_body_2093_);
if (v___x_2109_ == 0)
{
v_b_2095_ = v_body_2093_;
goto v___jp_2094_;
}
else
{
lean_object* v___x_2110_; 
v___x_2110_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(v_body_2093_, v_a_1973_, v_a_1974_);
if (lean_obj_tag(v___x_2110_) == 0)
{
lean_object* v_a_2111_; 
v_a_2111_ = lean_ctor_get(v___x_2110_, 0);
lean_inc(v_a_2111_);
lean_dec_ref_known(v___x_2110_, 1);
v_b_2095_ = v_a_2111_;
goto v___jp_2094_;
}
else
{
lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2119_; 
lean_dec_ref(v_binderType_2092_);
lean_del_object(v___x_1985_);
lean_dec_ref(v_todo_1969_);
v_a_2112_ = lean_ctor_get(v___x_2110_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2110_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2114_ = v___x_2110_;
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_dec(v___x_2110_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2117_; 
if (v_isShared_2115_ == 0)
{
v___x_2117_ = v___x_2114_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_a_2112_);
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
v___jp_2094_:
{
uint8_t v___x_2096_; 
v___x_2096_ = l_Lean_Expr_hasLooseBVars(v_b_2095_);
if (v___x_2096_ == 0)
{
lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2102_; 
v___x_2097_ = lean_box(5);
v___x_2098_ = lean_array_push(v_todo_1969_, v_binderType_2092_);
v___x_2099_ = lean_array_push(v___x_2098_, v_b_2095_);
v___x_2100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2100_, 0, v___x_2097_);
lean_ctor_set(v___x_2100_, 1, v___x_2099_);
if (v_isShared_1986_ == 0)
{
lean_ctor_set(v___x_1985_, 0, v___x_2100_);
v___x_2102_ = v___x_1985_;
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
else
{
lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2107_; 
lean_dec_ref(v_b_2095_);
lean_dec_ref(v_binderType_2092_);
v___x_2104_ = lean_box(4);
v___x_2105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2105_, 0, v___x_2104_);
lean_ctor_set(v___x_2105_, 1, v_todo_1969_);
if (v_isShared_1986_ == 0)
{
lean_ctor_set(v___x_1985_, 0, v___x_2105_);
v___x_2107_ = v___x_1985_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v___x_2105_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
}
}
default: 
{
lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2123_; 
lean_dec_ref(v___x_1987_);
lean_dec(v_a_1983_);
v___x_2120_ = lean_box(4);
v___x_2121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2120_);
lean_ctor_set(v___x_2121_, 1, v_todo_1969_);
if (v_isShared_1986_ == 0)
{
lean_ctor_set(v___x_1985_, 0, v___x_2121_);
v___x_2123_ = v___x_1985_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v___x_2121_);
v___x_2123_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
return v___x_2123_;
}
}
}
v___jp_1988_:
{
lean_object* v___x_1996_; 
lean_inc(v_nargs_1990_);
v___x_1996_ = l_Lean_Meta_getFunInfoNArgs(v___x_1987_, v_nargs_1990_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_object* v_a_1997_; lean_object* v_paramInfo_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2024_; 
v_a_1997_ = lean_ctor_get(v___x_1996_, 0);
lean_inc(v_a_1997_);
lean_dec_ref_known(v___x_1996_, 1);
v_paramInfo_1998_ = lean_ctor_get(v_a_1997_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v_a_1997_);
if (v_isSharedCheck_2024_ == 0)
{
lean_object* v_unused_2025_; 
v_unused_2025_ = lean_ctor_get(v_a_1997_, 1);
lean_dec(v_unused_2025_);
v___x_2000_ = v_a_1997_;
v_isShared_2001_ = v_isSharedCheck_2024_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_paramInfo_1998_);
lean_dec(v_a_1997_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2024_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; 
v___x_2002_ = lean_unsigned_to_nat(1u);
v___x_2003_ = lean_nat_sub(v_nargs_1990_, v___x_2002_);
lean_dec(v_nargs_1990_);
v___x_2004_ = l_Lean_Meta_LazyDiscrTree_MatchClone_pushArgsAux(v_paramInfo_1998_, v___x_2003_, v_a_1983_, v_todo_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
lean_dec_ref(v_paramInfo_1998_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v_a_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2015_; 
v_a_2005_ = lean_ctor_get(v___x_2004_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2007_ = v___x_2004_;
v_isShared_2008_ = v_isSharedCheck_2015_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_a_2005_);
lean_dec(v___x_2004_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2015_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2010_; 
if (v_isShared_2001_ == 0)
{
lean_ctor_set(v___x_2000_, 1, v_a_2005_);
lean_ctor_set(v___x_2000_, 0, v_k_1989_);
v___x_2010_ = v___x_2000_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_k_1989_);
lean_ctor_set(v_reuseFailAlloc_2014_, 1, v_a_2005_);
v___x_2010_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
lean_object* v___x_2012_; 
if (v_isShared_2008_ == 0)
{
lean_ctor_set(v___x_2007_, 0, v___x_2010_);
v___x_2012_ = v___x_2007_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v___x_2010_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
}
}
else
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2023_; 
lean_del_object(v___x_2000_);
lean_dec(v_k_1989_);
v_a_2016_ = lean_ctor_get(v___x_2004_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2018_ = v___x_2004_;
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___x_2004_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2021_; 
if (v_isShared_2019_ == 0)
{
v___x_2021_ = v___x_2018_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_a_2016_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
}
}
}
else
{
lean_object* v_a_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2033_; 
lean_dec_ref(v_todo_1991_);
lean_dec(v_nargs_1990_);
lean_dec(v_k_1989_);
lean_dec(v_a_1983_);
v_a_2026_ = lean_ctor_get(v___x_1996_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v___x_1996_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2028_ = v___x_1996_;
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_a_2026_);
lean_dec(v___x_1996_);
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
}
else
{
lean_object* v_a_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2133_; 
lean_dec_ref(v_todo_1969_);
v_a_2126_ = lean_ctor_get(v___x_1982_, 0);
v_isSharedCheck_2133_ = !lean_is_exclusive(v___x_1982_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2128_ = v___x_1982_;
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_a_2126_);
lean_dec(v___x_1982_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2131_; 
if (v_isShared_2129_ == 0)
{
v___x_2131_ = v___x_2128_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_a_2126_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
}
}
else
{
lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; 
lean_dec_ref(v_e_1970_);
v___x_2134_ = lean_box(3);
v___x_2135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2135_, 0, v___x_2134_);
lean_ctor_set(v___x_2135_, 1, v_todo_1969_);
v___x_2136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2136_, 0, v___x_2135_);
return v___x_2136_;
}
v___jp_1976_:
{
lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___x_1978_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1978_, 0, v_v_1977_);
v___x_1979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1979_, 0, v___x_1978_);
lean_ctor_set(v___x_1979_, 1, v_todo_1969_);
v___x_1980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1980_, 0, v___x_1979_);
return v___x_1980_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushArgs___boxed(lean_object* v_root_2137_, lean_object* v_todo_2138_, lean_object* v_e_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_){
_start:
{
uint8_t v_root_boxed_2145_; lean_object* v_res_2146_; 
v_root_boxed_2145_ = lean_unbox(v_root_2137_);
v_res_2146_ = l_Lean_Meta_LazyDiscrTree_pushArgs(v_root_boxed_2145_, v_todo_2138_, v_e_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_);
lean_dec(v_a_2143_);
lean_dec_ref(v_a_2142_);
lean_dec(v_a_2141_);
lean_dec_ref(v_a_2140_);
return v_res_2146_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0(lean_object* v_00_u03b1_2147_, lean_object* v_msg_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
lean_object* v___x_2154_; 
v___x_2154_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(v_msg_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
return v___x_2154_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___boxed(lean_object* v_00_u03b1_2155_, lean_object* v_msg_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_){
_start:
{
lean_object* v_res_2162_; 
v_res_2162_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0(v_00_u03b1_2155_, v_msg_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
return v_res_2162_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_initCapacity(void){
_start:
{
lean_object* v___x_2163_; 
v___x_2163_ = lean_unsigned_to_nat(8u);
return v___x_2163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_rootKey(lean_object* v_e_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_){
_start:
{
uint8_t v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; 
v___x_2170_ = 1;
v___x_2171_ = lean_unsigned_to_nat(8u);
v___x_2172_ = lean_mk_empty_array_with_capacity(v___x_2171_);
v___x_2173_ = l_Lean_Meta_LazyDiscrTree_pushArgs(v___x_2170_, v___x_2172_, v_e_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_);
return v___x_2173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_rootKey___boxed(lean_object* v_e_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_){
_start:
{
lean_object* v_res_2180_; 
v_res_2180_ = l_Lean_Meta_LazyDiscrTree_rootKey(v_e_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_);
lean_dec(v_a_2178_);
lean_dec_ref(v_a_2177_);
lean_dec(v_a_2176_);
lean_dec_ref(v_a_2175_);
return v_res_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_buildPath(lean_object* v_op_2181_, uint8_t v_root_2182_, lean_object* v_todo_2183_, lean_object* v_keys_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_){
_start:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; uint8_t v___x_2192_; 
v___x_2190_ = lean_array_get_size(v_todo_2183_);
v___x_2191_ = lean_unsigned_to_nat(0u);
v___x_2192_ = lean_nat_dec_eq(v___x_2190_, v___x_2191_);
if (v___x_2192_ == 0)
{
lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v_e_2196_; lean_object* v_todo_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2193_ = l_Lean_instInhabitedExpr;
v___x_2194_ = lean_unsigned_to_nat(1u);
v___x_2195_ = lean_nat_sub(v___x_2190_, v___x_2194_);
v_e_2196_ = lean_array_get(v___x_2193_, v_todo_2183_, v___x_2195_);
lean_dec(v___x_2195_);
v_todo_2197_ = lean_array_pop(v_todo_2183_);
v___x_2198_ = lean_box(v_root_2182_);
lean_inc_ref(v_op_2181_);
lean_inc(v_a_2188_);
lean_inc_ref(v_a_2187_);
lean_inc(v_a_2186_);
lean_inc_ref(v_a_2185_);
v___x_2199_ = lean_apply_8(v_op_2181_, v___x_2198_, v_todo_2197_, v_e_2196_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, lean_box(0));
if (lean_obj_tag(v___x_2199_) == 0)
{
lean_object* v_a_2200_; lean_object* v_fst_2201_; lean_object* v_snd_2202_; lean_object* v___x_2203_; 
v_a_2200_ = lean_ctor_get(v___x_2199_, 0);
lean_inc(v_a_2200_);
lean_dec_ref_known(v___x_2199_, 1);
v_fst_2201_ = lean_ctor_get(v_a_2200_, 0);
lean_inc(v_fst_2201_);
v_snd_2202_ = lean_ctor_get(v_a_2200_, 1);
lean_inc(v_snd_2202_);
lean_dec(v_a_2200_);
v___x_2203_ = lean_array_push(v_keys_2184_, v_fst_2201_);
v_root_2182_ = v___x_2192_;
v_todo_2183_ = v_snd_2202_;
v_keys_2184_ = v___x_2203_;
goto _start;
}
else
{
lean_object* v_a_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2212_; 
lean_dec_ref(v_keys_2184_);
lean_dec_ref(v_op_2181_);
v_a_2205_ = lean_ctor_get(v___x_2199_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2207_ = v___x_2199_;
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_a_2205_);
lean_dec(v___x_2199_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2210_; 
if (v_isShared_2208_ == 0)
{
v___x_2210_ = v___x_2207_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_a_2205_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
}
else
{
lean_object* v___x_2213_; 
lean_dec_ref(v_todo_2183_);
lean_dec_ref(v_op_2181_);
v___x_2213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2213_, 0, v_keys_2184_);
return v___x_2213_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_buildPath___boxed(lean_object* v_op_2214_, lean_object* v_root_2215_, lean_object* v_todo_2216_, lean_object* v_keys_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_){
_start:
{
uint8_t v_root_boxed_2223_; lean_object* v_res_2224_; 
v_root_boxed_2223_ = lean_unbox(v_root_2215_);
v_res_2224_ = l_Lean_Meta_LazyDiscrTree_buildPath(v_op_2214_, v_root_boxed_2223_, v_todo_2216_, v_keys_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
lean_dec(v_a_2221_);
lean_dec_ref(v_a_2220_);
lean_dec(v_a_2219_);
lean_dec_ref(v_a_2218_);
return v_res_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_patternPath(lean_object* v_e_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_){
_start:
{
lean_object* v_op_2232_; lean_object* v___x_2233_; lean_object* v_todo_2234_; uint8_t v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; 
v_op_2232_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_patternPath___closed__0));
v___x_2233_ = lean_unsigned_to_nat(8u);
v_todo_2234_ = lean_mk_empty_array_with_capacity(v___x_2233_);
v___x_2235_ = 1;
lean_inc_ref(v_todo_2234_);
v___x_2236_ = lean_array_push(v_todo_2234_, v_e_2226_);
v___x_2237_ = l_Lean_Meta_LazyDiscrTree_buildPath(v_op_2232_, v___x_2235_, v___x_2236_, v_todo_2234_, v_a_2227_, v_a_2228_, v_a_2229_, v_a_2230_);
return v___x_2237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_patternPath___boxed(lean_object* v_e_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_){
_start:
{
lean_object* v_res_2244_; 
v_res_2244_ = l_Lean_Meta_LazyDiscrTree_patternPath(v_e_2238_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_);
lean_dec(v_a_2242_);
lean_dec_ref(v_a_2241_);
lean_dec(v_a_2240_);
lean_dec_ref(v_a_2239_);
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath___lam__0(uint8_t v_root_2245_, lean_object* v_todo_2246_, lean_object* v_e_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_){
_start:
{
uint8_t v___x_2253_; lean_object* v___x_2254_; 
v___x_2253_ = 1;
v___x_2254_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_2247_, v___x_2253_, v_root_2245_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_);
if (lean_obj_tag(v___x_2254_) == 0)
{
lean_object* v_a_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2272_; 
v_a_2255_ = lean_ctor_get(v___x_2254_, 0);
v_isSharedCheck_2272_ = !lean_is_exclusive(v___x_2254_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2257_ = v___x_2254_;
v_isShared_2258_ = v_isSharedCheck_2272_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_a_2255_);
lean_dec(v___x_2254_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2272_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
lean_object* v_fst_2259_; lean_object* v_snd_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2271_; 
v_fst_2259_ = lean_ctor_get(v_a_2255_, 0);
v_snd_2260_ = lean_ctor_get(v_a_2255_, 1);
v_isSharedCheck_2271_ = !lean_is_exclusive(v_a_2255_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2262_ = v_a_2255_;
v_isShared_2263_ = v_isSharedCheck_2271_;
goto v_resetjp_2261_;
}
else
{
lean_inc(v_snd_2260_);
lean_inc(v_fst_2259_);
lean_dec(v_a_2255_);
v___x_2262_ = lean_box(0);
v_isShared_2263_ = v_isSharedCheck_2271_;
goto v_resetjp_2261_;
}
v_resetjp_2261_:
{
lean_object* v___x_2264_; lean_object* v___x_2266_; 
v___x_2264_ = l_Array_append___redArg(v_todo_2246_, v_snd_2260_);
lean_dec(v_snd_2260_);
if (v_isShared_2263_ == 0)
{
lean_ctor_set(v___x_2262_, 1, v___x_2264_);
v___x_2266_ = v___x_2262_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v_fst_2259_);
lean_ctor_set(v_reuseFailAlloc_2270_, 1, v___x_2264_);
v___x_2266_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
lean_object* v___x_2268_; 
if (v_isShared_2258_ == 0)
{
lean_ctor_set(v___x_2257_, 0, v___x_2266_);
v___x_2268_ = v___x_2257_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v___x_2266_);
v___x_2268_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
return v___x_2268_;
}
}
}
}
}
else
{
lean_dec_ref(v_todo_2246_);
return v___x_2254_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath___lam__0___boxed(lean_object* v_root_2273_, lean_object* v_todo_2274_, lean_object* v_e_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_){
_start:
{
uint8_t v_root_boxed_2281_; lean_object* v_res_2282_; 
v_root_boxed_2281_ = lean_unbox(v_root_2273_);
v_res_2282_ = l_Lean_Meta_LazyDiscrTree_targetPath___lam__0(v_root_boxed_2281_, v_todo_2274_, v_e_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
lean_dec(v___y_2277_);
lean_dec_ref(v___y_2276_);
return v_res_2282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath(lean_object* v_e_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_){
_start:
{
lean_object* v_op_2290_; lean_object* v___x_2291_; lean_object* v_todo_2292_; uint8_t v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; 
v_op_2290_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_targetPath___closed__0));
v___x_2291_ = lean_unsigned_to_nat(8u);
v_todo_2292_ = lean_mk_empty_array_with_capacity(v___x_2291_);
v___x_2293_ = 1;
lean_inc_ref(v_todo_2292_);
v___x_2294_ = lean_array_push(v_todo_2292_, v_e_2284_);
v___x_2295_ = l_Lean_Meta_LazyDiscrTree_buildPath(v_op_2290_, v___x_2293_, v___x_2294_, v_todo_2292_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_);
return v___x_2295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath___boxed(lean_object* v_e_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_){
_start:
{
lean_object* v_res_2302_; 
v_res_2302_ = l_Lean_Meta_LazyDiscrTree_targetPath(v_e_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
lean_dec(v_a_2300_);
lean_dec_ref(v_a_2299_);
lean_dec(v_a_2298_);
lean_dec_ref(v_a_2297_);
return v_res_2302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___redArg___lam__0(lean_object* v_tries_2303_, lean_object* v_m_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_){
_start:
{
lean_object* v___x_2310_; lean_object* v___x_2311_; 
v___x_2310_ = lean_st_mk_ref(v_tries_2303_);
lean_inc(v___x_2310_);
v___x_2311_ = lean_apply_6(v_m_2304_, v___x_2310_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, lean_box(0));
if (lean_obj_tag(v___x_2311_) == 0)
{
lean_object* v_a_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2321_; 
v_a_2312_ = lean_ctor_get(v___x_2311_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2311_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2314_ = v___x_2311_;
v_isShared_2315_ = v_isSharedCheck_2321_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_a_2312_);
lean_dec(v___x_2311_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2321_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2319_; 
v___x_2316_ = lean_st_ref_get(v___x_2310_);
lean_dec(v___x_2310_);
v___x_2317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2317_, 0, v_a_2312_);
lean_ctor_set(v___x_2317_, 1, v___x_2316_);
if (v_isShared_2315_ == 0)
{
lean_ctor_set(v___x_2314_, 0, v___x_2317_);
v___x_2319_ = v___x_2314_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v___x_2317_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
else
{
lean_object* v_a_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2329_; 
lean_dec(v___x_2310_);
v_a_2322_ = lean_ctor_get(v___x_2311_, 0);
v_isSharedCheck_2329_ = !lean_is_exclusive(v___x_2311_);
if (v_isSharedCheck_2329_ == 0)
{
v___x_2324_ = v___x_2311_;
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_a_2322_);
lean_dec(v___x_2311_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2327_; 
if (v_isShared_2325_ == 0)
{
v___x_2327_ = v___x_2324_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v_a_2322_);
v___x_2327_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
return v___x_2327_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___redArg___lam__0___boxed(lean_object* v_tries_2330_, lean_object* v_m_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_){
_start:
{
lean_object* v_res_2337_; 
v_res_2337_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg___lam__0(v_tries_2330_, v_m_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
return v_res_2337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___redArg(lean_object* v_d_2338_, lean_object* v_m_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_){
_start:
{
lean_object* v_tries_2345_; lean_object* v_roots_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2399_; 
v_tries_2345_ = lean_ctor_get(v_d_2338_, 0);
v_roots_2346_ = lean_ctor_get(v_d_2338_, 1);
v_isSharedCheck_2399_ = !lean_is_exclusive(v_d_2338_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2348_ = v_d_2338_;
v_isShared_2349_ = v_isSharedCheck_2399_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_roots_2346_);
lean_inc(v_tries_2345_);
lean_dec(v_d_2338_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2399_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v___y_2351_; lean_object* v___x_2380_; uint8_t v_transparency_2381_; uint8_t v___x_2382_; uint8_t v___x_2383_; 
v___x_2380_ = l_Lean_Meta_Context_config(v_a_2340_);
v_transparency_2381_ = lean_ctor_get_uint8(v___x_2380_, 9);
lean_dec_ref(v___x_2380_);
v___x_2382_ = 2;
v___x_2383_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2381_, v___x_2382_);
if (v___x_2383_ == 0)
{
lean_object* v_keyedConfig_2384_; uint8_t v_trackZetaDelta_2385_; lean_object* v_zetaDeltaSet_2386_; lean_object* v_lctx_2387_; lean_object* v_localInstances_2388_; lean_object* v_defEqCtx_x3f_2389_; lean_object* v_synthPendingDepth_2390_; lean_object* v_customCanUnfoldPredicate_x3f_2391_; uint8_t v_univApprox_2392_; uint8_t v_inTypeClassResolution_2393_; uint8_t v_cacheInferType_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
v_keyedConfig_2384_ = lean_ctor_get(v_a_2340_, 0);
v_trackZetaDelta_2385_ = lean_ctor_get_uint8(v_a_2340_, sizeof(void*)*7);
v_zetaDeltaSet_2386_ = lean_ctor_get(v_a_2340_, 1);
v_lctx_2387_ = lean_ctor_get(v_a_2340_, 2);
v_localInstances_2388_ = lean_ctor_get(v_a_2340_, 3);
v_defEqCtx_x3f_2389_ = lean_ctor_get(v_a_2340_, 4);
v_synthPendingDepth_2390_ = lean_ctor_get(v_a_2340_, 5);
v_customCanUnfoldPredicate_x3f_2391_ = lean_ctor_get(v_a_2340_, 6);
v_univApprox_2392_ = lean_ctor_get_uint8(v_a_2340_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2393_ = lean_ctor_get_uint8(v_a_2340_, sizeof(void*)*7 + 2);
v_cacheInferType_2394_ = lean_ctor_get_uint8(v_a_2340_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2384_);
v___x_2395_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2382_, v_keyedConfig_2384_);
lean_inc(v_customCanUnfoldPredicate_x3f_2391_);
lean_inc(v_synthPendingDepth_2390_);
lean_inc(v_defEqCtx_x3f_2389_);
lean_inc_ref(v_localInstances_2388_);
lean_inc_ref(v_lctx_2387_);
lean_inc(v_zetaDeltaSet_2386_);
v___x_2396_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2396_, 0, v___x_2395_);
lean_ctor_set(v___x_2396_, 1, v_zetaDeltaSet_2386_);
lean_ctor_set(v___x_2396_, 2, v_lctx_2387_);
lean_ctor_set(v___x_2396_, 3, v_localInstances_2388_);
lean_ctor_set(v___x_2396_, 4, v_defEqCtx_x3f_2389_);
lean_ctor_set(v___x_2396_, 5, v_synthPendingDepth_2390_);
lean_ctor_set(v___x_2396_, 6, v_customCanUnfoldPredicate_x3f_2391_);
lean_ctor_set_uint8(v___x_2396_, sizeof(void*)*7, v_trackZetaDelta_2385_);
lean_ctor_set_uint8(v___x_2396_, sizeof(void*)*7 + 1, v_univApprox_2392_);
lean_ctor_set_uint8(v___x_2396_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2393_);
lean_ctor_set_uint8(v___x_2396_, sizeof(void*)*7 + 3, v_cacheInferType_2394_);
lean_inc(v_a_2343_);
lean_inc_ref(v_a_2342_);
lean_inc(v_a_2341_);
v___x_2397_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg___lam__0(v_tries_2345_, v_m_2339_, v___x_2396_, v_a_2341_, v_a_2342_, v_a_2343_);
v___y_2351_ = v___x_2397_;
goto v___jp_2350_;
}
else
{
lean_object* v___x_2398_; 
lean_inc(v_a_2343_);
lean_inc_ref(v_a_2342_);
lean_inc(v_a_2341_);
lean_inc_ref(v_a_2340_);
v___x_2398_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg___lam__0(v_tries_2345_, v_m_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_);
v___y_2351_ = v___x_2398_;
goto v___jp_2350_;
}
v___jp_2350_:
{
if (lean_obj_tag(v___y_2351_) == 0)
{
lean_object* v_a_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2371_; 
v_a_2352_ = lean_ctor_get(v___y_2351_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___y_2351_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2354_ = v___y_2351_;
v_isShared_2355_ = v_isSharedCheck_2371_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_a_2352_);
lean_dec(v___y_2351_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2371_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v_fst_2356_; lean_object* v_snd_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2370_; 
v_fst_2356_ = lean_ctor_get(v_a_2352_, 0);
v_snd_2357_ = lean_ctor_get(v_a_2352_, 1);
v_isSharedCheck_2370_ = !lean_is_exclusive(v_a_2352_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2359_ = v_a_2352_;
v_isShared_2360_ = v_isSharedCheck_2370_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_snd_2357_);
lean_inc(v_fst_2356_);
lean_dec(v_a_2352_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2370_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___x_2362_; 
if (v_isShared_2349_ == 0)
{
lean_ctor_set(v___x_2348_, 0, v_snd_2357_);
v___x_2362_ = v___x_2348_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_snd_2357_);
lean_ctor_set(v_reuseFailAlloc_2369_, 1, v_roots_2346_);
v___x_2362_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
lean_object* v___x_2364_; 
if (v_isShared_2360_ == 0)
{
lean_ctor_set(v___x_2359_, 1, v___x_2362_);
v___x_2364_ = v___x_2359_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v_fst_2356_);
lean_ctor_set(v_reuseFailAlloc_2368_, 1, v___x_2362_);
v___x_2364_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
lean_object* v___x_2366_; 
if (v_isShared_2355_ == 0)
{
lean_ctor_set(v___x_2354_, 0, v___x_2364_);
v___x_2366_ = v___x_2354_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v___x_2364_);
v___x_2366_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
return v___x_2366_;
}
}
}
}
}
}
else
{
lean_object* v_a_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2379_; 
lean_del_object(v___x_2348_);
lean_dec_ref(v_roots_2346_);
v_a_2372_ = lean_ctor_get(v___y_2351_, 0);
v_isSharedCheck_2379_ = !lean_is_exclusive(v___y_2351_);
if (v_isSharedCheck_2379_ == 0)
{
v___x_2374_ = v___y_2351_;
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_a_2372_);
lean_dec(v___y_2351_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v___x_2377_; 
if (v_isShared_2375_ == 0)
{
v___x_2377_ = v___x_2374_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_a_2372_);
v___x_2377_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
return v___x_2377_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___redArg___boxed(lean_object* v_d_2400_, lean_object* v_m_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_){
_start:
{
lean_object* v_res_2407_; 
v_res_2407_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_d_2400_, v_m_2401_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_);
lean_dec(v_a_2405_);
lean_dec_ref(v_a_2404_);
lean_dec(v_a_2403_);
lean_dec_ref(v_a_2402_);
return v_res_2407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch(lean_object* v_00_u03b1_2408_, lean_object* v_00_u03b2_2409_, lean_object* v_d_2410_, lean_object* v_m_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_){
_start:
{
lean_object* v___x_2417_; 
v___x_2417_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_d_2410_, v_m_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_);
return v___x_2417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___boxed(lean_object* v_00_u03b1_2418_, lean_object* v_00_u03b2_2419_, lean_object* v_d_2420_, lean_object* v_m_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_){
_start:
{
lean_object* v_res_2427_; 
v_res_2427_ = l_Lean_Meta_LazyDiscrTree_runMatch(v_00_u03b1_2418_, v_00_u03b2_2419_, v_d_2420_, v_m_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_);
lean_dec(v_a_2425_);
lean_dec_ref(v_a_2424_);
lean_dec(v_a_2423_);
lean_dec_ref(v_a_2422_);
return v_res_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie___redArg(lean_object* v_i_2428_, lean_object* v_v_2429_, lean_object* v_a_2430_){
_start:
{
lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; 
v___x_2432_ = lean_st_ref_take(v_a_2430_);
v___x_2433_ = lean_box(0);
v___x_2434_ = lean_array_set(v___x_2432_, v_i_2428_, v_v_2429_);
v___x_2435_ = lean_st_ref_put(v_a_2430_, v___x_2434_);
v___x_2436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2433_);
return v___x_2436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie___redArg___boxed(lean_object* v_i_2437_, lean_object* v_v_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_){
_start:
{
lean_object* v_res_2441_; 
v_res_2441_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_i_2437_, v_v_2438_, v_a_2439_);
lean_dec(v_a_2439_);
lean_dec(v_i_2437_);
return v_res_2441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie(lean_object* v_00_u03b1_2442_, lean_object* v_i_2443_, lean_object* v_v_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_){
_start:
{
lean_object* v___x_2451_; 
v___x_2451_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_i_2443_, v_v_2444_, v_a_2445_);
return v___x_2451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie___boxed(lean_object* v_00_u03b1_2452_, lean_object* v_i_2453_, lean_object* v_v_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_){
_start:
{
lean_object* v_res_2461_; 
v_res_2461_ = l_Lean_Meta_LazyDiscrTree_setTrie(v_00_u03b1_2452_, v_i_2453_, v_v_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_);
lean_dec(v_a_2459_);
lean_dec_ref(v_a_2458_);
lean_dec(v_a_2457_);
lean_dec_ref(v_a_2456_);
lean_dec(v_a_2455_);
lean_dec(v_i_2453_);
return v_res_2461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___redArg___lam__0(lean_object* v_e_2462_, lean_object* v_a_2463_){
_start:
{
lean_object* v_sz_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; 
v_sz_2464_ = lean_array_get_size(v_a_2463_);
v___x_2465_ = lean_unsigned_to_nat(0u);
v___x_2466_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___x_2467_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2);
v___x_2468_ = lean_unsigned_to_nat(1u);
v___x_2469_ = lean_mk_empty_array_with_capacity(v___x_2468_);
v___x_2470_ = lean_array_push(v___x_2469_, v_e_2462_);
v___x_2471_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2471_, 0, v___x_2466_);
lean_ctor_set(v___x_2471_, 1, v___x_2465_);
lean_ctor_set(v___x_2471_, 2, v___x_2467_);
lean_ctor_set(v___x_2471_, 3, v___x_2470_);
v___x_2472_ = lean_array_push(v_a_2463_, v___x_2471_);
v___x_2473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2473_, 0, v_sz_2464_);
lean_ctor_set(v___x_2473_, 1, v___x_2472_);
return v___x_2473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___redArg(lean_object* v_inst_2474_, lean_object* v_e_2475_){
_start:
{
lean_object* v_modifyGet_2476_; lean_object* v___f_2477_; lean_object* v___x_2478_; 
v_modifyGet_2476_ = lean_ctor_get(v_inst_2474_, 2);
lean_inc(v_modifyGet_2476_);
lean_dec_ref(v_inst_2474_);
v___f_2477_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_newTrie___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2477_, 0, v_e_2475_);
v___x_2478_ = lean_apply_2(v_modifyGet_2476_, lean_box(0), v___f_2477_);
return v___x_2478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie(lean_object* v_m_2479_, lean_object* v_00_u03b1_2480_, lean_object* v_inst_2481_, lean_object* v_inst_2482_, lean_object* v_e_2483_){
_start:
{
lean_object* v___x_2484_; 
v___x_2484_ = l_Lean_Meta_LazyDiscrTree_newTrie___redArg(v_inst_2482_, v_e_2483_);
return v___x_2484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___boxed(lean_object* v_m_2485_, lean_object* v_00_u03b1_2486_, lean_object* v_inst_2487_, lean_object* v_inst_2488_, lean_object* v_e_2489_){
_start:
{
lean_object* v_res_2490_; 
v_res_2490_ = l_Lean_Meta_LazyDiscrTree_newTrie(v_m_2485_, v_00_u03b1_2486_, v_inst_2487_, v_inst_2488_, v_e_2489_);
lean_dec_ref(v_inst_2487_);
return v_res_2490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(lean_object* v_i_2491_, lean_object* v_e_2492_, lean_object* v_a_2493_){
_start:
{
lean_object* v___x_2495_; lean_object* v_fst_2497_; lean_object* v_snd_2498_; lean_object* v___x_2501_; lean_object* v___x_2502_; uint8_t v___x_2503_; 
v___x_2495_ = lean_st_ref_take(v_a_2493_);
v___x_2501_ = lean_box(0);
v___x_2502_ = lean_array_get_size(v___x_2495_);
v___x_2503_ = lean_nat_dec_lt(v_i_2491_, v___x_2502_);
if (v___x_2503_ == 0)
{
lean_dec_ref(v_e_2492_);
v_fst_2497_ = v___x_2501_;
v_snd_2498_ = v___x_2495_;
goto v___jp_2496_;
}
else
{
lean_object* v_v_2504_; lean_object* v_xs_x27_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; 
v_v_2504_ = lean_array_fget(v___x_2495_, v_i_2491_);
v_xs_x27_2505_ = lean_array_fset(v___x_2495_, v_i_2491_, v___x_2501_);
v___x_2506_ = l_Lean_Meta_LazyDiscrTree_Trie_pushPending___redArg(v_v_2504_, v_e_2492_);
v___x_2507_ = lean_array_fset(v_xs_x27_2505_, v_i_2491_, v___x_2506_);
v_fst_2497_ = v___x_2501_;
v_snd_2498_ = v___x_2507_;
goto v___jp_2496_;
}
v___jp_2496_:
{
lean_object* v___x_2499_; lean_object* v___x_2500_; 
v___x_2499_ = lean_st_ref_put(v_a_2493_, v_snd_2498_);
v___x_2500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2500_, 0, v_fst_2497_);
return v___x_2500_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg___boxed(lean_object* v_i_2508_, lean_object* v_e_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_){
_start:
{
lean_object* v_res_2512_; 
v_res_2512_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_i_2508_, v_e_2509_, v_a_2510_);
lean_dec(v_a_2510_);
lean_dec(v_i_2508_);
return v_res_2512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie(lean_object* v_00_u03b1_2513_, lean_object* v_i_2514_, lean_object* v_e_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_){
_start:
{
lean_object* v___x_2522_; 
v___x_2522_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_i_2514_, v_e_2515_, v_a_2516_);
return v___x_2522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___boxed(lean_object* v_00_u03b1_2523_, lean_object* v_i_2524_, lean_object* v_e_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_){
_start:
{
lean_object* v_res_2532_; 
v_res_2532_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie(v_00_u03b1_2523_, v_i_2524_, v_e_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_);
lean_dec(v_a_2530_);
lean_dec_ref(v_a_2529_);
lean_dec(v_a_2528_);
lean_dec_ref(v_a_2527_);
lean_dec(v_a_2526_);
lean_dec(v_i_2524_);
return v_res_2532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0(lean_object* v_x_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_){
_start:
{
lean_object* v___x_2540_; 
lean_inc(v___y_2534_);
v___x_2540_ = lean_apply_6(v_x_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, lean_box(0));
return v___x_2540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0___boxed(lean_object* v_x_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_){
_start:
{
lean_object* v_res_2548_; 
v_res_2548_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0(v_x_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_);
lean_dec(v___y_2542_);
return v_res_2548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(lean_object* v_lctx_2549_, lean_object* v_localInsts_2550_, lean_object* v_x_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_){
_start:
{
lean_object* v___f_2558_; lean_object* v___x_2559_; 
lean_inc(v___y_2552_);
v___f_2558_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2558_, 0, v_x_2551_);
lean_closure_set(v___f_2558_, 1, v___y_2552_);
v___x_2559_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_2549_, v_localInsts_2550_, v___f_2558_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_);
if (lean_obj_tag(v___x_2559_) == 0)
{
return v___x_2559_;
}
else
{
lean_object* v_a_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2567_; 
v_a_2560_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2567_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2567_ == 0)
{
v___x_2562_ = v___x_2559_;
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_a_2560_);
lean_dec(v___x_2559_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2565_; 
if (v_isShared_2563_ == 0)
{
v___x_2565_ = v___x_2562_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v_a_2560_);
v___x_2565_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
return v___x_2565_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___boxed(lean_object* v_lctx_2568_, lean_object* v_localInsts_2569_, lean_object* v_x_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_){
_start:
{
lean_object* v_res_2577_; 
v_res_2577_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(v_lctx_2568_, v_localInsts_2569_, v_x_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
lean_dec(v___y_2575_);
lean_dec_ref(v___y_2574_);
lean_dec(v___y_2573_);
lean_dec_ref(v___y_2572_);
lean_dec(v___y_2571_);
return v_res_2577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0(lean_object* v_00_u03b1_2578_, lean_object* v_00_u03b1_2579_, lean_object* v_lctx_2580_, lean_object* v_localInsts_2581_, lean_object* v_x_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_){
_start:
{
lean_object* v___x_2589_; 
v___x_2589_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(v_lctx_2580_, v_localInsts_2581_, v_x_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_);
return v___x_2589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___boxed(lean_object* v_00_u03b1_2590_, lean_object* v_00_u03b1_2591_, lean_object* v_lctx_2592_, lean_object* v_localInsts_2593_, lean_object* v_x_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_){
_start:
{
lean_object* v_res_2601_; 
v_res_2601_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0(v_00_u03b1_2590_, v_00_u03b1_2591_, v_lctx_2592_, v_localInsts_2593_, v_x_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_);
lean_dec(v___y_2599_);
lean_dec_ref(v___y_2598_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
lean_dec(v___y_2595_);
return v_res_2601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(lean_object* v_e_2602_, lean_object* v___y_2603_){
_start:
{
lean_object* v___x_2605_; lean_object* v_sz_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2605_ = lean_st_ref_take(v___y_2603_);
v_sz_2606_ = lean_array_get_size(v___x_2605_);
v___x_2607_ = lean_unsigned_to_nat(0u);
v___x_2608_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___x_2609_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2);
v___x_2610_ = lean_unsigned_to_nat(1u);
v___x_2611_ = lean_mk_empty_array_with_capacity(v___x_2610_);
v___x_2612_ = lean_array_push(v___x_2611_, v_e_2602_);
v___x_2613_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2613_, 0, v___x_2608_);
lean_ctor_set(v___x_2613_, 1, v___x_2607_);
lean_ctor_set(v___x_2613_, 2, v___x_2609_);
lean_ctor_set(v___x_2613_, 3, v___x_2612_);
v___x_2614_ = lean_array_push(v___x_2605_, v___x_2613_);
v___x_2615_ = lean_st_ref_put(v___y_2603_, v___x_2614_);
v___x_2616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2616_, 0, v_sz_2606_);
return v___x_2616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg___boxed(lean_object* v_e_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_){
_start:
{
lean_object* v_res_2620_; 
v_res_2620_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v_e_2617_, v___y_2618_);
lean_dec(v___y_2618_);
return v_res_2620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2(lean_object* v_00_u03b1_2621_, lean_object* v_e_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_){
_start:
{
lean_object* v___x_2629_; 
v___x_2629_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v_e_2622_, v___y_2623_);
return v___x_2629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___boxed(lean_object* v_00_u03b1_2630_, lean_object* v_e_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_){
_start:
{
lean_object* v_res_2638_; 
v_res_2638_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2(v_00_u03b1_2630_, v_e_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec(v___y_2632_);
return v_res_2638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0(uint8_t v___x_2639_, lean_object* v_todo_2640_, lean_object* v_e_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_){
_start:
{
lean_object* v___x_2648_; 
v___x_2648_ = l_Lean_Meta_LazyDiscrTree_pushArgs(v___x_2639_, v_todo_2640_, v_e_2641_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_);
return v___x_2648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0___boxed(lean_object* v___x_2649_, lean_object* v_todo_2650_, lean_object* v_e_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_){
_start:
{
uint8_t v___x_3423__boxed_2658_; lean_object* v_res_2659_; 
v___x_3423__boxed_2658_ = lean_unbox(v___x_2649_);
v_res_2659_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0(v___x_3423__boxed_2658_, v_todo_2650_, v_e_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_);
lean_dec(v___y_2656_);
lean_dec_ref(v___y_2655_);
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2653_);
lean_dec(v___y_2652_);
return v_res_2659_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(lean_object* v_a_2660_, lean_object* v_b_2661_, lean_object* v_x_2662_){
_start:
{
if (lean_obj_tag(v_x_2662_) == 0)
{
lean_dec(v_b_2661_);
lean_dec(v_a_2660_);
return v_x_2662_;
}
else
{
lean_object* v_key_2663_; lean_object* v_value_2664_; lean_object* v_tail_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2677_; 
v_key_2663_ = lean_ctor_get(v_x_2662_, 0);
v_value_2664_ = lean_ctor_get(v_x_2662_, 1);
v_tail_2665_ = lean_ctor_get(v_x_2662_, 2);
v_isSharedCheck_2677_ = !lean_is_exclusive(v_x_2662_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2667_ = v_x_2662_;
v_isShared_2668_ = v_isSharedCheck_2677_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_tail_2665_);
lean_inc(v_value_2664_);
lean_inc(v_key_2663_);
lean_dec(v_x_2662_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2677_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
uint8_t v___x_2669_; 
v___x_2669_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_2663_, v_a_2660_);
if (v___x_2669_ == 0)
{
lean_object* v___x_2670_; lean_object* v___x_2672_; 
v___x_2670_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(v_a_2660_, v_b_2661_, v_tail_2665_);
if (v_isShared_2668_ == 0)
{
lean_ctor_set(v___x_2667_, 2, v___x_2670_);
v___x_2672_ = v___x_2667_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v_key_2663_);
lean_ctor_set(v_reuseFailAlloc_2673_, 1, v_value_2664_);
lean_ctor_set(v_reuseFailAlloc_2673_, 2, v___x_2670_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
return v___x_2672_;
}
}
else
{
lean_object* v___x_2675_; 
lean_dec(v_value_2664_);
lean_dec(v_key_2663_);
if (v_isShared_2668_ == 0)
{
lean_ctor_set(v___x_2667_, 1, v_b_2661_);
lean_ctor_set(v___x_2667_, 0, v_a_2660_);
v___x_2675_ = v___x_2667_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_a_2660_);
lean_ctor_set(v_reuseFailAlloc_2676_, 1, v_b_2661_);
lean_ctor_set(v_reuseFailAlloc_2676_, 2, v_tail_2665_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(lean_object* v_a_2678_, lean_object* v_x_2679_){
_start:
{
if (lean_obj_tag(v_x_2679_) == 0)
{
uint8_t v___x_2680_; 
v___x_2680_ = 0;
return v___x_2680_;
}
else
{
lean_object* v_key_2681_; lean_object* v_tail_2682_; uint8_t v___x_2683_; 
v_key_2681_ = lean_ctor_get(v_x_2679_, 0);
v_tail_2682_ = lean_ctor_get(v_x_2679_, 2);
v___x_2683_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_2681_, v_a_2678_);
if (v___x_2683_ == 0)
{
v_x_2679_ = v_tail_2682_;
goto _start;
}
else
{
return v___x_2683_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg___boxed(lean_object* v_a_2685_, lean_object* v_x_2686_){
_start:
{
uint8_t v_res_2687_; lean_object* v_r_2688_; 
v_res_2687_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(v_a_2685_, v_x_2686_);
lean_dec(v_x_2686_);
lean_dec(v_a_2685_);
v_r_2688_ = lean_box(v_res_2687_);
return v_r_2688_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7___redArg(lean_object* v_x_2689_, lean_object* v_x_2690_){
_start:
{
if (lean_obj_tag(v_x_2690_) == 0)
{
return v_x_2689_;
}
else
{
lean_object* v_key_2691_; lean_object* v_value_2692_; lean_object* v_tail_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2716_; 
v_key_2691_ = lean_ctor_get(v_x_2690_, 0);
v_value_2692_ = lean_ctor_get(v_x_2690_, 1);
v_tail_2693_ = lean_ctor_get(v_x_2690_, 2);
v_isSharedCheck_2716_ = !lean_is_exclusive(v_x_2690_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2695_ = v_x_2690_;
v_isShared_2696_ = v_isSharedCheck_2716_;
goto v_resetjp_2694_;
}
else
{
lean_inc(v_tail_2693_);
lean_inc(v_value_2692_);
lean_inc(v_key_2691_);
lean_dec(v_x_2690_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2716_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
lean_object* v___x_2697_; uint64_t v___x_2698_; uint64_t v___x_2699_; uint64_t v___x_2700_; uint64_t v_fold_2701_; uint64_t v___x_2702_; uint64_t v___x_2703_; uint64_t v___x_2704_; size_t v___x_2705_; size_t v___x_2706_; size_t v___x_2707_; size_t v___x_2708_; size_t v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2712_; 
v___x_2697_ = lean_array_get_size(v_x_2689_);
v___x_2698_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_key_2691_);
v___x_2699_ = 32ULL;
v___x_2700_ = lean_uint64_shift_right(v___x_2698_, v___x_2699_);
v_fold_2701_ = lean_uint64_xor(v___x_2698_, v___x_2700_);
v___x_2702_ = 16ULL;
v___x_2703_ = lean_uint64_shift_right(v_fold_2701_, v___x_2702_);
v___x_2704_ = lean_uint64_xor(v_fold_2701_, v___x_2703_);
v___x_2705_ = lean_uint64_to_usize(v___x_2704_);
v___x_2706_ = lean_usize_of_nat(v___x_2697_);
v___x_2707_ = ((size_t)1ULL);
v___x_2708_ = lean_usize_sub(v___x_2706_, v___x_2707_);
v___x_2709_ = lean_usize_land(v___x_2705_, v___x_2708_);
v___x_2710_ = lean_array_uget_borrowed(v_x_2689_, v___x_2709_);
lean_inc(v___x_2710_);
if (v_isShared_2696_ == 0)
{
lean_ctor_set(v___x_2695_, 2, v___x_2710_);
v___x_2712_ = v___x_2695_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v_key_2691_);
lean_ctor_set(v_reuseFailAlloc_2715_, 1, v_value_2692_);
lean_ctor_set(v_reuseFailAlloc_2715_, 2, v___x_2710_);
v___x_2712_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
lean_object* v___x_2713_; 
v___x_2713_ = lean_array_uset(v_x_2689_, v___x_2709_, v___x_2712_);
v_x_2689_ = v___x_2713_;
v_x_2690_ = v_tail_2693_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6___redArg(lean_object* v_i_2717_, lean_object* v_source_2718_, lean_object* v_target_2719_){
_start:
{
lean_object* v___x_2720_; uint8_t v___x_2721_; 
v___x_2720_ = lean_array_get_size(v_source_2718_);
v___x_2721_ = lean_nat_dec_lt(v_i_2717_, v___x_2720_);
if (v___x_2721_ == 0)
{
lean_dec_ref(v_source_2718_);
lean_dec(v_i_2717_);
return v_target_2719_;
}
else
{
lean_object* v_es_2722_; lean_object* v___x_2723_; lean_object* v_source_2724_; lean_object* v_target_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; 
v_es_2722_ = lean_array_fget(v_source_2718_, v_i_2717_);
v___x_2723_ = lean_box(0);
v_source_2724_ = lean_array_fset(v_source_2718_, v_i_2717_, v___x_2723_);
v_target_2725_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7___redArg(v_target_2719_, v_es_2722_);
v___x_2726_ = lean_unsigned_to_nat(1u);
v___x_2727_ = lean_nat_add(v_i_2717_, v___x_2726_);
lean_dec(v_i_2717_);
v_i_2717_ = v___x_2727_;
v_source_2718_ = v_source_2724_;
v_target_2719_ = v_target_2725_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5___redArg(lean_object* v_data_2729_){
_start:
{
lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v_nbuckets_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; 
v___x_2730_ = lean_array_get_size(v_data_2729_);
v___x_2731_ = lean_unsigned_to_nat(2u);
v_nbuckets_2732_ = lean_nat_mul(v___x_2730_, v___x_2731_);
v___x_2733_ = lean_unsigned_to_nat(0u);
v___x_2734_ = lean_box(0);
v___x_2735_ = lean_mk_array(v_nbuckets_2732_, v___x_2734_);
v___x_2736_ = lean_array_propagate_mark(v_data_2729_, v___x_2735_);
v___x_2737_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6___redArg(v___x_2733_, v_data_2729_, v___x_2736_);
return v___x_2737_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(lean_object* v_m_2738_, lean_object* v_a_2739_, lean_object* v_b_2740_){
_start:
{
lean_object* v_size_2741_; lean_object* v_buckets_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2785_; 
v_size_2741_ = lean_ctor_get(v_m_2738_, 0);
v_buckets_2742_ = lean_ctor_get(v_m_2738_, 1);
v_isSharedCheck_2785_ = !lean_is_exclusive(v_m_2738_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2744_ = v_m_2738_;
v_isShared_2745_ = v_isSharedCheck_2785_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_buckets_2742_);
lean_inc(v_size_2741_);
lean_dec(v_m_2738_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_2785_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
lean_object* v___x_2746_; uint64_t v___x_2747_; uint64_t v___x_2748_; uint64_t v___x_2749_; uint64_t v_fold_2750_; uint64_t v___x_2751_; uint64_t v___x_2752_; uint64_t v___x_2753_; size_t v___x_2754_; size_t v___x_2755_; size_t v___x_2756_; size_t v___x_2757_; size_t v___x_2758_; lean_object* v_bkt_2759_; uint8_t v___x_2760_; 
v___x_2746_ = lean_array_get_size(v_buckets_2742_);
v___x_2747_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_a_2739_);
v___x_2748_ = 32ULL;
v___x_2749_ = lean_uint64_shift_right(v___x_2747_, v___x_2748_);
v_fold_2750_ = lean_uint64_xor(v___x_2747_, v___x_2749_);
v___x_2751_ = 16ULL;
v___x_2752_ = lean_uint64_shift_right(v_fold_2750_, v___x_2751_);
v___x_2753_ = lean_uint64_xor(v_fold_2750_, v___x_2752_);
v___x_2754_ = lean_uint64_to_usize(v___x_2753_);
v___x_2755_ = lean_usize_of_nat(v___x_2746_);
v___x_2756_ = ((size_t)1ULL);
v___x_2757_ = lean_usize_sub(v___x_2755_, v___x_2756_);
v___x_2758_ = lean_usize_land(v___x_2754_, v___x_2757_);
v_bkt_2759_ = lean_array_uget_borrowed(v_buckets_2742_, v___x_2758_);
v___x_2760_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(v_a_2739_, v_bkt_2759_);
if (v___x_2760_ == 0)
{
lean_object* v___x_2761_; lean_object* v_size_x27_2762_; lean_object* v___x_2763_; lean_object* v_buckets_x27_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; uint8_t v___x_2770_; 
v___x_2761_ = lean_unsigned_to_nat(1u);
v_size_x27_2762_ = lean_nat_add(v_size_2741_, v___x_2761_);
lean_dec(v_size_2741_);
lean_inc(v_bkt_2759_);
v___x_2763_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2763_, 0, v_a_2739_);
lean_ctor_set(v___x_2763_, 1, v_b_2740_);
lean_ctor_set(v___x_2763_, 2, v_bkt_2759_);
v_buckets_x27_2764_ = lean_array_uset(v_buckets_2742_, v___x_2758_, v___x_2763_);
v___x_2765_ = lean_unsigned_to_nat(4u);
v___x_2766_ = lean_nat_mul(v_size_x27_2762_, v___x_2765_);
v___x_2767_ = lean_unsigned_to_nat(3u);
v___x_2768_ = lean_nat_div(v___x_2766_, v___x_2767_);
lean_dec(v___x_2766_);
v___x_2769_ = lean_array_get_size(v_buckets_x27_2764_);
v___x_2770_ = lean_nat_dec_le(v___x_2768_, v___x_2769_);
lean_dec(v___x_2768_);
if (v___x_2770_ == 0)
{
lean_object* v_val_2771_; lean_object* v___x_2773_; 
v_val_2771_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5___redArg(v_buckets_x27_2764_);
if (v_isShared_2745_ == 0)
{
lean_ctor_set(v___x_2744_, 1, v_val_2771_);
lean_ctor_set(v___x_2744_, 0, v_size_x27_2762_);
v___x_2773_ = v___x_2744_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_size_x27_2762_);
lean_ctor_set(v_reuseFailAlloc_2774_, 1, v_val_2771_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
return v___x_2773_;
}
}
else
{
lean_object* v___x_2776_; 
if (v_isShared_2745_ == 0)
{
lean_ctor_set(v___x_2744_, 1, v_buckets_x27_2764_);
lean_ctor_set(v___x_2744_, 0, v_size_x27_2762_);
v___x_2776_ = v___x_2744_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_size_x27_2762_);
lean_ctor_set(v_reuseFailAlloc_2777_, 1, v_buckets_x27_2764_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
return v___x_2776_;
}
}
}
else
{
lean_object* v___x_2778_; lean_object* v_buckets_x27_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2783_; 
lean_inc(v_bkt_2759_);
v___x_2778_ = lean_box(0);
v_buckets_x27_2779_ = lean_array_uset(v_buckets_2742_, v___x_2758_, v___x_2778_);
v___x_2780_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(v_a_2739_, v_b_2740_, v_bkt_2759_);
v___x_2781_ = lean_array_uset(v_buckets_x27_2779_, v___x_2758_, v___x_2780_);
if (v_isShared_2745_ == 0)
{
lean_ctor_set(v___x_2744_, 1, v___x_2781_);
v___x_2783_ = v___x_2744_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v_size_2741_);
lean_ctor_set(v_reuseFailAlloc_2784_, 1, v___x_2781_);
v___x_2783_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
return v___x_2783_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(lean_object* v_a_2786_, lean_object* v_x_2787_){
_start:
{
if (lean_obj_tag(v_x_2787_) == 0)
{
lean_object* v___x_2788_; 
v___x_2788_ = lean_box(0);
return v___x_2788_;
}
else
{
lean_object* v_key_2789_; lean_object* v_value_2790_; lean_object* v_tail_2791_; uint8_t v___x_2792_; 
v_key_2789_ = lean_ctor_get(v_x_2787_, 0);
v_value_2790_ = lean_ctor_get(v_x_2787_, 1);
v_tail_2791_ = lean_ctor_get(v_x_2787_, 2);
v___x_2792_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_2789_, v_a_2786_);
if (v___x_2792_ == 0)
{
v_x_2787_ = v_tail_2791_;
goto _start;
}
else
{
lean_object* v___x_2794_; 
lean_inc(v_value_2790_);
v___x_2794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2794_, 0, v_value_2790_);
return v___x_2794_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg___boxed(lean_object* v_a_2795_, lean_object* v_x_2796_){
_start:
{
lean_object* v_res_2797_; 
v_res_2797_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(v_a_2795_, v_x_2796_);
lean_dec(v_x_2796_);
lean_dec(v_a_2795_);
return v_res_2797_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(lean_object* v_m_2798_, lean_object* v_a_2799_){
_start:
{
lean_object* v_buckets_2800_; lean_object* v___x_2801_; uint64_t v___x_2802_; uint64_t v___x_2803_; uint64_t v___x_2804_; uint64_t v_fold_2805_; uint64_t v___x_2806_; uint64_t v___x_2807_; uint64_t v___x_2808_; size_t v___x_2809_; size_t v___x_2810_; size_t v___x_2811_; size_t v___x_2812_; size_t v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; 
v_buckets_2800_ = lean_ctor_get(v_m_2798_, 1);
v___x_2801_ = lean_array_get_size(v_buckets_2800_);
v___x_2802_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_a_2799_);
v___x_2803_ = 32ULL;
v___x_2804_ = lean_uint64_shift_right(v___x_2802_, v___x_2803_);
v_fold_2805_ = lean_uint64_xor(v___x_2802_, v___x_2804_);
v___x_2806_ = 16ULL;
v___x_2807_ = lean_uint64_shift_right(v_fold_2805_, v___x_2806_);
v___x_2808_ = lean_uint64_xor(v_fold_2805_, v___x_2807_);
v___x_2809_ = lean_uint64_to_usize(v___x_2808_);
v___x_2810_ = lean_usize_of_nat(v___x_2801_);
v___x_2811_ = ((size_t)1ULL);
v___x_2812_ = lean_usize_sub(v___x_2810_, v___x_2811_);
v___x_2813_ = lean_usize_land(v___x_2809_, v___x_2812_);
v___x_2814_ = lean_array_uget_borrowed(v_buckets_2800_, v___x_2813_);
v___x_2815_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(v_a_2799_, v___x_2814_);
return v___x_2815_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg___boxed(lean_object* v_m_2816_, lean_object* v_a_2817_){
_start:
{
lean_object* v_res_2818_; 
v_res_2818_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_m_2816_, v_a_2817_);
lean_dec(v_a_2817_);
lean_dec_ref(v_m_2816_);
return v_res_2818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(lean_object* v_p_2819_, lean_object* v_entry_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_){
_start:
{
lean_object* v_snd_2827_; lean_object* v_snd_2828_; lean_object* v_fst_2829_; lean_object* v_fst_2830_; lean_object* v_snd_2831_; lean_object* v_fst_2832_; lean_object* v_fst_2833_; lean_object* v_snd_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; uint8_t v___x_2837_; 
v_snd_2827_ = lean_ctor_get(v_p_2819_, 1);
v_snd_2828_ = lean_ctor_get(v_entry_2820_, 1);
lean_inc(v_snd_2828_);
v_fst_2829_ = lean_ctor_get(v_p_2819_, 0);
v_fst_2830_ = lean_ctor_get(v_snd_2827_, 0);
v_snd_2831_ = lean_ctor_get(v_snd_2827_, 1);
v_fst_2832_ = lean_ctor_get(v_entry_2820_, 0);
lean_inc(v_fst_2832_);
lean_dec_ref(v_entry_2820_);
v_fst_2833_ = lean_ctor_get(v_snd_2828_, 0);
lean_inc(v_fst_2833_);
v_snd_2834_ = lean_ctor_get(v_snd_2828_, 1);
v___x_2835_ = lean_array_get_size(v_fst_2832_);
v___x_2836_ = lean_unsigned_to_nat(0u);
v___x_2837_ = lean_nat_dec_eq(v___x_2835_, v___x_2836_);
if (v___x_2837_ == 0)
{
lean_object* v_fst_2838_; lean_object* v_snd_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2944_; 
v_fst_2838_ = lean_ctor_get(v_fst_2833_, 0);
v_snd_2839_ = lean_ctor_get(v_fst_2833_, 1);
v_isSharedCheck_2944_ = !lean_is_exclusive(v_fst_2833_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2841_ = v_fst_2833_;
v_isShared_2842_ = v_isSharedCheck_2944_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_snd_2839_);
lean_inc(v_fst_2838_);
lean_dec(v_fst_2833_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2944_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v_e_2846_; lean_object* v_todo_2847_; lean_object* v___x_2848_; lean_object* v___f_2849_; lean_object* v___x_2850_; 
v___x_2843_ = l_Lean_instInhabitedExpr;
v___x_2844_ = lean_unsigned_to_nat(1u);
v___x_2845_ = lean_nat_sub(v___x_2835_, v___x_2844_);
v_e_2846_ = lean_array_get(v___x_2843_, v_fst_2832_, v___x_2845_);
lean_dec(v___x_2845_);
v_todo_2847_ = lean_array_pop(v_fst_2832_);
v___x_2848_ = lean_box(v___x_2837_);
v___f_2849_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2849_, 0, v___x_2848_);
lean_closure_set(v___f_2849_, 1, v_todo_2847_);
lean_closure_set(v___f_2849_, 2, v_e_2846_);
v___x_2850_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(v_fst_2838_, v_snd_2839_, v___f_2849_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_, v_a_2825_);
if (lean_obj_tag(v___x_2850_) == 0)
{
lean_object* v_a_2851_; lean_object* v_fst_2852_; lean_object* v_snd_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2935_; 
v_a_2851_ = lean_ctor_get(v___x_2850_, 0);
lean_inc(v_a_2851_);
lean_dec_ref_known(v___x_2850_, 1);
v_fst_2852_ = lean_ctor_get(v_a_2851_, 0);
v_snd_2853_ = lean_ctor_get(v_a_2851_, 1);
v_isSharedCheck_2935_ = !lean_is_exclusive(v_a_2851_);
if (v_isSharedCheck_2935_ == 0)
{
v___x_2855_ = v_a_2851_;
v_isShared_2856_ = v_isSharedCheck_2935_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_snd_2853_);
lean_inc(v_fst_2852_);
lean_dec(v_a_2851_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2935_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v___x_2857_; uint8_t v___x_2858_; 
v___x_2857_ = lean_box(3);
v___x_2858_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_fst_2852_, v___x_2857_);
if (v___x_2858_ == 0)
{
lean_object* v___x_2859_; 
v___x_2859_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_snd_2831_, v_fst_2852_);
if (lean_obj_tag(v___x_2859_) == 0)
{
lean_object* v___x_2861_; 
lean_inc(v_snd_2831_);
lean_inc(v_fst_2830_);
lean_inc(v_fst_2829_);
lean_dec_ref(v_p_2819_);
lean_inc(v_snd_2828_);
if (v_isShared_2856_ == 0)
{
lean_ctor_set(v___x_2855_, 1, v_snd_2828_);
lean_ctor_set(v___x_2855_, 0, v_snd_2853_);
v___x_2861_ = v___x_2855_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v_snd_2853_);
lean_ctor_set(v_reuseFailAlloc_2884_, 1, v_snd_2828_);
v___x_2861_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2881_; 
v_isSharedCheck_2881_ = !lean_is_exclusive(v_snd_2828_);
if (v_isSharedCheck_2881_ == 0)
{
lean_object* v_unused_2882_; lean_object* v_unused_2883_; 
v_unused_2882_ = lean_ctor_get(v_snd_2828_, 1);
lean_dec(v_unused_2882_);
v_unused_2883_ = lean_ctor_get(v_snd_2828_, 0);
lean_dec(v_unused_2883_);
v___x_2863_ = v_snd_2828_;
v_isShared_2864_ = v_isSharedCheck_2881_;
goto v_resetjp_2862_;
}
else
{
lean_dec(v_snd_2828_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_2881_;
goto v_resetjp_2862_;
}
v_resetjp_2862_:
{
lean_object* v___x_2865_; lean_object* v_a_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2880_; 
v___x_2865_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v___x_2861_, v_a_2821_);
v_a_2866_ = lean_ctor_get(v___x_2865_, 0);
v_isSharedCheck_2880_ = !lean_is_exclusive(v___x_2865_);
if (v_isSharedCheck_2880_ == 0)
{
v___x_2868_ = v___x_2865_;
v_isShared_2869_ = v_isSharedCheck_2880_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_a_2866_);
lean_dec(v___x_2865_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2880_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2870_; lean_object* v___x_2872_; 
v___x_2870_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_snd_2831_, v_fst_2852_, v_a_2866_);
if (v_isShared_2842_ == 0)
{
lean_ctor_set(v___x_2841_, 1, v___x_2870_);
lean_ctor_set(v___x_2841_, 0, v_fst_2830_);
v___x_2872_ = v___x_2841_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v_fst_2830_);
lean_ctor_set(v_reuseFailAlloc_2879_, 1, v___x_2870_);
v___x_2872_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
lean_object* v___x_2874_; 
if (v_isShared_2864_ == 0)
{
lean_ctor_set(v___x_2863_, 1, v___x_2872_);
lean_ctor_set(v___x_2863_, 0, v_fst_2829_);
v___x_2874_ = v___x_2863_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v_fst_2829_);
lean_ctor_set(v_reuseFailAlloc_2878_, 1, v___x_2872_);
v___x_2874_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
lean_object* v___x_2876_; 
if (v_isShared_2869_ == 0)
{
lean_ctor_set(v___x_2868_, 0, v___x_2874_);
v___x_2876_ = v___x_2868_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v___x_2874_);
v___x_2876_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
return v___x_2876_;
}
}
}
}
}
}
}
else
{
lean_object* v_val_2885_; lean_object* v___x_2887_; 
lean_dec(v_fst_2852_);
lean_del_object(v___x_2841_);
v_val_2885_ = lean_ctor_get(v___x_2859_, 0);
lean_inc(v_val_2885_);
lean_dec_ref_known(v___x_2859_, 1);
if (v_isShared_2856_ == 0)
{
lean_ctor_set(v___x_2855_, 1, v_snd_2828_);
lean_ctor_set(v___x_2855_, 0, v_snd_2853_);
v___x_2887_ = v___x_2855_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v_snd_2853_);
lean_ctor_set(v_reuseFailAlloc_2897_, 1, v_snd_2828_);
v___x_2887_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
lean_object* v___x_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2895_; 
v___x_2888_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_val_2885_, v___x_2887_, v_a_2821_);
lean_dec(v_val_2885_);
v_isSharedCheck_2895_ = !lean_is_exclusive(v___x_2888_);
if (v_isSharedCheck_2895_ == 0)
{
lean_object* v_unused_2896_; 
v_unused_2896_ = lean_ctor_get(v___x_2888_, 0);
lean_dec(v_unused_2896_);
v___x_2890_ = v___x_2888_;
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
else
{
lean_dec(v___x_2888_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v___x_2893_; 
if (v_isShared_2891_ == 0)
{
lean_ctor_set(v___x_2890_, 0, v_p_2819_);
v___x_2893_ = v___x_2890_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v_p_2819_);
v___x_2893_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
return v___x_2893_;
}
}
}
}
}
else
{
uint8_t v___x_2898_; 
lean_dec(v_fst_2852_);
v___x_2898_ = lean_nat_dec_eq(v_fst_2830_, v___x_2836_);
if (v___x_2898_ == 0)
{
lean_object* v___x_2900_; 
lean_del_object(v___x_2841_);
if (v_isShared_2856_ == 0)
{
lean_ctor_set(v___x_2855_, 1, v_snd_2828_);
lean_ctor_set(v___x_2855_, 0, v_snd_2853_);
v___x_2900_ = v___x_2855_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v_snd_2853_);
lean_ctor_set(v_reuseFailAlloc_2910_, 1, v_snd_2828_);
v___x_2900_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
lean_object* v___x_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2908_; 
v___x_2901_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_fst_2830_, v___x_2900_, v_a_2821_);
v_isSharedCheck_2908_ = !lean_is_exclusive(v___x_2901_);
if (v_isSharedCheck_2908_ == 0)
{
lean_object* v_unused_2909_; 
v_unused_2909_ = lean_ctor_get(v___x_2901_, 0);
lean_dec(v_unused_2909_);
v___x_2903_ = v___x_2901_;
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
else
{
lean_dec(v___x_2901_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v___x_2906_; 
if (v_isShared_2904_ == 0)
{
lean_ctor_set(v___x_2903_, 0, v_p_2819_);
v___x_2906_ = v___x_2903_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v_p_2819_);
v___x_2906_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
return v___x_2906_;
}
}
}
}
else
{
lean_object* v___x_2912_; 
lean_inc(v_snd_2831_);
lean_inc(v_fst_2829_);
lean_dec_ref(v_p_2819_);
lean_inc(v_snd_2828_);
if (v_isShared_2856_ == 0)
{
lean_ctor_set(v___x_2855_, 1, v_snd_2828_);
lean_ctor_set(v___x_2855_, 0, v_snd_2853_);
v___x_2912_ = v___x_2855_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2934_; 
v_reuseFailAlloc_2934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2934_, 0, v_snd_2853_);
lean_ctor_set(v_reuseFailAlloc_2934_, 1, v_snd_2828_);
v___x_2912_ = v_reuseFailAlloc_2934_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2931_; 
v_isSharedCheck_2931_ = !lean_is_exclusive(v_snd_2828_);
if (v_isSharedCheck_2931_ == 0)
{
lean_object* v_unused_2932_; lean_object* v_unused_2933_; 
v_unused_2932_ = lean_ctor_get(v_snd_2828_, 1);
lean_dec(v_unused_2932_);
v_unused_2933_ = lean_ctor_get(v_snd_2828_, 0);
lean_dec(v_unused_2933_);
v___x_2914_ = v_snd_2828_;
v_isShared_2915_ = v_isSharedCheck_2931_;
goto v_resetjp_2913_;
}
else
{
lean_dec(v_snd_2828_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2931_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2916_; lean_object* v_a_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2930_; 
v___x_2916_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v___x_2912_, v_a_2821_);
v_a_2917_ = lean_ctor_get(v___x_2916_, 0);
v_isSharedCheck_2930_ = !lean_is_exclusive(v___x_2916_);
if (v_isSharedCheck_2930_ == 0)
{
v___x_2919_ = v___x_2916_;
v_isShared_2920_ = v_isSharedCheck_2930_;
goto v_resetjp_2918_;
}
else
{
lean_inc(v_a_2917_);
lean_dec(v___x_2916_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2930_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v___x_2922_; 
if (v_isShared_2842_ == 0)
{
lean_ctor_set(v___x_2841_, 1, v_snd_2831_);
lean_ctor_set(v___x_2841_, 0, v_a_2917_);
v___x_2922_ = v___x_2841_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v_a_2917_);
lean_ctor_set(v_reuseFailAlloc_2929_, 1, v_snd_2831_);
v___x_2922_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
lean_object* v___x_2924_; 
if (v_isShared_2915_ == 0)
{
lean_ctor_set(v___x_2914_, 1, v___x_2922_);
lean_ctor_set(v___x_2914_, 0, v_fst_2829_);
v___x_2924_ = v___x_2914_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_fst_2829_);
lean_ctor_set(v_reuseFailAlloc_2928_, 1, v___x_2922_);
v___x_2924_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
lean_object* v___x_2926_; 
if (v_isShared_2920_ == 0)
{
lean_ctor_set(v___x_2919_, 0, v___x_2924_);
v___x_2926_ = v___x_2919_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v___x_2924_);
v___x_2926_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
return v___x_2926_;
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
lean_object* v_a_2936_; lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2943_; 
lean_del_object(v___x_2841_);
lean_dec(v_snd_2828_);
lean_dec_ref(v_p_2819_);
v_a_2936_ = lean_ctor_get(v___x_2850_, 0);
v_isSharedCheck_2943_ = !lean_is_exclusive(v___x_2850_);
if (v_isSharedCheck_2943_ == 0)
{
v___x_2938_ = v___x_2850_;
v_isShared_2939_ = v_isSharedCheck_2943_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_a_2936_);
lean_dec(v___x_2850_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_2943_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
lean_object* v___x_2941_; 
if (v_isShared_2939_ == 0)
{
v___x_2941_ = v___x_2938_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v_a_2936_);
v___x_2941_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
return v___x_2941_;
}
}
}
}
}
else
{
lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2953_; 
lean_inc(v_snd_2834_);
lean_inc(v_fst_2829_);
lean_inc(v_snd_2827_);
lean_dec(v_fst_2833_);
lean_dec(v_fst_2832_);
lean_dec_ref(v_p_2819_);
v_isSharedCheck_2953_ = !lean_is_exclusive(v_snd_2828_);
if (v_isSharedCheck_2953_ == 0)
{
lean_object* v_unused_2954_; lean_object* v_unused_2955_; 
v_unused_2954_ = lean_ctor_get(v_snd_2828_, 1);
lean_dec(v_unused_2954_);
v_unused_2955_ = lean_ctor_get(v_snd_2828_, 0);
lean_dec(v_unused_2955_);
v___x_2946_ = v_snd_2828_;
v_isShared_2947_ = v_isSharedCheck_2953_;
goto v_resetjp_2945_;
}
else
{
lean_dec(v_snd_2828_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2953_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
lean_object* v_values_2948_; lean_object* v___x_2950_; 
v_values_2948_ = lean_array_push(v_fst_2829_, v_snd_2834_);
if (v_isShared_2947_ == 0)
{
lean_ctor_set(v___x_2946_, 1, v_snd_2827_);
lean_ctor_set(v___x_2946_, 0, v_values_2948_);
v___x_2950_ = v___x_2946_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_values_2948_);
lean_ctor_set(v_reuseFailAlloc_2952_, 1, v_snd_2827_);
v___x_2950_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
lean_object* v___x_2951_; 
v___x_2951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2950_);
return v___x_2951_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___boxed(lean_object* v_p_2956_, lean_object* v_entry_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_, lean_object* v_a_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_){
_start:
{
lean_object* v_res_2964_; 
v_res_2964_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(v_p_2956_, v_entry_2957_, v_a_2958_, v_a_2959_, v_a_2960_, v_a_2961_, v_a_2962_);
lean_dec(v_a_2962_);
lean_dec_ref(v_a_2961_);
lean_dec(v_a_2960_);
lean_dec_ref(v_a_2959_);
lean_dec(v_a_2958_);
return v_res_2964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry(lean_object* v_00_u03b1_2965_, lean_object* v_p_2966_, lean_object* v_entry_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_){
_start:
{
lean_object* v___x_2974_; 
v___x_2974_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(v_p_2966_, v_entry_2967_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_);
return v___x_2974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___boxed(lean_object* v_00_u03b1_2975_, lean_object* v_p_2976_, lean_object* v_entry_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_){
_start:
{
lean_object* v_res_2984_; 
v_res_2984_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry(v_00_u03b1_2975_, v_p_2976_, v_entry_2977_, v_a_2978_, v_a_2979_, v_a_2980_, v_a_2981_, v_a_2982_);
lean_dec(v_a_2982_);
lean_dec_ref(v_a_2981_);
lean_dec(v_a_2980_);
lean_dec_ref(v_a_2979_);
lean_dec(v_a_2978_);
return v_res_2984_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1(lean_object* v_00_u03b2_2985_, lean_object* v_m_2986_, lean_object* v_a_2987_){
_start:
{
lean_object* v___x_2988_; 
v___x_2988_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_m_2986_, v_a_2987_);
return v___x_2988_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___boxed(lean_object* v_00_u03b2_2989_, lean_object* v_m_2990_, lean_object* v_a_2991_){
_start:
{
lean_object* v_res_2992_; 
v_res_2992_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1(v_00_u03b2_2989_, v_m_2990_, v_a_2991_);
lean_dec(v_a_2991_);
lean_dec_ref(v_m_2990_);
return v_res_2992_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3(lean_object* v_00_u03b2_2993_, lean_object* v_m_2994_, lean_object* v_a_2995_, lean_object* v_b_2996_){
_start:
{
lean_object* v___x_2997_; 
v___x_2997_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_m_2994_, v_a_2995_, v_b_2996_);
return v___x_2997_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1(lean_object* v_00_u03b2_2998_, lean_object* v_a_2999_, lean_object* v_x_3000_){
_start:
{
lean_object* v___x_3001_; 
v___x_3001_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(v_a_2999_, v_x_3000_);
return v___x_3001_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___boxed(lean_object* v_00_u03b2_3002_, lean_object* v_a_3003_, lean_object* v_x_3004_){
_start:
{
lean_object* v_res_3005_; 
v_res_3005_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1(v_00_u03b2_3002_, v_a_3003_, v_x_3004_);
lean_dec(v_x_3004_);
lean_dec(v_a_3003_);
return v_res_3005_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4(lean_object* v_00_u03b2_3006_, lean_object* v_a_3007_, lean_object* v_x_3008_){
_start:
{
uint8_t v___x_3009_; 
v___x_3009_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(v_a_3007_, v_x_3008_);
return v___x_3009_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___boxed(lean_object* v_00_u03b2_3010_, lean_object* v_a_3011_, lean_object* v_x_3012_){
_start:
{
uint8_t v_res_3013_; lean_object* v_r_3014_; 
v_res_3013_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4(v_00_u03b2_3010_, v_a_3011_, v_x_3012_);
lean_dec(v_x_3012_);
lean_dec(v_a_3011_);
v_r_3014_ = lean_box(v_res_3013_);
return v_r_3014_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5(lean_object* v_00_u03b2_3015_, lean_object* v_data_3016_){
_start:
{
lean_object* v___x_3017_; 
v___x_3017_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5___redArg(v_data_3016_);
return v___x_3017_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6(lean_object* v_00_u03b2_3018_, lean_object* v_a_3019_, lean_object* v_b_3020_, lean_object* v_x_3021_){
_start:
{
lean_object* v___x_3022_; 
v___x_3022_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(v_a_3019_, v_b_3020_, v_x_3021_);
return v___x_3022_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_3023_, lean_object* v_i_3024_, lean_object* v_source_3025_, lean_object* v_target_3026_){
_start:
{
lean_object* v___x_3027_; 
v___x_3027_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6___redArg(v_i_3024_, v_source_3025_, v_target_3026_);
return v___x_3027_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_3028_, lean_object* v_x_3029_, lean_object* v_x_3030_){
_start:
{
lean_object* v___x_3031_; 
v___x_3031_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7___redArg(v_x_3029_, v_x_3030_);
return v___x_3031_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(lean_object* v_as_3032_, size_t v_i_3033_, size_t v_stop_3034_, lean_object* v_b_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_){
_start:
{
uint8_t v___x_3042_; 
v___x_3042_ = lean_usize_dec_eq(v_i_3033_, v_stop_3034_);
if (v___x_3042_ == 0)
{
lean_object* v___x_3043_; lean_object* v___x_3044_; 
v___x_3043_ = lean_array_uget_borrowed(v_as_3032_, v_i_3033_);
lean_inc(v___x_3043_);
v___x_3044_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(v_b_3035_, v___x_3043_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_);
if (lean_obj_tag(v___x_3044_) == 0)
{
lean_object* v_a_3045_; size_t v___x_3046_; size_t v___x_3047_; 
v_a_3045_ = lean_ctor_get(v___x_3044_, 0);
lean_inc(v_a_3045_);
lean_dec_ref_known(v___x_3044_, 1);
v___x_3046_ = ((size_t)1ULL);
v___x_3047_ = lean_usize_add(v_i_3033_, v___x_3046_);
v_i_3033_ = v___x_3047_;
v_b_3035_ = v_a_3045_;
goto _start;
}
else
{
return v___x_3044_;
}
}
else
{
lean_object* v___x_3049_; 
v___x_3049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3049_, 0, v_b_3035_);
return v___x_3049_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg___boxed(lean_object* v_as_3050_, lean_object* v_i_3051_, lean_object* v_stop_3052_, lean_object* v_b_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_){
_start:
{
size_t v_i_boxed_3060_; size_t v_stop_boxed_3061_; lean_object* v_res_3062_; 
v_i_boxed_3060_ = lean_unbox_usize(v_i_3051_);
lean_dec(v_i_3051_);
v_stop_boxed_3061_ = lean_unbox_usize(v_stop_3052_);
lean_dec(v_stop_3052_);
v_res_3062_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_as_3050_, v_i_boxed_3060_, v_stop_boxed_3061_, v_b_3053_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_, v___y_3058_);
lean_dec(v___y_3058_);
lean_dec_ref(v___y_3057_);
lean_dec(v___y_3056_);
lean_dec_ref(v___y_3055_);
lean_dec(v___y_3054_);
lean_dec_ref(v_as_3050_);
return v_res_3062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(lean_object* v_values_3063_, lean_object* v_starIdx_3064_, lean_object* v_children_3065_, lean_object* v_entries_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_){
_start:
{
lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; uint8_t v___x_3077_; 
v___x_3073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3073_, 0, v_starIdx_3064_);
lean_ctor_set(v___x_3073_, 1, v_children_3065_);
v___x_3074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3074_, 0, v_values_3063_);
lean_ctor_set(v___x_3074_, 1, v___x_3073_);
v___x_3075_ = lean_unsigned_to_nat(0u);
v___x_3076_ = lean_array_get_size(v_entries_3066_);
v___x_3077_ = lean_nat_dec_lt(v___x_3075_, v___x_3076_);
if (v___x_3077_ == 0)
{
lean_object* v___x_3078_; 
v___x_3078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3078_, 0, v___x_3074_);
return v___x_3078_;
}
else
{
size_t v___x_3079_; size_t v___x_3080_; lean_object* v___x_3081_; 
v___x_3079_ = ((size_t)0ULL);
v___x_3080_ = lean_usize_of_nat(v___x_3076_);
v___x_3081_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_entries_3066_, v___x_3079_, v___x_3080_, v___x_3074_, v_a_3067_, v_a_3068_, v_a_3069_, v_a_3070_, v_a_3071_);
return v___x_3081_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg___boxed(lean_object* v_values_3082_, lean_object* v_starIdx_3083_, lean_object* v_children_3084_, lean_object* v_entries_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_){
_start:
{
lean_object* v_res_3092_; 
v_res_3092_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(v_values_3082_, v_starIdx_3083_, v_children_3084_, v_entries_3085_, v_a_3086_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_);
lean_dec(v_a_3090_);
lean_dec_ref(v_a_3089_);
lean_dec(v_a_3088_);
lean_dec_ref(v_a_3087_);
lean_dec(v_a_3086_);
lean_dec_ref(v_entries_3085_);
return v_res_3092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries(lean_object* v_00_u03b1_3093_, lean_object* v_values_3094_, lean_object* v_starIdx_3095_, lean_object* v_children_3096_, lean_object* v_entries_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_, lean_object* v_a_3102_){
_start:
{
lean_object* v___x_3104_; 
v___x_3104_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(v_values_3094_, v_starIdx_3095_, v_children_3096_, v_entries_3097_, v_a_3098_, v_a_3099_, v_a_3100_, v_a_3101_, v_a_3102_);
return v___x_3104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries___boxed(lean_object* v_00_u03b1_3105_, lean_object* v_values_3106_, lean_object* v_starIdx_3107_, lean_object* v_children_3108_, lean_object* v_entries_3109_, lean_object* v_a_3110_, lean_object* v_a_3111_, lean_object* v_a_3112_, lean_object* v_a_3113_, lean_object* v_a_3114_, lean_object* v_a_3115_){
_start:
{
lean_object* v_res_3116_; 
v_res_3116_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries(v_00_u03b1_3105_, v_values_3106_, v_starIdx_3107_, v_children_3108_, v_entries_3109_, v_a_3110_, v_a_3111_, v_a_3112_, v_a_3113_, v_a_3114_);
lean_dec(v_a_3114_);
lean_dec_ref(v_a_3113_);
lean_dec(v_a_3112_);
lean_dec_ref(v_a_3111_);
lean_dec(v_a_3110_);
lean_dec_ref(v_entries_3109_);
return v_res_3116_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0(lean_object* v_00_u03b1_3117_, lean_object* v_as_3118_, size_t v_i_3119_, size_t v_stop_3120_, lean_object* v_b_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_){
_start:
{
lean_object* v___x_3128_; 
v___x_3128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_as_3118_, v_i_3119_, v_stop_3120_, v_b_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_);
return v___x_3128_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___boxed(lean_object* v_00_u03b1_3129_, lean_object* v_as_3130_, lean_object* v_i_3131_, lean_object* v_stop_3132_, lean_object* v_b_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_){
_start:
{
size_t v_i_boxed_3140_; size_t v_stop_boxed_3141_; lean_object* v_res_3142_; 
v_i_boxed_3140_ = lean_unbox_usize(v_i_3131_);
lean_dec(v_i_3131_);
v_stop_boxed_3141_ = lean_unbox_usize(v_stop_3132_);
lean_dec(v_stop_3132_);
v_res_3142_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0(v_00_u03b1_3129_, v_as_3130_, v_i_boxed_3140_, v_stop_boxed_3141_, v_b_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
lean_dec(v___y_3136_);
lean_dec_ref(v___y_3135_);
lean_dec(v___y_3134_);
lean_dec_ref(v_as_3130_);
return v_res_3142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode___redArg(lean_object* v_c_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_, lean_object* v_a_3146_, lean_object* v_a_3147_, lean_object* v_a_3148_){
_start:
{
lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v_values_3153_; lean_object* v_star_3154_; lean_object* v_children_3155_; lean_object* v_pending_3156_; lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3186_; 
v___x_3150_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0);
v___x_3151_ = lean_st_ref_get(v_a_3144_);
v___x_3152_ = lean_array_get(v___x_3150_, v___x_3151_, v_c_3143_);
lean_dec(v___x_3151_);
v_values_3153_ = lean_ctor_get(v___x_3152_, 0);
v_star_3154_ = lean_ctor_get(v___x_3152_, 1);
v_children_3155_ = lean_ctor_get(v___x_3152_, 2);
v_pending_3156_ = lean_ctor_get(v___x_3152_, 3);
v_isSharedCheck_3186_ = !lean_is_exclusive(v___x_3152_);
if (v_isSharedCheck_3186_ == 0)
{
v___x_3158_ = v___x_3152_;
v_isShared_3159_ = v_isSharedCheck_3186_;
goto v_resetjp_3157_;
}
else
{
lean_inc(v_pending_3156_);
lean_inc(v_children_3155_);
lean_inc(v_star_3154_);
lean_inc(v_values_3153_);
lean_dec(v___x_3152_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3186_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
lean_object* v___x_3160_; lean_object* v___x_3161_; uint8_t v___x_3162_; 
v___x_3160_ = lean_array_get_size(v_pending_3156_);
v___x_3161_ = lean_unsigned_to_nat(0u);
v___x_3162_ = lean_nat_dec_eq(v___x_3160_, v___x_3161_);
if (v___x_3162_ == 0)
{
lean_object* v___x_3163_; lean_object* v___x_3164_; 
v___x_3163_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_c_3143_, v___x_3150_, v_a_3144_);
lean_dec_ref(v___x_3163_);
v___x_3164_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(v_values_3153_, v_star_3154_, v_children_3155_, v_pending_3156_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_, v_a_3148_);
lean_dec_ref(v_pending_3156_);
if (lean_obj_tag(v___x_3164_) == 0)
{
lean_object* v_a_3165_; lean_object* v_snd_3166_; lean_object* v_fst_3167_; lean_object* v_fst_3168_; lean_object* v_snd_3169_; lean_object* v___x_3170_; lean_object* v___x_3172_; 
v_a_3165_ = lean_ctor_get(v___x_3164_, 0);
lean_inc(v_a_3165_);
lean_dec_ref_known(v___x_3164_, 1);
v_snd_3166_ = lean_ctor_get(v_a_3165_, 1);
v_fst_3167_ = lean_ctor_get(v_a_3165_, 0);
v_fst_3168_ = lean_ctor_get(v_snd_3166_, 0);
v_snd_3169_ = lean_ctor_get(v_snd_3166_, 1);
v___x_3170_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__3));
lean_inc(v_snd_3169_);
lean_inc(v_fst_3168_);
lean_inc(v_fst_3167_);
if (v_isShared_3159_ == 0)
{
lean_ctor_set(v___x_3158_, 3, v___x_3170_);
lean_ctor_set(v___x_3158_, 2, v_snd_3169_);
lean_ctor_set(v___x_3158_, 1, v_fst_3168_);
lean_ctor_set(v___x_3158_, 0, v_fst_3167_);
v___x_3172_ = v___x_3158_;
goto v_reusejp_3171_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v_fst_3167_);
lean_ctor_set(v_reuseFailAlloc_3182_, 1, v_fst_3168_);
lean_ctor_set(v_reuseFailAlloc_3182_, 2, v_snd_3169_);
lean_ctor_set(v_reuseFailAlloc_3182_, 3, v___x_3170_);
v___x_3172_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3171_;
}
v_reusejp_3171_:
{
lean_object* v___x_3173_; lean_object* v___x_3175_; uint8_t v_isShared_3176_; uint8_t v_isSharedCheck_3180_; 
v___x_3173_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_c_3143_, v___x_3172_, v_a_3144_);
v_isSharedCheck_3180_ = !lean_is_exclusive(v___x_3173_);
if (v_isSharedCheck_3180_ == 0)
{
lean_object* v_unused_3181_; 
v_unused_3181_ = lean_ctor_get(v___x_3173_, 0);
lean_dec(v_unused_3181_);
v___x_3175_ = v___x_3173_;
v_isShared_3176_ = v_isSharedCheck_3180_;
goto v_resetjp_3174_;
}
else
{
lean_dec(v___x_3173_);
v___x_3175_ = lean_box(0);
v_isShared_3176_ = v_isSharedCheck_3180_;
goto v_resetjp_3174_;
}
v_resetjp_3174_:
{
lean_object* v___x_3178_; 
if (v_isShared_3176_ == 0)
{
lean_ctor_set(v___x_3175_, 0, v_a_3165_);
v___x_3178_ = v___x_3175_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v_a_3165_);
v___x_3178_ = v_reuseFailAlloc_3179_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
return v___x_3178_;
}
}
}
}
else
{
lean_del_object(v___x_3158_);
return v___x_3164_;
}
}
else
{
lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; 
lean_del_object(v___x_3158_);
lean_dec_ref(v_pending_3156_);
v___x_3183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3183_, 0, v_star_3154_);
lean_ctor_set(v___x_3183_, 1, v_children_3155_);
v___x_3184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3184_, 0, v_values_3153_);
lean_ctor_set(v___x_3184_, 1, v___x_3183_);
v___x_3185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3185_, 0, v___x_3184_);
return v___x_3185_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode___redArg___boxed(lean_object* v_c_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_, lean_object* v_a_3193_){
_start:
{
lean_object* v_res_3194_; 
v_res_3194_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_c_3187_, v_a_3188_, v_a_3189_, v_a_3190_, v_a_3191_, v_a_3192_);
lean_dec(v_a_3192_);
lean_dec_ref(v_a_3191_);
lean_dec(v_a_3190_);
lean_dec_ref(v_a_3189_);
lean_dec(v_a_3188_);
lean_dec(v_c_3187_);
return v_res_3194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode(lean_object* v_00_u03b1_3195_, lean_object* v_c_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_, lean_object* v_a_3200_, lean_object* v_a_3201_){
_start:
{
lean_object* v___x_3203_; 
v___x_3203_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_c_3196_, v_a_3197_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_);
return v___x_3203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode___boxed(lean_object* v_00_u03b1_3204_, lean_object* v_c_3205_, lean_object* v_a_3206_, lean_object* v_a_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_){
_start:
{
lean_object* v_res_3212_; 
v_res_3212_ = l_Lean_Meta_LazyDiscrTree_evalNode(v_00_u03b1_3204_, v_c_3205_, v_a_3206_, v_a_3207_, v_a_3208_, v_a_3209_, v_a_3210_);
lean_dec(v_a_3210_);
lean_dec_ref(v_a_3209_);
lean_dec(v_a_3208_);
lean_dec_ref(v_a_3207_);
lean_dec(v_a_3206_);
lean_dec(v_c_3205_);
return v_res_3212_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(lean_object* v_a_3213_, lean_object* v_fallback_3214_, lean_object* v_x_3215_){
_start:
{
if (lean_obj_tag(v_x_3215_) == 0)
{
lean_inc(v_fallback_3214_);
return v_fallback_3214_;
}
else
{
lean_object* v_key_3216_; lean_object* v_value_3217_; lean_object* v_tail_3218_; uint8_t v___x_3219_; 
v_key_3216_ = lean_ctor_get(v_x_3215_, 0);
v_value_3217_ = lean_ctor_get(v_x_3215_, 1);
v_tail_3218_ = lean_ctor_get(v_x_3215_, 2);
v___x_3219_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_3216_, v_a_3213_);
if (v___x_3219_ == 0)
{
v_x_3215_ = v_tail_3218_;
goto _start;
}
else
{
lean_inc(v_value_3217_);
return v_value_3217_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg___boxed(lean_object* v_a_3221_, lean_object* v_fallback_3222_, lean_object* v_x_3223_){
_start:
{
lean_object* v_res_3224_; 
v_res_3224_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(v_a_3221_, v_fallback_3222_, v_x_3223_);
lean_dec(v_x_3223_);
lean_dec(v_fallback_3222_);
lean_dec(v_a_3221_);
return v_res_3224_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(lean_object* v_m_3225_, lean_object* v_a_3226_, lean_object* v_fallback_3227_){
_start:
{
lean_object* v_buckets_3228_; lean_object* v___x_3229_; uint64_t v___x_3230_; uint64_t v___x_3231_; uint64_t v___x_3232_; uint64_t v_fold_3233_; uint64_t v___x_3234_; uint64_t v___x_3235_; uint64_t v___x_3236_; size_t v___x_3237_; size_t v___x_3238_; size_t v___x_3239_; size_t v___x_3240_; size_t v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; 
v_buckets_3228_ = lean_ctor_get(v_m_3225_, 1);
v___x_3229_ = lean_array_get_size(v_buckets_3228_);
v___x_3230_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_a_3226_);
v___x_3231_ = 32ULL;
v___x_3232_ = lean_uint64_shift_right(v___x_3230_, v___x_3231_);
v_fold_3233_ = lean_uint64_xor(v___x_3230_, v___x_3232_);
v___x_3234_ = 16ULL;
v___x_3235_ = lean_uint64_shift_right(v_fold_3233_, v___x_3234_);
v___x_3236_ = lean_uint64_xor(v_fold_3233_, v___x_3235_);
v___x_3237_ = lean_uint64_to_usize(v___x_3236_);
v___x_3238_ = lean_usize_of_nat(v___x_3229_);
v___x_3239_ = ((size_t)1ULL);
v___x_3240_ = lean_usize_sub(v___x_3238_, v___x_3239_);
v___x_3241_ = lean_usize_land(v___x_3237_, v___x_3240_);
v___x_3242_ = lean_array_uget_borrowed(v_buckets_3228_, v___x_3241_);
v___x_3243_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(v_a_3226_, v_fallback_3227_, v___x_3242_);
return v___x_3243_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg___boxed(lean_object* v_m_3244_, lean_object* v_a_3245_, lean_object* v_fallback_3246_){
_start:
{
lean_object* v_res_3247_; 
v_res_3247_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_m_3244_, v_a_3245_, v_fallback_3246_);
lean_dec(v_fallback_3246_);
lean_dec(v_a_3245_);
lean_dec_ref(v_m_3244_);
return v_res_3247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg(lean_object* v_next_3248_, lean_object* v_rest_3249_, lean_object* v_a_3250_, lean_object* v_a_3251_, lean_object* v_a_3252_, lean_object* v_a_3253_, lean_object* v_a_3254_){
_start:
{
lean_object* v___x_3256_; uint8_t v___x_3257_; 
v___x_3256_ = lean_unsigned_to_nat(0u);
v___x_3257_ = lean_nat_dec_eq(v_next_3248_, v___x_3256_);
if (v___x_3257_ == 0)
{
lean_object* v___x_3258_; 
v___x_3258_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_next_3248_, v_a_3250_, v_a_3251_, v_a_3252_, v_a_3253_, v_a_3254_);
if (lean_obj_tag(v___x_3258_) == 0)
{
lean_object* v_a_3259_; lean_object* v___x_3261_; uint8_t v_isShared_3262_; uint8_t v_isSharedCheck_3284_; 
v_a_3259_ = lean_ctor_get(v___x_3258_, 0);
v_isSharedCheck_3284_ = !lean_is_exclusive(v___x_3258_);
if (v_isSharedCheck_3284_ == 0)
{
v___x_3261_ = v___x_3258_;
v_isShared_3262_ = v_isSharedCheck_3284_;
goto v_resetjp_3260_;
}
else
{
lean_inc(v_a_3259_);
lean_dec(v___x_3258_);
v___x_3261_ = lean_box(0);
v_isShared_3262_ = v_isSharedCheck_3284_;
goto v_resetjp_3260_;
}
v_resetjp_3260_:
{
lean_object* v_snd_3263_; 
v_snd_3263_ = lean_ctor_get(v_a_3259_, 1);
lean_inc(v_snd_3263_);
lean_dec(v_a_3259_);
if (lean_obj_tag(v_rest_3249_) == 0)
{
lean_object* v_fst_3264_; lean_object* v_snd_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3273_; 
v_fst_3264_ = lean_ctor_get(v_snd_3263_, 0);
lean_inc(v_fst_3264_);
v_snd_3265_ = lean_ctor_get(v_snd_3263_, 1);
lean_inc(v_snd_3265_);
lean_dec(v_snd_3263_);
v___x_3266_ = lean_st_ref_take(v_a_3250_);
v___x_3267_ = lean_box(0);
v___x_3268_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___x_3269_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3269_, 0, v___x_3268_);
lean_ctor_set(v___x_3269_, 1, v_fst_3264_);
lean_ctor_set(v___x_3269_, 2, v_snd_3265_);
lean_ctor_set(v___x_3269_, 3, v___x_3268_);
v___x_3270_ = lean_array_set(v___x_3266_, v_next_3248_, v___x_3269_);
lean_dec(v_next_3248_);
v___x_3271_ = lean_st_ref_put(v_a_3250_, v___x_3270_);
if (v_isShared_3262_ == 0)
{
lean_ctor_set(v___x_3261_, 0, v___x_3267_);
v___x_3273_ = v___x_3261_;
goto v_reusejp_3272_;
}
else
{
lean_object* v_reuseFailAlloc_3274_; 
v_reuseFailAlloc_3274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3274_, 0, v___x_3267_);
v___x_3273_ = v_reuseFailAlloc_3274_;
goto v_reusejp_3272_;
}
v_reusejp_3272_:
{
return v___x_3273_;
}
}
else
{
lean_object* v_fst_3275_; lean_object* v_snd_3276_; lean_object* v_head_3277_; lean_object* v_tail_3278_; lean_object* v___x_3279_; uint8_t v___x_3280_; 
lean_del_object(v___x_3261_);
lean_dec(v_next_3248_);
v_fst_3275_ = lean_ctor_get(v_snd_3263_, 0);
lean_inc(v_fst_3275_);
v_snd_3276_ = lean_ctor_get(v_snd_3263_, 1);
lean_inc(v_snd_3276_);
lean_dec(v_snd_3263_);
v_head_3277_ = lean_ctor_get(v_rest_3249_, 0);
v_tail_3278_ = lean_ctor_get(v_rest_3249_, 1);
v___x_3279_ = lean_box(3);
v___x_3280_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_head_3277_, v___x_3279_);
if (v___x_3280_ == 0)
{
lean_object* v___x_3281_; 
lean_dec(v_fst_3275_);
v___x_3281_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_snd_3276_, v_head_3277_, v___x_3256_);
lean_dec(v_snd_3276_);
v_next_3248_ = v___x_3281_;
v_rest_3249_ = v_tail_3278_;
goto _start;
}
else
{
lean_dec(v_snd_3276_);
v_next_3248_ = v_fst_3275_;
v_rest_3249_ = v_tail_3278_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3285_; lean_object* v___x_3287_; uint8_t v_isShared_3288_; uint8_t v_isSharedCheck_3292_; 
lean_dec(v_next_3248_);
v_a_3285_ = lean_ctor_get(v___x_3258_, 0);
v_isSharedCheck_3292_ = !lean_is_exclusive(v___x_3258_);
if (v_isSharedCheck_3292_ == 0)
{
v___x_3287_ = v___x_3258_;
v_isShared_3288_ = v_isSharedCheck_3292_;
goto v_resetjp_3286_;
}
else
{
lean_inc(v_a_3285_);
lean_dec(v___x_3258_);
v___x_3287_ = lean_box(0);
v_isShared_3288_ = v_isSharedCheck_3292_;
goto v_resetjp_3286_;
}
v_resetjp_3286_:
{
lean_object* v___x_3290_; 
if (v_isShared_3288_ == 0)
{
v___x_3290_ = v___x_3287_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3291_; 
v_reuseFailAlloc_3291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3291_, 0, v_a_3285_);
v___x_3290_ = v_reuseFailAlloc_3291_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
return v___x_3290_;
}
}
}
}
else
{
lean_object* v___x_3293_; lean_object* v___x_3294_; 
lean_dec(v_next_3248_);
v___x_3293_ = lean_box(0);
v___x_3294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3294_, 0, v___x_3293_);
return v___x_3294_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg___boxed(lean_object* v_next_3295_, lean_object* v_rest_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_, lean_object* v_a_3302_){
_start:
{
lean_object* v_res_3303_; 
v_res_3303_ = l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg(v_next_3295_, v_rest_3296_, v_a_3297_, v_a_3298_, v_a_3299_, v_a_3300_, v_a_3301_);
lean_dec(v_a_3301_);
lean_dec_ref(v_a_3300_);
lean_dec(v_a_3299_);
lean_dec_ref(v_a_3298_);
lean_dec(v_a_3297_);
lean_dec(v_rest_3296_);
return v_res_3303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux(lean_object* v_00_u03b1_3304_, lean_object* v_next_3305_, lean_object* v_rest_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_, lean_object* v_a_3311_){
_start:
{
lean_object* v___x_3313_; 
v___x_3313_ = l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg(v_next_3305_, v_rest_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_);
return v___x_3313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux___boxed(lean_object* v_00_u03b1_3314_, lean_object* v_next_3315_, lean_object* v_rest_3316_, lean_object* v_a_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_, lean_object* v_a_3322_){
_start:
{
lean_object* v_res_3323_; 
v_res_3323_ = l_Lean_Meta_LazyDiscrTree_dropKeyAux(v_00_u03b1_3314_, v_next_3315_, v_rest_3316_, v_a_3317_, v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_);
lean_dec(v_a_3321_);
lean_dec_ref(v_a_3320_);
lean_dec(v_a_3319_);
lean_dec_ref(v_a_3318_);
lean_dec(v_a_3317_);
lean_dec(v_rest_3316_);
return v_res_3323_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0(lean_object* v_00_u03b2_3324_, lean_object* v_m_3325_, lean_object* v_a_3326_, lean_object* v_fallback_3327_){
_start:
{
lean_object* v___x_3328_; 
v___x_3328_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_m_3325_, v_a_3326_, v_fallback_3327_);
return v___x_3328_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___boxed(lean_object* v_00_u03b2_3329_, lean_object* v_m_3330_, lean_object* v_a_3331_, lean_object* v_fallback_3332_){
_start:
{
lean_object* v_res_3333_; 
v_res_3333_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0(v_00_u03b2_3329_, v_m_3330_, v_a_3331_, v_fallback_3332_);
lean_dec(v_fallback_3332_);
lean_dec(v_a_3331_);
lean_dec_ref(v_m_3330_);
return v_res_3333_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0(lean_object* v_00_u03b2_3334_, lean_object* v_a_3335_, lean_object* v_fallback_3336_, lean_object* v_x_3337_){
_start:
{
lean_object* v___x_3338_; 
v___x_3338_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(v_a_3335_, v_fallback_3336_, v_x_3337_);
return v___x_3338_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3339_, lean_object* v_a_3340_, lean_object* v_fallback_3341_, lean_object* v_x_3342_){
_start:
{
lean_object* v_res_3343_; 
v_res_3343_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0(v_00_u03b2_3339_, v_a_3340_, v_fallback_3341_, v_x_3342_);
lean_dec(v_x_3342_);
lean_dec(v_fallback_3341_);
lean_dec(v_a_3340_);
return v_res_3343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey___redArg(lean_object* v_t_3344_, lean_object* v_path_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_){
_start:
{
if (lean_obj_tag(v_path_3345_) == 0)
{
lean_object* v___x_3351_; 
v___x_3351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3351_, 0, v_t_3344_);
return v___x_3351_;
}
else
{
lean_object* v_head_3352_; lean_object* v_tail_3353_; lean_object* v_roots_3354_; lean_object* v___x_3355_; lean_object* v_idx_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; 
v_head_3352_ = lean_ctor_get(v_path_3345_, 0);
lean_inc(v_head_3352_);
v_tail_3353_ = lean_ctor_get(v_path_3345_, 1);
lean_inc(v_tail_3353_);
lean_dec_ref_known(v_path_3345_, 2);
v_roots_3354_ = lean_ctor_get(v_t_3344_, 1);
v___x_3355_ = lean_unsigned_to_nat(0u);
v_idx_3356_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_roots_3354_, v_head_3352_, v___x_3355_);
lean_dec(v_head_3352_);
v___x_3357_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_dropKeyAux___boxed), 9, 3);
lean_closure_set(v___x_3357_, 0, lean_box(0));
lean_closure_set(v___x_3357_, 1, v_idx_3356_);
lean_closure_set(v___x_3357_, 2, v_tail_3353_);
v___x_3358_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_t_3344_, v___x_3357_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_);
if (lean_obj_tag(v___x_3358_) == 0)
{
lean_object* v_a_3359_; lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3367_; 
v_a_3359_ = lean_ctor_get(v___x_3358_, 0);
v_isSharedCheck_3367_ = !lean_is_exclusive(v___x_3358_);
if (v_isSharedCheck_3367_ == 0)
{
v___x_3361_ = v___x_3358_;
v_isShared_3362_ = v_isSharedCheck_3367_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_a_3359_);
lean_dec(v___x_3358_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3367_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
lean_object* v_snd_3363_; lean_object* v___x_3365_; 
v_snd_3363_ = lean_ctor_get(v_a_3359_, 1);
lean_inc(v_snd_3363_);
lean_dec(v_a_3359_);
if (v_isShared_3362_ == 0)
{
lean_ctor_set(v___x_3361_, 0, v_snd_3363_);
v___x_3365_ = v___x_3361_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3366_; 
v_reuseFailAlloc_3366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3366_, 0, v_snd_3363_);
v___x_3365_ = v_reuseFailAlloc_3366_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
return v___x_3365_;
}
}
}
else
{
lean_object* v_a_3368_; lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3375_; 
v_a_3368_ = lean_ctor_get(v___x_3358_, 0);
v_isSharedCheck_3375_ = !lean_is_exclusive(v___x_3358_);
if (v_isSharedCheck_3375_ == 0)
{
v___x_3370_ = v___x_3358_;
v_isShared_3371_ = v_isSharedCheck_3375_;
goto v_resetjp_3369_;
}
else
{
lean_inc(v_a_3368_);
lean_dec(v___x_3358_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3375_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
lean_object* v___x_3373_; 
if (v_isShared_3371_ == 0)
{
v___x_3373_ = v___x_3370_;
goto v_reusejp_3372_;
}
else
{
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3374_, 0, v_a_3368_);
v___x_3373_ = v_reuseFailAlloc_3374_;
goto v_reusejp_3372_;
}
v_reusejp_3372_:
{
return v___x_3373_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey___redArg___boxed(lean_object* v_t_3376_, lean_object* v_path_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_){
_start:
{
lean_object* v_res_3383_; 
v_res_3383_ = l_Lean_Meta_LazyDiscrTree_dropKey___redArg(v_t_3376_, v_path_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_);
lean_dec(v_a_3381_);
lean_dec_ref(v_a_3380_);
lean_dec(v_a_3379_);
lean_dec_ref(v_a_3378_);
return v_res_3383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey(lean_object* v_00_u03b1_3384_, lean_object* v_t_3385_, lean_object* v_path_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_){
_start:
{
lean_object* v___x_3392_; 
v___x_3392_ = l_Lean_Meta_LazyDiscrTree_dropKey___redArg(v_t_3385_, v_path_3386_, v_a_3387_, v_a_3388_, v_a_3389_, v_a_3390_);
return v___x_3392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey___boxed(lean_object* v_00_u03b1_3393_, lean_object* v_t_3394_, lean_object* v_path_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_){
_start:
{
lean_object* v_res_3401_; 
v_res_3401_ = l_Lean_Meta_LazyDiscrTree_dropKey(v_00_u03b1_3393_, v_t_3394_, v_path_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_);
lean_dec(v_a_3399_);
lean_dec_ref(v_a_3398_);
lean_dec(v_a_3397_);
lean_dec_ref(v_a_3396_);
return v_res_3401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(lean_object* v_score_3404_, lean_object* v_e_3405_, lean_object* v_a_3406_){
_start:
{
lean_object* v___x_3407_; uint8_t v___x_3408_; 
v___x_3407_ = lean_array_get_size(v_a_3406_);
v___x_3408_ = lean_nat_dec_lt(v___x_3407_, v_score_3404_);
if (v___x_3408_ == 0)
{
lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; 
v___x_3409_ = lean_unsigned_to_nat(1u);
v___x_3410_ = lean_mk_empty_array_with_capacity(v___x_3409_);
v___x_3411_ = lean_array_push(v___x_3410_, v_e_3405_);
v___x_3412_ = lean_array_push(v_a_3406_, v___x_3411_);
return v___x_3412_;
}
else
{
lean_object* v___x_3413_; lean_object* v___x_3414_; 
v___x_3413_ = ((lean_object*)(l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg___closed__0));
v___x_3414_ = lean_array_push(v_a_3406_, v___x_3413_);
v_a_3406_ = v___x_3414_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg___boxed(lean_object* v_score_3416_, lean_object* v_e_3417_, lean_object* v_a_3418_){
_start:
{
lean_object* v_res_3419_; 
v_res_3419_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(v_score_3416_, v_e_3417_, v_a_3418_);
lean_dec(v_score_3416_);
return v_res_3419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop(lean_object* v_00_u03b1_3420_, lean_object* v_score_3421_, lean_object* v_e_3422_, lean_object* v_a_3423_){
_start:
{
lean_object* v___x_3424_; 
v___x_3424_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(v_score_3421_, v_e_3422_, v_a_3423_);
return v___x_3424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___boxed(lean_object* v_00_u03b1_3425_, lean_object* v_score_3426_, lean_object* v_e_3427_, lean_object* v_a_3428_){
_start:
{
lean_object* v_res_3429_; 
v_res_3429_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop(v_00_u03b1_3425_, v_score_3426_, v_e_3427_, v_a_3428_);
lean_dec(v_score_3426_);
return v_res_3429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(lean_object* v_r_3430_, lean_object* v_score_3431_, lean_object* v_e_3432_){
_start:
{
lean_object* v___x_3433_; lean_object* v___x_3434_; uint8_t v___x_3435_; 
v___x_3433_ = lean_array_get_size(v_e_3432_);
v___x_3434_ = lean_unsigned_to_nat(0u);
v___x_3435_ = lean_nat_dec_eq(v___x_3433_, v___x_3434_);
if (v___x_3435_ == 0)
{
lean_object* v___x_3436_; uint8_t v___x_3437_; 
v___x_3436_ = lean_array_get_size(v_r_3430_);
v___x_3437_ = lean_nat_dec_lt(v_score_3431_, v___x_3436_);
if (v___x_3437_ == 0)
{
lean_object* v___x_3438_; 
v___x_3438_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(v_score_3431_, v_e_3432_, v_r_3430_);
return v___x_3438_;
}
else
{
lean_object* v_v_3439_; lean_object* v___x_3440_; lean_object* v_xs_x27_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; 
v_v_3439_ = lean_array_fget(v_r_3430_, v_score_3431_);
v___x_3440_ = lean_box(0);
v_xs_x27_3441_ = lean_array_fset(v_r_3430_, v_score_3431_, v___x_3440_);
v___x_3442_ = lean_array_push(v_v_3439_, v_e_3432_);
v___x_3443_ = lean_array_fset(v_xs_x27_3441_, v_score_3431_, v___x_3442_);
return v___x_3443_;
}
}
else
{
lean_dec_ref(v_e_3432_);
return v_r_3430_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg___boxed(lean_object* v_r_3444_, lean_object* v_score_3445_, lean_object* v_e_3446_){
_start:
{
lean_object* v_res_3447_; 
v_res_3447_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v_r_3444_, v_score_3445_, v_e_3446_);
lean_dec(v_score_3445_);
return v_res_3447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push(lean_object* v_00_u03b1_3448_, lean_object* v_r_3449_, lean_object* v_score_3450_, lean_object* v_e_3451_){
_start:
{
lean_object* v___x_3452_; 
v___x_3452_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v_r_3449_, v_score_3450_, v_e_3451_);
return v___x_3452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push___boxed(lean_object* v_00_u03b1_3453_, lean_object* v_r_3454_, lean_object* v_score_3455_, lean_object* v_e_3456_){
_start:
{
lean_object* v_res_3457_; 
v_res_3457_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push(v_00_u03b1_3453_, v_r_3454_, v_score_3455_, v_e_3456_);
lean_dec(v_score_3455_);
return v_res_3457_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(lean_object* v_as_3458_, size_t v_i_3459_, size_t v_stop_3460_, lean_object* v_b_3461_){
_start:
{
uint8_t v___x_3462_; 
v___x_3462_ = lean_usize_dec_eq(v_i_3459_, v_stop_3460_);
if (v___x_3462_ == 0)
{
lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; size_t v___x_3466_; size_t v___x_3467_; 
v___x_3463_ = lean_array_uget_borrowed(v_as_3458_, v_i_3459_);
v___x_3464_ = lean_array_get_size(v___x_3463_);
v___x_3465_ = lean_nat_add(v_b_3461_, v___x_3464_);
lean_dec(v_b_3461_);
v___x_3466_ = ((size_t)1ULL);
v___x_3467_ = lean_usize_add(v_i_3459_, v___x_3466_);
v_i_3459_ = v___x_3467_;
v_b_3461_ = v___x_3465_;
goto _start;
}
else
{
return v_b_3461_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg___boxed(lean_object* v_as_3469_, lean_object* v_i_3470_, lean_object* v_stop_3471_, lean_object* v_b_3472_){
_start:
{
size_t v_i_boxed_3473_; size_t v_stop_boxed_3474_; lean_object* v_res_3475_; 
v_i_boxed_3473_ = lean_unbox_usize(v_i_3470_);
lean_dec(v_i_3470_);
v_stop_boxed_3474_ = lean_unbox_usize(v_stop_3471_);
lean_dec(v_stop_3471_);
v_res_3475_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v_as_3469_, v_i_boxed_3473_, v_stop_boxed_3474_, v_b_3472_);
lean_dec_ref(v_as_3469_);
return v_res_3475_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(lean_object* v_as_3476_, size_t v_i_3477_, size_t v_stop_3478_, lean_object* v_b_3479_){
_start:
{
lean_object* v___y_3481_; uint8_t v___x_3485_; 
v___x_3485_ = lean_usize_dec_eq(v_i_3477_, v_stop_3478_);
if (v___x_3485_ == 0)
{
lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; uint8_t v___x_3489_; 
v___x_3486_ = lean_array_uget_borrowed(v_as_3476_, v_i_3477_);
v___x_3487_ = lean_unsigned_to_nat(0u);
v___x_3488_ = lean_array_get_size(v___x_3486_);
v___x_3489_ = lean_nat_dec_lt(v___x_3487_, v___x_3488_);
if (v___x_3489_ == 0)
{
v___y_3481_ = v_b_3479_;
goto v___jp_3480_;
}
else
{
size_t v___x_3490_; size_t v___x_3491_; lean_object* v___x_3492_; 
v___x_3490_ = ((size_t)0ULL);
v___x_3491_ = lean_usize_of_nat(v___x_3488_);
v___x_3492_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v___x_3486_, v___x_3490_, v___x_3491_, v_b_3479_);
v___y_3481_ = v___x_3492_;
goto v___jp_3480_;
}
}
else
{
return v_b_3479_;
}
v___jp_3480_:
{
size_t v___x_3482_; size_t v___x_3483_; 
v___x_3482_ = ((size_t)1ULL);
v___x_3483_ = lean_usize_add(v_i_3477_, v___x_3482_);
v_i_3477_ = v___x_3483_;
v_b_3479_ = v___y_3481_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg___boxed(lean_object* v_as_3493_, lean_object* v_i_3494_, lean_object* v_stop_3495_, lean_object* v_b_3496_){
_start:
{
size_t v_i_boxed_3497_; size_t v_stop_boxed_3498_; lean_object* v_res_3499_; 
v_i_boxed_3497_ = lean_unbox_usize(v_i_3494_);
lean_dec(v_i_3494_);
v_stop_boxed_3498_ = lean_unbox_usize(v_stop_3495_);
lean_dec(v_stop_3495_);
v_res_3499_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_as_3493_, v_i_boxed_3497_, v_stop_boxed_3498_, v_b_3496_);
lean_dec_ref(v_as_3493_);
return v_res_3499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(lean_object* v_mr_3500_){
_start:
{
lean_object* v___x_3501_; lean_object* v___x_3502_; uint8_t v___x_3503_; 
v___x_3501_ = lean_unsigned_to_nat(0u);
v___x_3502_ = lean_array_get_size(v_mr_3500_);
v___x_3503_ = lean_nat_dec_lt(v___x_3501_, v___x_3502_);
if (v___x_3503_ == 0)
{
return v___x_3501_;
}
else
{
size_t v___x_3504_; size_t v___x_3505_; lean_object* v___x_3506_; 
v___x_3504_ = ((size_t)0ULL);
v___x_3505_ = lean_usize_of_nat(v___x_3502_);
v___x_3506_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_mr_3500_, v___x_3504_, v___x_3505_, v___x_3501_);
return v___x_3506_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg___boxed(lean_object* v_mr_3507_){
_start:
{
lean_object* v_res_3508_; 
v_res_3508_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_mr_3507_);
lean_dec_ref(v_mr_3507_);
return v_res_3508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size(lean_object* v_00_u03b1_3509_, lean_object* v_mr_3510_){
_start:
{
lean_object* v___x_3511_; 
v___x_3511_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_mr_3510_);
return v___x_3511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size___boxed(lean_object* v_00_u03b1_3512_, lean_object* v_mr_3513_){
_start:
{
lean_object* v_res_3514_; 
v_res_3514_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size(v_00_u03b1_3512_, v_mr_3513_);
lean_dec_ref(v_mr_3513_);
return v_res_3514_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0(lean_object* v_00_u03b1_3515_, lean_object* v_as_3516_, size_t v_i_3517_, size_t v_stop_3518_, lean_object* v_b_3519_){
_start:
{
lean_object* v___x_3520_; 
v___x_3520_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v_as_3516_, v_i_3517_, v_stop_3518_, v_b_3519_);
return v___x_3520_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___boxed(lean_object* v_00_u03b1_3521_, lean_object* v_as_3522_, lean_object* v_i_3523_, lean_object* v_stop_3524_, lean_object* v_b_3525_){
_start:
{
size_t v_i_boxed_3526_; size_t v_stop_boxed_3527_; lean_object* v_res_3528_; 
v_i_boxed_3526_ = lean_unbox_usize(v_i_3523_);
lean_dec(v_i_3523_);
v_stop_boxed_3527_ = lean_unbox_usize(v_stop_3524_);
lean_dec(v_stop_3524_);
v_res_3528_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0(v_00_u03b1_3521_, v_as_3522_, v_i_boxed_3526_, v_stop_boxed_3527_, v_b_3525_);
lean_dec_ref(v_as_3522_);
return v_res_3528_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1(lean_object* v_00_u03b1_3529_, lean_object* v_as_3530_, size_t v_i_3531_, size_t v_stop_3532_, lean_object* v_b_3533_){
_start:
{
lean_object* v___x_3534_; 
v___x_3534_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_as_3530_, v_i_3531_, v_stop_3532_, v_b_3533_);
return v___x_3534_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___boxed(lean_object* v_00_u03b1_3535_, lean_object* v_as_3536_, lean_object* v_i_3537_, lean_object* v_stop_3538_, lean_object* v_b_3539_){
_start:
{
size_t v_i_boxed_3540_; size_t v_stop_boxed_3541_; lean_object* v_res_3542_; 
v_i_boxed_3540_ = lean_unbox_usize(v_i_3537_);
lean_dec(v_i_3537_);
v_stop_boxed_3541_ = lean_unbox_usize(v_stop_3538_);
lean_dec(v_stop_3538_);
v_res_3542_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1(v_00_u03b1_3535_, v_as_3536_, v_i_boxed_3540_, v_stop_boxed_3541_, v_b_3539_);
lean_dec_ref(v_as_3536_);
return v_res_3542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__0(lean_object* v_f_3543_, lean_object* v_j_3544_, lean_object* v_x_3545_){
_start:
{
lean_object* v___x_3546_; 
v___x_3546_ = lean_apply_2(v_f_3543_, v_j_3544_, v_x_3545_);
return v___x_3546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1(lean_object* v___f_3566_, lean_object* v_x1_3567_, lean_object* v_x2_3568_){
_start:
{
lean_object* v___x_3569_; size_t v_sz_3570_; size_t v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; 
v___x_3569_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__9));
v_sz_3570_ = lean_array_size(v_x2_3568_);
v___x_3571_ = ((size_t)0ULL);
v___x_3572_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3569_, v___f_3566_, v_sz_3570_, v___x_3571_, v_x2_3568_);
v___x_3573_ = l_Array_append___redArg(v_x1_3567_, v___x_3572_);
lean_dec(v___x_3572_);
return v___x_3573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2(lean_object* v_n_3574_, lean_object* v_mr_3575_, lean_object* v_f_3576_, lean_object* v_i_3577_, lean_object* v_x_3578_, lean_object* v_r_3579_){
_start:
{
lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v_j_3582_; lean_object* v_b_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; uint8_t v___x_3587_; 
v___x_3580_ = lean_unsigned_to_nat(1u);
v___x_3581_ = lean_nat_sub(v_n_3574_, v___x_3580_);
v_j_3582_ = lean_nat_sub(v___x_3581_, v_i_3577_);
lean_dec(v___x_3581_);
v_b_3583_ = lean_array_fget_borrowed(v_mr_3575_, v_j_3582_);
v___x_3584_ = lean_unsigned_to_nat(0u);
v___x_3585_ = lean_array_get_size(v_b_3583_);
v___x_3586_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__9));
v___x_3587_ = lean_nat_dec_lt(v___x_3584_, v___x_3585_);
if (v___x_3587_ == 0)
{
lean_dec(v_j_3582_);
lean_dec(v_f_3576_);
return v_r_3579_;
}
else
{
lean_object* v___f_3588_; lean_object* v___f_3589_; size_t v___x_3590_; size_t v___x_3591_; lean_object* v___x_3592_; 
v___f_3588_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3588_, 0, v_f_3576_);
lean_closure_set(v___f_3588_, 1, v_j_3582_);
v___f_3589_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1), 3, 1);
lean_closure_set(v___f_3589_, 0, v___f_3588_);
v___x_3590_ = ((size_t)0ULL);
v___x_3591_ = lean_usize_of_nat(v___x_3585_);
lean_inc(v_b_3583_);
v___x_3592_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3586_, v___f_3589_, v_b_3583_, v___x_3590_, v___x_3591_, v_r_3579_);
return v___x_3592_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2___boxed(lean_object* v_n_3593_, lean_object* v_mr_3594_, lean_object* v_f_3595_, lean_object* v_i_3596_, lean_object* v_x_3597_, lean_object* v_r_3598_){
_start:
{
lean_object* v_res_3599_; 
v_res_3599_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2(v_n_3593_, v_mr_3594_, v_f_3595_, v_i_3596_, v_x_3597_, v_r_3598_);
lean_dec(v_i_3596_);
lean_dec_ref(v_mr_3594_);
lean_dec(v_n_3593_);
return v_res_3599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg(lean_object* v_mr_3600_, lean_object* v_a_3601_, lean_object* v_f_3602_){
_start:
{
lean_object* v_n_3603_; lean_object* v___f_3604_; lean_object* v___x_3605_; 
v_n_3603_ = lean_array_get_size(v_mr_3600_);
v___f_3604_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_3604_, 0, v_n_3603_);
lean_closure_set(v___f_3604_, 1, v_mr_3600_);
lean_closure_set(v___f_3604_, 2, v_f_3602_);
v___x_3605_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop(lean_box(0), v_n_3603_, v___f_3604_, v_n_3603_, lean_box(0), v_a_3601_);
return v___x_3605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux(lean_object* v_00_u03b1_3606_, lean_object* v_00_u03b2_3607_, lean_object* v_mr_3608_, lean_object* v_a_3609_, lean_object* v_f_3610_){
_start:
{
lean_object* v___x_3611_; 
v___x_3611_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg(v_mr_3608_, v_a_3609_, v_f_3610_);
return v___x_3611_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(size_t v_sz_3612_, size_t v_i_3613_, lean_object* v_bs_3614_){
_start:
{
uint8_t v___x_3615_; 
v___x_3615_ = lean_usize_dec_lt(v_i_3613_, v_sz_3612_);
if (v___x_3615_ == 0)
{
return v_bs_3614_;
}
else
{
lean_object* v_v_3616_; lean_object* v___x_3617_; lean_object* v_bs_x27_3618_; size_t v___x_3619_; size_t v___x_3620_; lean_object* v___x_3621_; 
v_v_3616_ = lean_array_uget(v_bs_3614_, v_i_3613_);
v___x_3617_ = lean_unsigned_to_nat(0u);
v_bs_x27_3618_ = lean_array_uset(v_bs_3614_, v_i_3613_, v___x_3617_);
v___x_3619_ = ((size_t)1ULL);
v___x_3620_ = lean_usize_add(v_i_3613_, v___x_3619_);
v___x_3621_ = lean_array_uset(v_bs_x27_3618_, v_i_3613_, v_v_3616_);
v_i_3613_ = v___x_3620_;
v_bs_3614_ = v___x_3621_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg___boxed(lean_object* v_sz_3623_, lean_object* v_i_3624_, lean_object* v_bs_3625_){
_start:
{
size_t v_sz_boxed_3626_; size_t v_i_boxed_3627_; lean_object* v_res_3628_; 
v_sz_boxed_3626_ = lean_unbox_usize(v_sz_3623_);
lean_dec(v_sz_3623_);
v_i_boxed_3627_ = lean_unbox_usize(v_i_3624_);
lean_dec(v_i_3624_);
v_res_3628_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(v_sz_boxed_3626_, v_i_boxed_3627_, v_bs_3625_);
return v_res_3628_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(lean_object* v_as_3629_, size_t v_i_3630_, size_t v_stop_3631_, lean_object* v_b_3632_){
_start:
{
uint8_t v___x_3633_; 
v___x_3633_ = lean_usize_dec_eq(v_i_3630_, v_stop_3631_);
if (v___x_3633_ == 0)
{
lean_object* v___x_3634_; size_t v_sz_3635_; size_t v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; size_t v___x_3639_; size_t v___x_3640_; 
v___x_3634_ = lean_array_uget_borrowed(v_as_3629_, v_i_3630_);
v_sz_3635_ = lean_array_size(v___x_3634_);
v___x_3636_ = ((size_t)0ULL);
lean_inc(v___x_3634_);
v___x_3637_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(v_sz_3635_, v___x_3636_, v___x_3634_);
v___x_3638_ = l_Array_append___redArg(v_b_3632_, v___x_3637_);
lean_dec_ref(v___x_3637_);
v___x_3639_ = ((size_t)1ULL);
v___x_3640_ = lean_usize_add(v_i_3630_, v___x_3639_);
v_i_3630_ = v___x_3640_;
v_b_3632_ = v___x_3638_;
goto _start;
}
else
{
return v_b_3632_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg___boxed(lean_object* v_as_3642_, lean_object* v_i_3643_, lean_object* v_stop_3644_, lean_object* v_b_3645_){
_start:
{
size_t v_i_boxed_3646_; size_t v_stop_boxed_3647_; lean_object* v_res_3648_; 
v_i_boxed_3646_ = lean_unbox_usize(v_i_3643_);
lean_dec(v_i_3643_);
v_stop_boxed_3647_ = lean_unbox_usize(v_stop_3644_);
lean_dec(v_stop_3644_);
v_res_3648_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(v_as_3642_, v_i_boxed_3646_, v_stop_boxed_3647_, v_b_3645_);
lean_dec_ref(v_as_3642_);
return v_res_3648_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(lean_object* v_n_3649_, lean_object* v_aa_3650_, lean_object* v_n_3651_, lean_object* v_j_3652_, lean_object* v_a_3653_){
_start:
{
lean_object* v_zero_3654_; uint8_t v_isZero_3655_; 
v_zero_3654_ = lean_unsigned_to_nat(0u);
v_isZero_3655_ = lean_nat_dec_eq(v_j_3652_, v_zero_3654_);
if (v_isZero_3655_ == 1)
{
lean_dec(v_j_3652_);
return v_a_3653_;
}
else
{
lean_object* v_one_3656_; lean_object* v_n_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v_j_3660_; lean_object* v_b_3661_; lean_object* v___x_3662_; uint8_t v___x_3663_; 
v_one_3656_ = lean_unsigned_to_nat(1u);
v_n_3657_ = lean_nat_sub(v_j_3652_, v_one_3656_);
v___x_3658_ = lean_nat_sub(v_n_3651_, v_j_3652_);
lean_dec(v_j_3652_);
v___x_3659_ = lean_nat_sub(v_n_3649_, v_one_3656_);
v_j_3660_ = lean_nat_sub(v___x_3659_, v___x_3658_);
lean_dec(v___x_3658_);
lean_dec(v___x_3659_);
v_b_3661_ = lean_array_fget_borrowed(v_aa_3650_, v_j_3660_);
lean_dec(v_j_3660_);
v___x_3662_ = lean_array_get_size(v_b_3661_);
v___x_3663_ = lean_nat_dec_lt(v_zero_3654_, v___x_3662_);
if (v___x_3663_ == 0)
{
v_j_3652_ = v_n_3657_;
goto _start;
}
else
{
size_t v___x_3665_; size_t v___x_3666_; lean_object* v___x_3667_; 
v___x_3665_ = ((size_t)0ULL);
v___x_3666_ = lean_usize_of_nat(v___x_3662_);
v___x_3667_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(v_b_3661_, v___x_3665_, v___x_3666_, v_a_3653_);
v_j_3652_ = v_n_3657_;
v_a_3653_ = v___x_3667_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg___boxed(lean_object* v_n_3669_, lean_object* v_aa_3670_, lean_object* v_n_3671_, lean_object* v_j_3672_, lean_object* v_a_3673_){
_start:
{
lean_object* v_res_3674_; 
v_res_3674_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(v_n_3669_, v_aa_3670_, v_n_3671_, v_j_3672_, v_a_3673_);
lean_dec(v_n_3671_);
lean_dec_ref(v_aa_3670_);
lean_dec(v_n_3669_);
return v_res_3674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(lean_object* v_mr_3675_, lean_object* v_a_3676_){
_start:
{
lean_object* v_n_3677_; lean_object* v___x_3678_; 
v_n_3677_ = lean_array_get_size(v_mr_3675_);
v___x_3678_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(v_n_3677_, v_mr_3675_, v_n_3677_, v_n_3677_, v_a_3676_);
return v___x_3678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg___boxed(lean_object* v_mr_3679_, lean_object* v_a_3680_){
_start:
{
lean_object* v_res_3681_; 
v_res_3681_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3679_, v_a_3680_);
lean_dec_ref(v_mr_3679_);
return v_res_3681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___redArg(lean_object* v_mr_3682_, lean_object* v_a_3683_){
_start:
{
lean_object* v___x_3684_; 
v___x_3684_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3682_, v_a_3683_);
return v___x_3684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___redArg___boxed(lean_object* v_mr_3685_, lean_object* v_a_3686_){
_start:
{
lean_object* v_res_3687_; 
v_res_3687_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___redArg(v_mr_3685_, v_a_3686_);
lean_dec_ref(v_mr_3685_);
return v_res_3687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults(lean_object* v_00_u03b1_3688_, lean_object* v_mr_3689_, lean_object* v_a_3690_){
_start:
{
lean_object* v___x_3691_; 
v___x_3691_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3689_, v_a_3690_);
return v___x_3691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___boxed(lean_object* v_00_u03b1_3692_, lean_object* v_mr_3693_, lean_object* v_a_3694_){
_start:
{
lean_object* v_res_3695_; 
v_res_3695_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults(v_00_u03b1_3692_, v_mr_3693_, v_a_3694_);
lean_dec_ref(v_mr_3693_);
return v_res_3695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0(lean_object* v_00_u03b1_3696_, lean_object* v_mr_3697_, lean_object* v_a_3698_){
_start:
{
lean_object* v___x_3699_; 
v___x_3699_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3697_, v_a_3698_);
return v___x_3699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___boxed(lean_object* v_00_u03b1_3700_, lean_object* v_mr_3701_, lean_object* v_a_3702_){
_start:
{
lean_object* v_res_3703_; 
v_res_3703_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0(v_00_u03b1_3700_, v_mr_3701_, v_a_3702_);
lean_dec_ref(v_mr_3701_);
return v_res_3703_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0(lean_object* v_00_u03b1_3704_, size_t v_sz_3705_, size_t v_i_3706_, lean_object* v_bs_3707_){
_start:
{
lean_object* v___x_3708_; 
v___x_3708_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(v_sz_3705_, v_i_3706_, v_bs_3707_);
return v___x_3708_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3709_, lean_object* v_sz_3710_, lean_object* v_i_3711_, lean_object* v_bs_3712_){
_start:
{
size_t v_sz_boxed_3713_; size_t v_i_boxed_3714_; lean_object* v_res_3715_; 
v_sz_boxed_3713_ = lean_unbox_usize(v_sz_3710_);
lean_dec(v_sz_3710_);
v_i_boxed_3714_ = lean_unbox_usize(v_i_3711_);
lean_dec(v_i_3711_);
v_res_3715_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0(v_00_u03b1_3709_, v_sz_boxed_3713_, v_i_boxed_3714_, v_bs_3712_);
return v_res_3715_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1(lean_object* v_00_u03b1_3716_, lean_object* v_as_3717_, size_t v_i_3718_, size_t v_stop_3719_, lean_object* v_b_3720_){
_start:
{
lean_object* v___x_3721_; 
v___x_3721_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(v_as_3717_, v_i_3718_, v_stop_3719_, v_b_3720_);
return v___x_3721_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3722_, lean_object* v_as_3723_, lean_object* v_i_3724_, lean_object* v_stop_3725_, lean_object* v_b_3726_){
_start:
{
size_t v_i_boxed_3727_; size_t v_stop_boxed_3728_; lean_object* v_res_3729_; 
v_i_boxed_3727_ = lean_unbox_usize(v_i_3724_);
lean_dec(v_i_3724_);
v_stop_boxed_3728_ = lean_unbox_usize(v_stop_3725_);
lean_dec(v_stop_3725_);
v_res_3729_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1(v_00_u03b1_3722_, v_as_3723_, v_i_boxed_3727_, v_stop_boxed_3728_, v_b_3726_);
lean_dec_ref(v_as_3723_);
return v_res_3729_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2(lean_object* v_00_u03b1_3730_, lean_object* v_n_3731_, lean_object* v_aa_3732_, lean_object* v_n_3733_, lean_object* v_j_3734_, lean_object* v_a_3735_, lean_object* v_a_3736_){
_start:
{
lean_object* v___x_3737_; 
v___x_3737_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(v_n_3731_, v_aa_3732_, v_n_3733_, v_j_3734_, v_a_3736_);
return v___x_3737_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___boxed(lean_object* v_00_u03b1_3738_, lean_object* v_n_3739_, lean_object* v_aa_3740_, lean_object* v_n_3741_, lean_object* v_j_3742_, lean_object* v_a_3743_, lean_object* v_a_3744_){
_start:
{
lean_object* v_res_3745_; 
v_res_3745_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2(v_00_u03b1_3738_, v_n_3739_, v_aa_3740_, v_n_3741_, v_j_3742_, v_a_3743_, v_a_3744_);
lean_dec(v_n_3741_);
lean_dec_ref(v_aa_3740_);
lean_dec(v_n_3739_);
return v_res_3745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0(lean_object* v_snd_3753_, lean_object* v___x_3754_, lean_object* v_score_3755_, lean_object* v___x_3756_, lean_object* v_k_3757_, lean_object* v_args_3758_, lean_object* v_cases_3759_){
_start:
{
lean_object* v___x_3760_; 
v___x_3760_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_snd_3753_, v_k_3757_);
if (lean_obj_tag(v___x_3760_) == 0)
{
lean_dec_ref(v___x_3754_);
return v_cases_3759_;
}
else
{
lean_object* v_val_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; 
v_val_3761_ = lean_ctor_get(v___x_3760_, 0);
lean_inc(v_val_3761_);
lean_dec_ref_known(v___x_3760_, 1);
v___x_3762_ = l_Array_append___redArg(v___x_3754_, v_args_3758_);
v___x_3763_ = lean_nat_add(v_score_3755_, v___x_3756_);
v___x_3764_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3764_, 0, v___x_3762_);
lean_ctor_set(v___x_3764_, 1, v___x_3763_);
lean_ctor_set(v___x_3764_, 2, v_val_3761_);
v___x_3765_ = lean_array_push(v_cases_3759_, v___x_3764_);
return v___x_3765_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0___boxed(lean_object* v_snd_3766_, lean_object* v___x_3767_, lean_object* v_score_3768_, lean_object* v___x_3769_, lean_object* v_k_3770_, lean_object* v_args_3771_, lean_object* v_cases_3772_){
_start:
{
lean_object* v_res_3773_; 
v_res_3773_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0(v_snd_3766_, v___x_3767_, v_score_3768_, v___x_3769_, v_k_3770_, v_args_3771_, v_cases_3772_);
lean_dec_ref(v_args_3771_);
lean_dec(v_k_3770_);
lean_dec(v___x_3769_);
lean_dec(v_score_3768_);
lean_dec_ref(v_snd_3766_);
return v_res_3773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(lean_object* v_cases_3774_, lean_object* v_result_3775_, lean_object* v_a_3776_, lean_object* v_a_3777_, lean_object* v_a_3778_, lean_object* v_a_3779_, lean_object* v_a_3780_){
_start:
{
lean_object* v___x_3782_; lean_object* v___x_3783_; uint8_t v___x_3784_; 
v___x_3782_ = lean_array_get_size(v_cases_3774_);
v___x_3783_ = lean_unsigned_to_nat(0u);
v___x_3784_ = lean_nat_dec_eq(v___x_3782_, v___x_3783_);
if (v___x_3784_ == 0)
{
lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v_ca_3788_; lean_object* v_todo_3789_; lean_object* v_score_3790_; lean_object* v_c_3791_; lean_object* v___x_3793_; uint8_t v_isShared_3794_; uint8_t v_isSharedCheck_3857_; 
v___x_3785_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedPartialMatch_default));
v___x_3786_ = lean_unsigned_to_nat(1u);
v___x_3787_ = lean_nat_sub(v___x_3782_, v___x_3786_);
v_ca_3788_ = lean_array_get(v___x_3785_, v_cases_3774_, v___x_3787_);
lean_dec(v___x_3787_);
v_todo_3789_ = lean_ctor_get(v_ca_3788_, 0);
v_score_3790_ = lean_ctor_get(v_ca_3788_, 1);
v_c_3791_ = lean_ctor_get(v_ca_3788_, 2);
v_isSharedCheck_3857_ = !lean_is_exclusive(v_ca_3788_);
if (v_isSharedCheck_3857_ == 0)
{
v___x_3793_ = v_ca_3788_;
v_isShared_3794_ = v_isSharedCheck_3857_;
goto v_resetjp_3792_;
}
else
{
lean_inc(v_c_3791_);
lean_inc(v_score_3790_);
lean_inc(v_todo_3789_);
lean_dec(v_ca_3788_);
v___x_3793_ = lean_box(0);
v_isShared_3794_ = v_isSharedCheck_3857_;
goto v_resetjp_3792_;
}
v_resetjp_3792_:
{
lean_object* v___x_3795_; lean_object* v_cases_3796_; lean_object* v___x_3797_; 
v___x_3795_ = l_Lean_instInhabitedExpr;
v_cases_3796_ = lean_array_pop(v_cases_3774_);
v___x_3797_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_c_3791_, v_a_3776_, v_a_3777_, v_a_3778_, v_a_3779_, v_a_3780_);
lean_dec(v_c_3791_);
if (lean_obj_tag(v___x_3797_) == 0)
{
lean_object* v_a_3798_; lean_object* v___y_3800_; lean_object* v___y_3801_; uint8_t v___y_3802_; lean_object* v___y_3803_; lean_object* v_snd_3826_; lean_object* v_fst_3827_; lean_object* v_fst_3828_; lean_object* v_snd_3829_; lean_object* v___x_3830_; uint8_t v___y_3832_; uint8_t v___x_3842_; 
v_a_3798_ = lean_ctor_get(v___x_3797_, 0);
lean_inc(v_a_3798_);
lean_dec_ref_known(v___x_3797_, 1);
v_snd_3826_ = lean_ctor_get(v_a_3798_, 1);
lean_inc(v_snd_3826_);
v_fst_3827_ = lean_ctor_get(v_a_3798_, 0);
lean_inc(v_fst_3827_);
lean_dec(v_a_3798_);
v_fst_3828_ = lean_ctor_get(v_snd_3826_, 0);
lean_inc(v_fst_3828_);
v_snd_3829_ = lean_ctor_get(v_snd_3826_, 1);
lean_inc(v_snd_3829_);
lean_dec(v_snd_3826_);
v___x_3830_ = lean_array_get_size(v_todo_3789_);
v___x_3842_ = lean_nat_dec_eq(v___x_3830_, v___x_3783_);
if (v___x_3842_ == 0)
{
uint8_t v___x_3843_; 
lean_dec(v_fst_3827_);
v___x_3843_ = lean_nat_dec_eq(v_fst_3828_, v___x_3783_);
if (v___x_3843_ == 0)
{
v___y_3832_ = v___x_3842_;
goto v___jp_3831_;
}
else
{
lean_object* v_size_3844_; uint8_t v___x_3845_; 
v_size_3844_ = lean_ctor_get(v_snd_3829_, 0);
v___x_3845_ = lean_nat_dec_eq(v_size_3844_, v___x_3783_);
if (v___x_3845_ == 0)
{
v___y_3832_ = v___x_3845_;
goto v___jp_3831_;
}
else
{
lean_dec(v_snd_3829_);
lean_dec(v_fst_3828_);
lean_del_object(v___x_3793_);
lean_dec(v_score_3790_);
lean_dec_ref(v_todo_3789_);
v_cases_3774_ = v_cases_3796_;
goto _start;
}
}
}
else
{
lean_object* v___x_3847_; 
lean_dec(v_snd_3829_);
lean_dec(v_fst_3828_);
lean_del_object(v___x_3793_);
lean_dec_ref(v_todo_3789_);
v___x_3847_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v_result_3775_, v_score_3790_, v_fst_3827_);
lean_dec(v_score_3790_);
v_cases_3774_ = v_cases_3796_;
v_result_3775_ = v___x_3847_;
goto _start;
}
v___jp_3799_:
{
uint8_t v___x_3804_; lean_object* v___x_3805_; 
v___x_3804_ = 1;
v___x_3805_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v___y_3800_, v___x_3804_, v___y_3802_, v_a_3777_, v_a_3778_, v_a_3779_, v_a_3780_);
if (lean_obj_tag(v___x_3805_) == 0)
{
lean_object* v_a_3806_; lean_object* v_fst_3807_; 
v_a_3806_ = lean_ctor_get(v___x_3805_, 0);
lean_inc(v_a_3806_);
lean_dec_ref_known(v___x_3805_, 1);
v_fst_3807_ = lean_ctor_get(v_a_3806_, 0);
lean_inc(v_fst_3807_);
switch(lean_obj_tag(v_fst_3807_))
{
case 3:
{
lean_dec(v_a_3806_);
lean_dec_ref(v___y_3801_);
v_cases_3774_ = v___y_3803_;
goto _start;
}
case 5:
{
lean_object* v_snd_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; 
v_snd_3809_ = lean_ctor_get(v_a_3806_, 1);
lean_inc(v_snd_3809_);
lean_dec(v_a_3806_);
v___x_3810_ = lean_box(4);
v___x_3811_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
lean_inc_ref(v___y_3801_);
v___x_3812_ = lean_apply_3(v___y_3801_, v___x_3810_, v___x_3811_, v___y_3803_);
v___x_3813_ = lean_apply_3(v___y_3801_, v_fst_3807_, v_snd_3809_, v___x_3812_);
v_cases_3774_ = v___x_3813_;
goto _start;
}
default: 
{
lean_object* v_snd_3815_; lean_object* v___x_3816_; 
v_snd_3815_ = lean_ctor_get(v_a_3806_, 1);
lean_inc(v_snd_3815_);
lean_dec(v_a_3806_);
v___x_3816_ = lean_apply_3(v___y_3801_, v_fst_3807_, v_snd_3815_, v___y_3803_);
v_cases_3774_ = v___x_3816_;
goto _start;
}
}
}
else
{
lean_object* v_a_3818_; lean_object* v___x_3820_; uint8_t v_isShared_3821_; uint8_t v_isSharedCheck_3825_; 
lean_dec_ref(v___y_3803_);
lean_dec_ref(v___y_3801_);
lean_dec_ref(v_result_3775_);
v_a_3818_ = lean_ctor_get(v___x_3805_, 0);
v_isSharedCheck_3825_ = !lean_is_exclusive(v___x_3805_);
if (v_isSharedCheck_3825_ == 0)
{
v___x_3820_ = v___x_3805_;
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
else
{
lean_inc(v_a_3818_);
lean_dec(v___x_3805_);
v___x_3820_ = lean_box(0);
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
v_resetjp_3819_:
{
lean_object* v___x_3823_; 
if (v_isShared_3821_ == 0)
{
v___x_3823_ = v___x_3820_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v_a_3818_);
v___x_3823_ = v_reuseFailAlloc_3824_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
return v___x_3823_;
}
}
}
}
v___jp_3831_:
{
lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___f_3836_; uint8_t v___x_3837_; 
v___x_3833_ = lean_nat_sub(v___x_3830_, v___x_3786_);
v___x_3834_ = lean_array_get(v___x_3795_, v_todo_3789_, v___x_3833_);
lean_dec(v___x_3833_);
v___x_3835_ = lean_array_pop(v_todo_3789_);
lean_inc(v_score_3790_);
lean_inc_ref(v___x_3835_);
v___f_3836_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0___boxed), 7, 4);
lean_closure_set(v___f_3836_, 0, v_snd_3829_);
lean_closure_set(v___f_3836_, 1, v___x_3835_);
lean_closure_set(v___f_3836_, 2, v_score_3790_);
lean_closure_set(v___f_3836_, 3, v___x_3786_);
v___x_3837_ = lean_nat_dec_eq(v_fst_3828_, v___x_3783_);
if (v___x_3837_ == 0)
{
lean_object* v___x_3839_; 
if (v_isShared_3794_ == 0)
{
lean_ctor_set(v___x_3793_, 2, v_fst_3828_);
lean_ctor_set(v___x_3793_, 0, v___x_3835_);
v___x_3839_ = v___x_3793_;
goto v_reusejp_3838_;
}
else
{
lean_object* v_reuseFailAlloc_3841_; 
v_reuseFailAlloc_3841_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3841_, 0, v___x_3835_);
lean_ctor_set(v_reuseFailAlloc_3841_, 1, v_score_3790_);
lean_ctor_set(v_reuseFailAlloc_3841_, 2, v_fst_3828_);
v___x_3839_ = v_reuseFailAlloc_3841_;
goto v_reusejp_3838_;
}
v_reusejp_3838_:
{
lean_object* v___x_3840_; 
v___x_3840_ = lean_array_push(v_cases_3796_, v___x_3839_);
v___y_3800_ = v___x_3834_;
v___y_3801_ = v___f_3836_;
v___y_3802_ = v___y_3832_;
v___y_3803_ = v___x_3840_;
goto v___jp_3799_;
}
}
else
{
lean_dec_ref(v___x_3835_);
lean_dec(v_fst_3828_);
lean_del_object(v___x_3793_);
lean_dec(v_score_3790_);
v___y_3800_ = v___x_3834_;
v___y_3801_ = v___f_3836_;
v___y_3802_ = v___y_3832_;
v___y_3803_ = v_cases_3796_;
goto v___jp_3799_;
}
}
}
else
{
lean_object* v_a_3849_; lean_object* v___x_3851_; uint8_t v_isShared_3852_; uint8_t v_isSharedCheck_3856_; 
lean_dec_ref(v_cases_3796_);
lean_del_object(v___x_3793_);
lean_dec(v_score_3790_);
lean_dec_ref(v_todo_3789_);
lean_dec_ref(v_result_3775_);
v_a_3849_ = lean_ctor_get(v___x_3797_, 0);
v_isSharedCheck_3856_ = !lean_is_exclusive(v___x_3797_);
if (v_isSharedCheck_3856_ == 0)
{
v___x_3851_ = v___x_3797_;
v_isShared_3852_ = v_isSharedCheck_3856_;
goto v_resetjp_3850_;
}
else
{
lean_inc(v_a_3849_);
lean_dec(v___x_3797_);
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
lean_dec_ref(v_cases_3774_);
v___x_3858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3858_, 0, v_result_3775_);
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
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1(void){
_start:
{
lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; 
v___x_4102_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__0));
v___x_4103_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2);
v___x_4104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4104_, 0, v___x_4103_);
lean_ctor_set(v___x_4104_, 1, v___x_4102_);
return v___x_4104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg(){
_start:
{
lean_object* v___x_4106_; 
v___x_4106_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1);
return v___x_4106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___boxed(lean_object* v___dummy_4107_){
_start:
{
lean_object* v_res_4108_; 
v_res_4108_ = l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg();
return v_res_4108_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0(void){
_start:
{
lean_object* v___x_4109_; 
v___x_4109_ = l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg();
return v___x_4109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default(lean_object* v_00_u03b1_4110_){
_start:
{
lean_object* v___x_4111_; 
v___x_4111_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0);
return v___x_4111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___redArg(){
_start:
{
lean_object* v___x_4113_; 
v___x_4113_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0);
return v___x_4113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___redArg___boxed(lean_object* v___dummy_4114_){
_start:
{
lean_object* v_res_4115_; 
v_res_4115_ = l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___redArg();
return v_res_4115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree(lean_object* v_a_4116_){
_start:
{
lean_object* v___x_4117_; 
v___x_4117_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0);
return v___x_4117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(lean_object* v_d_4118_, lean_object* v_k_4119_, lean_object* v_f_4120_){
_start:
{
lean_object* v_roots_4121_; lean_object* v_tries_4122_; lean_object* v___x_4123_; 
v_roots_4121_ = lean_ctor_get(v_d_4118_, 0);
v_tries_4122_ = lean_ctor_get(v_d_4118_, 1);
v___x_4123_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_roots_4121_, v_k_4119_);
if (lean_obj_tag(v___x_4123_) == 0)
{
lean_object* v___x_4125_; uint8_t v_isShared_4126_; uint8_t v_isSharedCheck_4135_; 
lean_inc_ref(v_tries_4122_);
lean_inc_ref(v_roots_4121_);
v_isSharedCheck_4135_ = !lean_is_exclusive(v_d_4118_);
if (v_isSharedCheck_4135_ == 0)
{
lean_object* v_unused_4136_; lean_object* v_unused_4137_; 
v_unused_4136_ = lean_ctor_get(v_d_4118_, 1);
lean_dec(v_unused_4136_);
v_unused_4137_ = lean_ctor_get(v_d_4118_, 0);
lean_dec(v_unused_4137_);
v___x_4125_ = v_d_4118_;
v_isShared_4126_ = v_isSharedCheck_4135_;
goto v_resetjp_4124_;
}
else
{
lean_dec(v_d_4118_);
v___x_4125_ = lean_box(0);
v_isShared_4126_ = v_isSharedCheck_4135_;
goto v_resetjp_4124_;
}
v_resetjp_4124_:
{
lean_object* v___x_4127_; lean_object* v_roots_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4133_; 
v___x_4127_ = lean_array_get_size(v_tries_4122_);
v_roots_4128_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_roots_4121_, v_k_4119_, v___x_4127_);
v___x_4129_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__3));
v___x_4130_ = lean_apply_1(v_f_4120_, v___x_4129_);
v___x_4131_ = lean_array_push(v_tries_4122_, v___x_4130_);
if (v_isShared_4126_ == 0)
{
lean_ctor_set(v___x_4125_, 1, v___x_4131_);
lean_ctor_set(v___x_4125_, 0, v_roots_4128_);
v___x_4133_ = v___x_4125_;
goto v_reusejp_4132_;
}
else
{
lean_object* v_reuseFailAlloc_4134_; 
v_reuseFailAlloc_4134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4134_, 0, v_roots_4128_);
lean_ctor_set(v_reuseFailAlloc_4134_, 1, v___x_4131_);
v___x_4133_ = v_reuseFailAlloc_4134_;
goto v_reusejp_4132_;
}
v_reusejp_4132_:
{
return v___x_4133_;
}
}
}
else
{
lean_object* v_val_4138_; lean_object* v___x_4139_; uint8_t v___x_4140_; 
lean_dec(v_k_4119_);
v_val_4138_ = lean_ctor_get(v___x_4123_, 0);
lean_inc(v_val_4138_);
lean_dec_ref_known(v___x_4123_, 1);
v___x_4139_ = lean_array_get_size(v_tries_4122_);
v___x_4140_ = lean_nat_dec_lt(v_val_4138_, v___x_4139_);
if (v___x_4140_ == 0)
{
lean_dec(v_val_4138_);
lean_dec_ref(v_f_4120_);
return v_d_4118_;
}
else
{
lean_object* v___x_4142_; uint8_t v_isShared_4143_; uint8_t v_isSharedCheck_4152_; 
lean_inc_ref(v_tries_4122_);
lean_inc_ref(v_roots_4121_);
v_isSharedCheck_4152_ = !lean_is_exclusive(v_d_4118_);
if (v_isSharedCheck_4152_ == 0)
{
lean_object* v_unused_4153_; lean_object* v_unused_4154_; 
v_unused_4153_ = lean_ctor_get(v_d_4118_, 1);
lean_dec(v_unused_4153_);
v_unused_4154_ = lean_ctor_get(v_d_4118_, 0);
lean_dec(v_unused_4154_);
v___x_4142_ = v_d_4118_;
v_isShared_4143_ = v_isSharedCheck_4152_;
goto v_resetjp_4141_;
}
else
{
lean_dec(v_d_4118_);
v___x_4142_ = lean_box(0);
v_isShared_4143_ = v_isSharedCheck_4152_;
goto v_resetjp_4141_;
}
v_resetjp_4141_:
{
lean_object* v_v_4144_; lean_object* v___x_4145_; lean_object* v_xs_x27_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4150_; 
v_v_4144_ = lean_array_fget(v_tries_4122_, v_val_4138_);
v___x_4145_ = lean_box(0);
v_xs_x27_4146_ = lean_array_fset(v_tries_4122_, v_val_4138_, v___x_4145_);
v___x_4147_ = lean_apply_1(v_f_4120_, v_v_4144_);
v___x_4148_ = lean_array_fset(v_xs_x27_4146_, v_val_4138_, v___x_4147_);
lean_dec(v_val_4138_);
if (v_isShared_4143_ == 0)
{
lean_ctor_set(v___x_4142_, 1, v___x_4148_);
v___x_4150_ = v___x_4142_;
goto v_reusejp_4149_;
}
else
{
lean_object* v_reuseFailAlloc_4151_; 
v_reuseFailAlloc_4151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4151_, 0, v_roots_4121_);
lean_ctor_set(v_reuseFailAlloc_4151_, 1, v___x_4148_);
v___x_4150_ = v_reuseFailAlloc_4151_;
goto v_reusejp_4149_;
}
v_reusejp_4149_:
{
return v___x_4150_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt(lean_object* v_00_u03b1_4155_, lean_object* v_d_4156_, lean_object* v_k_4157_, lean_object* v_f_4158_){
_start:
{
lean_object* v___x_4159_; 
v___x_4159_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(v_d_4156_, v_k_4157_, v_f_4158_);
return v___x_4159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg___lam__0(lean_object* v_e_4160_, lean_object* v_x_4161_){
_start:
{
lean_object* v___x_4162_; 
v___x_4162_ = lean_array_push(v_x_4161_, v_e_4160_);
return v___x_4162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg(lean_object* v_d_4163_, lean_object* v_k_4164_, lean_object* v_e_4165_){
_start:
{
lean_object* v___f_4166_; lean_object* v___x_4167_; 
v___f_4166_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4166_, 0, v_e_4165_);
v___x_4167_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(v_d_4163_, v_k_4164_, v___f_4166_);
return v___x_4167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push(lean_object* v_00_u03b1_4168_, lean_object* v_d_4169_, lean_object* v_k_4170_, lean_object* v_e_4171_){
_start:
{
lean_object* v___x_4172_; 
v___x_4172_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg(v_d_4169_, v_k_4170_, v_e_4171_);
return v___x_4172_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(size_t v_sz_4173_, size_t v_i_4174_, lean_object* v_bs_4175_){
_start:
{
uint8_t v___x_4176_; 
v___x_4176_ = lean_usize_dec_lt(v_i_4174_, v_sz_4173_);
if (v___x_4176_ == 0)
{
return v_bs_4175_;
}
else
{
lean_object* v_v_4177_; lean_object* v___x_4178_; lean_object* v_bs_x27_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; size_t v___x_4183_; size_t v___x_4184_; lean_object* v___x_4185_; 
v_v_4177_ = lean_array_uget(v_bs_4175_, v_i_4174_);
v___x_4178_ = lean_unsigned_to_nat(0u);
v_bs_x27_4179_ = lean_array_uset(v_bs_4175_, v_i_4174_, v___x_4178_);
v___x_4180_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__0));
v___x_4181_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2);
v___x_4182_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4182_, 0, v___x_4180_);
lean_ctor_set(v___x_4182_, 1, v___x_4178_);
lean_ctor_set(v___x_4182_, 2, v___x_4181_);
lean_ctor_set(v___x_4182_, 3, v_v_4177_);
v___x_4183_ = ((size_t)1ULL);
v___x_4184_ = lean_usize_add(v_i_4174_, v___x_4183_);
v___x_4185_ = lean_array_uset(v_bs_x27_4179_, v_i_4174_, v___x_4182_);
v_i_4174_ = v___x_4184_;
v_bs_4175_ = v___x_4185_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg___boxed(lean_object* v_sz_4187_, lean_object* v_i_4188_, lean_object* v_bs_4189_){
_start:
{
size_t v_sz_boxed_4190_; size_t v_i_boxed_4191_; lean_object* v_res_4192_; 
v_sz_boxed_4190_ = lean_unbox_usize(v_sz_4187_);
lean_dec(v_sz_4187_);
v_i_boxed_4191_ = lean_unbox_usize(v_i_4188_);
lean_dec(v_i_4188_);
v_res_4192_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(v_sz_boxed_4190_, v_i_boxed_4191_, v_bs_4189_);
return v_res_4192_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__1(lean_object* v_x_4193_, lean_object* v_x_4194_){
_start:
{
if (lean_obj_tag(v_x_4194_) == 0)
{
return v_x_4193_;
}
else
{
lean_object* v_key_4195_; lean_object* v_value_4196_; lean_object* v_tail_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; 
v_key_4195_ = lean_ctor_get(v_x_4194_, 0);
lean_inc(v_key_4195_);
v_value_4196_ = lean_ctor_get(v_x_4194_, 1);
lean_inc(v_value_4196_);
v_tail_4197_ = lean_ctor_get(v_x_4194_, 2);
lean_inc(v_tail_4197_);
lean_dec_ref_known(v_x_4194_, 3);
v___x_4198_ = lean_unsigned_to_nat(1u);
v___x_4199_ = lean_nat_add(v_value_4196_, v___x_4198_);
lean_dec(v_value_4196_);
v___x_4200_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_x_4193_, v_key_4195_, v___x_4199_);
v_x_4193_ = v___x_4200_;
v_x_4194_ = v_tail_4197_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(lean_object* v_as_4202_, size_t v_i_4203_, size_t v_stop_4204_, lean_object* v_b_4205_){
_start:
{
uint8_t v___x_4206_; 
v___x_4206_ = lean_usize_dec_eq(v_i_4203_, v_stop_4204_);
if (v___x_4206_ == 0)
{
lean_object* v___x_4207_; lean_object* v___x_4208_; size_t v___x_4209_; size_t v___x_4210_; 
v___x_4207_ = lean_array_uget_borrowed(v_as_4202_, v_i_4203_);
lean_inc(v___x_4207_);
v___x_4208_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__1(v_b_4205_, v___x_4207_);
v___x_4209_ = ((size_t)1ULL);
v___x_4210_ = lean_usize_add(v_i_4203_, v___x_4209_);
v_i_4203_ = v___x_4210_;
v_b_4205_ = v___x_4208_;
goto _start;
}
else
{
return v_b_4205_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2___boxed(lean_object* v_as_4212_, lean_object* v_i_4213_, lean_object* v_stop_4214_, lean_object* v_b_4215_){
_start:
{
size_t v_i_boxed_4216_; size_t v_stop_boxed_4217_; lean_object* v_res_4218_; 
v_i_boxed_4216_ = lean_unbox_usize(v_i_4213_);
lean_dec(v_i_4213_);
v_stop_boxed_4217_ = lean_unbox_usize(v_stop_4214_);
lean_dec(v_stop_4214_);
v_res_4218_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(v_as_4212_, v_i_boxed_4216_, v_stop_boxed_4217_, v_b_4215_);
lean_dec_ref(v_as_4212_);
return v_res_4218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(lean_object* v_d_4219_){
_start:
{
lean_object* v_roots_4220_; lean_object* v_tries_4221_; lean_object* v___x_4223_; uint8_t v_isShared_4224_; uint8_t v_isSharedCheck_4244_; 
v_roots_4220_ = lean_ctor_get(v_d_4219_, 0);
v_tries_4221_ = lean_ctor_get(v_d_4219_, 1);
v_isSharedCheck_4244_ = !lean_is_exclusive(v_d_4219_);
if (v_isSharedCheck_4244_ == 0)
{
v___x_4223_ = v_d_4219_;
v_isShared_4224_ = v_isSharedCheck_4244_;
goto v_resetjp_4222_;
}
else
{
lean_inc(v_tries_4221_);
lean_inc(v_roots_4220_);
lean_dec(v_d_4219_);
v___x_4223_ = lean_box(0);
v_isShared_4224_ = v_isSharedCheck_4244_;
goto v_resetjp_4222_;
}
v_resetjp_4222_:
{
lean_object* v___y_4226_; lean_object* v_buckets_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; uint8_t v___x_4240_; 
v_buckets_4237_ = lean_ctor_get(v_roots_4220_, 1);
v___x_4238_ = lean_unsigned_to_nat(0u);
v___x_4239_ = lean_array_get_size(v_buckets_4237_);
v___x_4240_ = lean_nat_dec_lt(v___x_4238_, v___x_4239_);
if (v___x_4240_ == 0)
{
v___y_4226_ = v_roots_4220_;
goto v___jp_4225_;
}
else
{
size_t v___x_4241_; size_t v___x_4242_; lean_object* v___x_4243_; 
lean_inc_ref(v_buckets_4237_);
v___x_4241_ = ((size_t)0ULL);
v___x_4242_ = lean_usize_of_nat(v___x_4239_);
v___x_4243_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(v_buckets_4237_, v___x_4241_, v___x_4242_, v_roots_4220_);
lean_dec_ref(v_buckets_4237_);
v___y_4226_ = v___x_4243_;
goto v___jp_4225_;
}
v___jp_4225_:
{
lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; size_t v_sz_4230_; size_t v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4235_; 
v___x_4227_ = lean_unsigned_to_nat(1u);
v___x_4228_ = lean_mk_empty_array_with_capacity(v___x_4227_);
lean_dec_ref(v___x_4228_);
v___x_4229_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__0);
v_sz_4230_ = lean_array_size(v_tries_4221_);
v___x_4231_ = ((size_t)0ULL);
v___x_4232_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(v_sz_4230_, v___x_4231_, v_tries_4221_);
v___x_4233_ = l_Array_append___redArg(v___x_4229_, v___x_4232_);
lean_dec_ref(v___x_4232_);
if (v_isShared_4224_ == 0)
{
lean_ctor_set(v___x_4223_, 1, v___y_4226_);
lean_ctor_set(v___x_4223_, 0, v___x_4233_);
v___x_4235_ = v___x_4223_;
goto v_reusejp_4234_;
}
else
{
lean_object* v_reuseFailAlloc_4236_; 
v_reuseFailAlloc_4236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4236_, 0, v___x_4233_);
lean_ctor_set(v_reuseFailAlloc_4236_, 1, v___y_4226_);
v___x_4235_ = v_reuseFailAlloc_4236_;
goto v_reusejp_4234_;
}
v_reusejp_4234_:
{
return v___x_4235_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy(lean_object* v_00_u03b1_4245_, lean_object* v_d_4246_){
_start:
{
lean_object* v___x_4247_; 
v___x_4247_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_d_4246_);
return v___x_4247_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0(lean_object* v_00_u03b1_4248_, size_t v_sz_4249_, size_t v_i_4250_, lean_object* v_bs_4251_){
_start:
{
lean_object* v___x_4252_; 
v___x_4252_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(v_sz_4249_, v_i_4250_, v_bs_4251_);
return v___x_4252_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___boxed(lean_object* v_00_u03b1_4253_, lean_object* v_sz_4254_, lean_object* v_i_4255_, lean_object* v_bs_4256_){
_start:
{
size_t v_sz_boxed_4257_; size_t v_i_boxed_4258_; lean_object* v_res_4259_; 
v_sz_boxed_4257_ = lean_unbox_usize(v_sz_4254_);
lean_dec(v_sz_4254_);
v_i_boxed_4258_ = lean_unbox_usize(v_i_4255_);
lean_dec(v_i_4255_);
v_res_4259_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0(v_00_u03b1_4253_, v_sz_boxed_4257_, v_i_boxed_4258_, v_bs_4256_);
return v_res_4259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___lam__0(lean_object* v_y_4260_, lean_object* v_x_4261_){
_start:
{
lean_object* v___x_4262_; 
v___x_4262_ = l_Array_append___redArg(v_x_4261_, v_y_4260_);
return v___x_4262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___lam__0___boxed(lean_object* v_y_4263_, lean_object* v_x_4264_){
_start:
{
lean_object* v_res_4265_; 
v_res_4265_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___lam__0(v_y_4263_, v_x_4264_);
lean_dec_ref(v_y_4263_);
return v_res_4265_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4266_; 
v___x_4266_ = l_Array_instInhabited___redArg();
return v___x_4266_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(lean_object* v_tries_4267_, lean_object* v_snd_4268_, lean_object* v_x_4269_, lean_object* v_x_4270_){
_start:
{
if (lean_obj_tag(v_x_4270_) == 0)
{
lean_dec_ref(v_snd_4268_);
return v_x_4269_;
}
else
{
lean_object* v_key_4271_; lean_object* v_value_4272_; lean_object* v_tail_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; 
v_key_4271_ = lean_ctor_get(v_x_4270_, 0);
lean_inc(v_key_4271_);
v_value_4272_ = lean_ctor_get(v_x_4270_, 1);
lean_inc(v_value_4272_);
v_tail_4273_ = lean_ctor_get(v_x_4270_, 2);
lean_inc(v_tail_4273_);
lean_dec_ref_known(v_x_4270_, 3);
v___x_4274_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0);
v___x_4275_ = lean_array_get_borrowed(v___x_4274_, v_tries_4267_, v_value_4272_);
lean_dec(v_value_4272_);
lean_inc_ref(v_snd_4268_);
lean_inc(v___x_4275_);
v___x_4276_ = lean_apply_1(v_snd_4268_, v___x_4275_);
v___x_4277_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(v_x_4269_, v_key_4271_, v___x_4276_);
v_x_4269_ = v___x_4277_;
v_x_4270_ = v_tail_4273_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___boxed(lean_object* v_tries_4279_, lean_object* v_snd_4280_, lean_object* v_x_4281_, lean_object* v_x_4282_){
_start:
{
lean_object* v_res_4283_; 
v_res_4283_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(v_tries_4279_, v_snd_4280_, v_x_4281_, v_x_4282_);
lean_dec_ref(v_tries_4279_);
return v_res_4283_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(lean_object* v_tries_4284_, lean_object* v_snd_4285_, lean_object* v_as_4286_, size_t v_i_4287_, size_t v_stop_4288_, lean_object* v_b_4289_){
_start:
{
uint8_t v___x_4290_; 
v___x_4290_ = lean_usize_dec_eq(v_i_4287_, v_stop_4288_);
if (v___x_4290_ == 0)
{
lean_object* v___x_4291_; lean_object* v___x_4292_; size_t v___x_4293_; size_t v___x_4294_; 
v___x_4291_ = lean_array_uget_borrowed(v_as_4286_, v_i_4287_);
lean_inc(v___x_4291_);
lean_inc_ref(v_snd_4285_);
v___x_4292_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(v_tries_4284_, v_snd_4285_, v_b_4289_, v___x_4291_);
v___x_4293_ = ((size_t)1ULL);
v___x_4294_ = lean_usize_add(v_i_4287_, v___x_4293_);
v_i_4287_ = v___x_4294_;
v_b_4289_ = v___x_4292_;
goto _start;
}
else
{
lean_dec_ref(v_snd_4285_);
return v_b_4289_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg___boxed(lean_object* v_tries_4296_, lean_object* v_snd_4297_, lean_object* v_as_4298_, lean_object* v_i_4299_, lean_object* v_stop_4300_, lean_object* v_b_4301_){
_start:
{
size_t v_i_boxed_4302_; size_t v_stop_boxed_4303_; lean_object* v_res_4304_; 
v_i_boxed_4302_ = lean_unbox_usize(v_i_4299_);
lean_dec(v_i_4299_);
v_stop_boxed_4303_ = lean_unbox_usize(v_stop_4300_);
lean_dec(v_stop_4300_);
v_res_4304_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(v_tries_4296_, v_snd_4297_, v_as_4298_, v_i_boxed_4302_, v_stop_boxed_4303_, v_b_4301_);
lean_dec_ref(v_as_4298_);
lean_dec_ref(v_tries_4296_);
return v_res_4304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg(lean_object* v_x_4307_, lean_object* v_y_4308_){
_start:
{
lean_object* v_fst_4310_; lean_object* v_buckets_4311_; lean_object* v_tries_4312_; lean_object* v_snd_4313_; lean_object* v_roots_4320_; lean_object* v_roots_4321_; lean_object* v_tries_4322_; lean_object* v_size_4323_; lean_object* v_buckets_4324_; lean_object* v_tries_4325_; lean_object* v_size_4326_; lean_object* v_buckets_4327_; uint8_t v___x_4328_; 
v_roots_4320_ = lean_ctor_get(v_y_4308_, 0);
v_roots_4321_ = lean_ctor_get(v_x_4307_, 0);
v_tries_4322_ = lean_ctor_get(v_y_4308_, 1);
v_size_4323_ = lean_ctor_get(v_roots_4320_, 0);
v_buckets_4324_ = lean_ctor_get(v_roots_4320_, 1);
v_tries_4325_ = lean_ctor_get(v_x_4307_, 1);
v_size_4326_ = lean_ctor_get(v_roots_4321_, 0);
v_buckets_4327_ = lean_ctor_get(v_roots_4321_, 1);
v___x_4328_ = lean_nat_dec_le(v_size_4323_, v_size_4326_);
if (v___x_4328_ == 0)
{
lean_object* v___f_4329_; 
lean_inc_ref(v_buckets_4327_);
lean_inc_ref(v_tries_4325_);
lean_dec_ref(v_x_4307_);
v___f_4329_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___closed__0));
v_fst_4310_ = v_y_4308_;
v_buckets_4311_ = v_buckets_4327_;
v_tries_4312_ = v_tries_4325_;
v_snd_4313_ = v___f_4329_;
goto v___jp_4309_;
}
else
{
lean_object* v___f_4330_; 
lean_inc_ref(v_buckets_4324_);
lean_inc_ref(v_tries_4322_);
lean_dec_ref(v_y_4308_);
v___f_4330_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___closed__1));
v_fst_4310_ = v_x_4307_;
v_buckets_4311_ = v_buckets_4324_;
v_tries_4312_ = v_tries_4322_;
v_snd_4313_ = v___f_4330_;
goto v___jp_4309_;
}
v___jp_4309_:
{
lean_object* v___x_4314_; lean_object* v___x_4315_; uint8_t v___x_4316_; 
v___x_4314_ = lean_unsigned_to_nat(0u);
v___x_4315_ = lean_array_get_size(v_buckets_4311_);
v___x_4316_ = lean_nat_dec_lt(v___x_4314_, v___x_4315_);
if (v___x_4316_ == 0)
{
lean_dec_ref(v_tries_4312_);
lean_dec_ref(v_buckets_4311_);
return v_fst_4310_;
}
else
{
size_t v___x_4317_; size_t v___x_4318_; lean_object* v___x_4319_; 
v___x_4317_ = ((size_t)0ULL);
v___x_4318_ = lean_usize_of_nat(v___x_4315_);
lean_inc_ref(v_snd_4313_);
v___x_4319_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(v_tries_4312_, v_snd_4313_, v_buckets_4311_, v___x_4317_, v___x_4318_, v_fst_4310_);
lean_dec_ref(v_buckets_4311_);
lean_dec_ref(v_tries_4312_);
return v___x_4319_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append(lean_object* v_00_u03b1_4331_, lean_object* v_x_4332_, lean_object* v_y_4333_){
_start:
{
lean_object* v___x_4334_; 
v___x_4334_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg(v_x_4332_, v_y_4333_);
return v___x_4334_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0(lean_object* v_00_u03b1_4335_, lean_object* v_tries_4336_, lean_object* v_snd_4337_, lean_object* v_x_4338_, lean_object* v_x_4339_){
_start:
{
lean_object* v___x_4340_; 
v___x_4340_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(v_tries_4336_, v_snd_4337_, v_x_4338_, v_x_4339_);
return v___x_4340_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___boxed(lean_object* v_00_u03b1_4341_, lean_object* v_tries_4342_, lean_object* v_snd_4343_, lean_object* v_x_4344_, lean_object* v_x_4345_){
_start:
{
lean_object* v_res_4346_; 
v_res_4346_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0(v_00_u03b1_4341_, v_tries_4342_, v_snd_4343_, v_x_4344_, v_x_4345_);
lean_dec_ref(v_tries_4342_);
return v_res_4346_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1(lean_object* v_00_u03b1_4347_, lean_object* v_tries_4348_, lean_object* v_snd_4349_, lean_object* v_as_4350_, size_t v_i_4351_, size_t v_stop_4352_, lean_object* v_b_4353_){
_start:
{
lean_object* v___x_4354_; 
v___x_4354_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(v_tries_4348_, v_snd_4349_, v_as_4350_, v_i_4351_, v_stop_4352_, v_b_4353_);
return v___x_4354_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___boxed(lean_object* v_00_u03b1_4355_, lean_object* v_tries_4356_, lean_object* v_snd_4357_, lean_object* v_as_4358_, lean_object* v_i_4359_, lean_object* v_stop_4360_, lean_object* v_b_4361_){
_start:
{
size_t v_i_boxed_4362_; size_t v_stop_boxed_4363_; lean_object* v_res_4364_; 
v_i_boxed_4362_ = lean_unbox_usize(v_i_4359_);
lean_dec(v_i_4359_);
v_stop_boxed_4363_ = lean_unbox_usize(v_stop_4360_);
lean_dec(v_stop_4360_);
v_res_4364_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1(v_00_u03b1_4355_, v_tries_4356_, v_snd_4357_, v_as_4358_, v_i_boxed_4362_, v_stop_boxed_4363_, v_b_4361_);
lean_dec_ref(v_as_4358_);
lean_dec_ref(v_tries_4356_);
return v_res_4364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend___redArg(){
_start:
{
lean_object* v___x_4367_; 
v___x_4367_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend___redArg___closed__0));
return v___x_4367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend___redArg___boxed(lean_object* v___dummy_4368_){
_start:
{
lean_object* v_res_4369_; 
v_res_4369_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend___redArg();
return v_res_4369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend(lean_object* v_00_u03b1_4370_){
_start:
{
lean_object* v___x_4371_; 
v___x_4371_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend___redArg___closed__0));
return v___x_4371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(lean_object* v_expr_4372_, lean_object* v_value_4373_, lean_object* v_a_4374_, lean_object* v_a_4375_, lean_object* v_a_4376_, lean_object* v_a_4377_){
_start:
{
lean_object* v_lctx_4379_; lean_object* v_localInstances_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; 
v_lctx_4379_ = lean_ctor_get(v_a_4374_, 2);
v_localInstances_4380_ = lean_ctor_get(v_a_4374_, 3);
lean_inc_ref(v_localInstances_4380_);
lean_inc_ref(v_lctx_4379_);
v___x_4381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4381_, 0, v_lctx_4379_);
lean_ctor_set(v___x_4381_, 1, v_localInstances_4380_);
v___x_4382_ = l_Lean_Meta_LazyDiscrTree_rootKey(v_expr_4372_, v_a_4374_, v_a_4375_, v_a_4376_, v_a_4377_);
if (lean_obj_tag(v___x_4382_) == 0)
{
lean_object* v_a_4383_; lean_object* v___x_4385_; uint8_t v_isShared_4386_; uint8_t v_isSharedCheck_4401_; 
v_a_4383_ = lean_ctor_get(v___x_4382_, 0);
v_isSharedCheck_4401_ = !lean_is_exclusive(v___x_4382_);
if (v_isSharedCheck_4401_ == 0)
{
v___x_4385_ = v___x_4382_;
v_isShared_4386_ = v_isSharedCheck_4401_;
goto v_resetjp_4384_;
}
else
{
lean_inc(v_a_4383_);
lean_dec(v___x_4382_);
v___x_4385_ = lean_box(0);
v_isShared_4386_ = v_isSharedCheck_4401_;
goto v_resetjp_4384_;
}
v_resetjp_4384_:
{
lean_object* v_fst_4387_; lean_object* v_snd_4388_; lean_object* v___x_4390_; uint8_t v_isShared_4391_; uint8_t v_isSharedCheck_4400_; 
v_fst_4387_ = lean_ctor_get(v_a_4383_, 0);
v_snd_4388_ = lean_ctor_get(v_a_4383_, 1);
v_isSharedCheck_4400_ = !lean_is_exclusive(v_a_4383_);
if (v_isSharedCheck_4400_ == 0)
{
v___x_4390_ = v_a_4383_;
v_isShared_4391_ = v_isSharedCheck_4400_;
goto v_resetjp_4389_;
}
else
{
lean_inc(v_snd_4388_);
lean_inc(v_fst_4387_);
lean_dec(v_a_4383_);
v___x_4390_ = lean_box(0);
v_isShared_4391_ = v_isSharedCheck_4400_;
goto v_resetjp_4389_;
}
v_resetjp_4389_:
{
lean_object* v___x_4393_; 
if (v_isShared_4391_ == 0)
{
lean_ctor_set(v___x_4390_, 1, v_value_4373_);
lean_ctor_set(v___x_4390_, 0, v___x_4381_);
v___x_4393_ = v___x_4390_;
goto v_reusejp_4392_;
}
else
{
lean_object* v_reuseFailAlloc_4399_; 
v_reuseFailAlloc_4399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4399_, 0, v___x_4381_);
lean_ctor_set(v_reuseFailAlloc_4399_, 1, v_value_4373_);
v___x_4393_ = v_reuseFailAlloc_4399_;
goto v_reusejp_4392_;
}
v_reusejp_4392_:
{
lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4397_; 
v___x_4394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4394_, 0, v_snd_4388_);
lean_ctor_set(v___x_4394_, 1, v___x_4393_);
v___x_4395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4395_, 0, v_fst_4387_);
lean_ctor_set(v___x_4395_, 1, v___x_4394_);
if (v_isShared_4386_ == 0)
{
lean_ctor_set(v___x_4385_, 0, v___x_4395_);
v___x_4397_ = v___x_4385_;
goto v_reusejp_4396_;
}
else
{
lean_object* v_reuseFailAlloc_4398_; 
v_reuseFailAlloc_4398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4398_, 0, v___x_4395_);
v___x_4397_ = v_reuseFailAlloc_4398_;
goto v_reusejp_4396_;
}
v_reusejp_4396_:
{
return v___x_4397_;
}
}
}
}
}
else
{
lean_object* v_a_4402_; lean_object* v___x_4404_; uint8_t v_isShared_4405_; uint8_t v_isSharedCheck_4409_; 
lean_dec_ref_known(v___x_4381_, 2);
lean_dec(v_value_4373_);
v_a_4402_ = lean_ctor_get(v___x_4382_, 0);
v_isSharedCheck_4409_ = !lean_is_exclusive(v___x_4382_);
if (v_isSharedCheck_4409_ == 0)
{
v___x_4404_ = v___x_4382_;
v_isShared_4405_ = v_isSharedCheck_4409_;
goto v_resetjp_4403_;
}
else
{
lean_inc(v_a_4402_);
lean_dec(v___x_4382_);
v___x_4404_ = lean_box(0);
v_isShared_4405_ = v_isSharedCheck_4409_;
goto v_resetjp_4403_;
}
v_resetjp_4403_:
{
lean_object* v___x_4407_; 
if (v_isShared_4405_ == 0)
{
v___x_4407_ = v___x_4404_;
goto v_reusejp_4406_;
}
else
{
lean_object* v_reuseFailAlloc_4408_; 
v_reuseFailAlloc_4408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4408_, 0, v_a_4402_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg___boxed(lean_object* v_expr_4410_, lean_object* v_value_4411_, lean_object* v_a_4412_, lean_object* v_a_4413_, lean_object* v_a_4414_, lean_object* v_a_4415_, lean_object* v_a_4416_){
_start:
{
lean_object* v_res_4417_; 
v_res_4417_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(v_expr_4410_, v_value_4411_, v_a_4412_, v_a_4413_, v_a_4414_, v_a_4415_);
lean_dec(v_a_4415_);
lean_dec_ref(v_a_4414_);
lean_dec(v_a_4413_);
lean_dec_ref(v_a_4412_);
return v_res_4417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr(lean_object* v_00_u03b1_4418_, lean_object* v_expr_4419_, lean_object* v_value_4420_, lean_object* v_a_4421_, lean_object* v_a_4422_, lean_object* v_a_4423_, lean_object* v_a_4424_){
_start:
{
lean_object* v___x_4426_; 
v___x_4426_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(v_expr_4419_, v_value_4420_, v_a_4421_, v_a_4422_, v_a_4423_, v_a_4424_);
return v___x_4426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___boxed(lean_object* v_00_u03b1_4427_, lean_object* v_expr_4428_, lean_object* v_value_4429_, lean_object* v_a_4430_, lean_object* v_a_4431_, lean_object* v_a_4432_, lean_object* v_a_4433_, lean_object* v_a_4434_){
_start:
{
lean_object* v_res_4435_; 
v_res_4435_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr(v_00_u03b1_4427_, v_expr_4428_, v_value_4429_, v_a_4430_, v_a_4431_, v_a_4432_, v_a_4433_);
lean_dec(v_a_4433_);
lean_dec_ref(v_a_4432_);
lean_dec(v_a_4431_);
lean_dec_ref(v_a_4430_);
return v_res_4435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(lean_object* v_e_4436_, lean_object* v_idx_4437_, lean_object* v_value_4438_, lean_object* v_a_4439_, lean_object* v_a_4440_, lean_object* v_a_4441_, lean_object* v_a_4442_){
_start:
{
lean_object* v_entry_4444_; lean_object* v___x_4446_; uint8_t v_isShared_4447_; uint8_t v_isSharedCheck_4490_; 
v_entry_4444_ = lean_ctor_get(v_e_4436_, 1);
v_isSharedCheck_4490_ = !lean_is_exclusive(v_e_4436_);
if (v_isSharedCheck_4490_ == 0)
{
lean_object* v_unused_4491_; 
v_unused_4491_ = lean_ctor_get(v_e_4436_, 0);
lean_dec(v_unused_4491_);
v___x_4446_ = v_e_4436_;
v_isShared_4447_ = v_isSharedCheck_4490_;
goto v_resetjp_4445_;
}
else
{
lean_inc(v_entry_4444_);
lean_dec(v_e_4436_);
v___x_4446_ = lean_box(0);
v_isShared_4447_ = v_isSharedCheck_4490_;
goto v_resetjp_4445_;
}
v_resetjp_4445_:
{
lean_object* v_snd_4448_; lean_object* v_fst_4449_; lean_object* v_fst_4450_; lean_object* v___x_4452_; uint8_t v_isShared_4453_; uint8_t v_isSharedCheck_4488_; 
v_snd_4448_ = lean_ctor_get(v_entry_4444_, 1);
lean_inc(v_snd_4448_);
v_fst_4449_ = lean_ctor_get(v_entry_4444_, 0);
lean_inc(v_fst_4449_);
lean_dec_ref(v_entry_4444_);
v_fst_4450_ = lean_ctor_get(v_snd_4448_, 0);
v_isSharedCheck_4488_ = !lean_is_exclusive(v_snd_4448_);
if (v_isSharedCheck_4488_ == 0)
{
lean_object* v_unused_4489_; 
v_unused_4489_ = lean_ctor_get(v_snd_4448_, 1);
lean_dec(v_unused_4489_);
v___x_4452_ = v_snd_4448_;
v_isShared_4453_ = v_isSharedCheck_4488_;
goto v_resetjp_4451_;
}
else
{
lean_inc(v_fst_4450_);
lean_dec(v_snd_4448_);
v___x_4452_ = lean_box(0);
v_isShared_4453_ = v_isSharedCheck_4488_;
goto v_resetjp_4451_;
}
v_resetjp_4451_:
{
lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; 
v___x_4454_ = l_Lean_instInhabitedExpr;
v___x_4455_ = lean_array_get(v___x_4454_, v_fst_4449_, v_idx_4437_);
lean_dec(v_fst_4449_);
v___x_4456_ = l_Lean_Meta_LazyDiscrTree_rootKey(v___x_4455_, v_a_4439_, v_a_4440_, v_a_4441_, v_a_4442_);
if (lean_obj_tag(v___x_4456_) == 0)
{
lean_object* v_a_4457_; lean_object* v___x_4459_; uint8_t v_isShared_4460_; uint8_t v_isSharedCheck_4479_; 
v_a_4457_ = lean_ctor_get(v___x_4456_, 0);
v_isSharedCheck_4479_ = !lean_is_exclusive(v___x_4456_);
if (v_isSharedCheck_4479_ == 0)
{
v___x_4459_ = v___x_4456_;
v_isShared_4460_ = v_isSharedCheck_4479_;
goto v_resetjp_4458_;
}
else
{
lean_inc(v_a_4457_);
lean_dec(v___x_4456_);
v___x_4459_ = lean_box(0);
v_isShared_4460_ = v_isSharedCheck_4479_;
goto v_resetjp_4458_;
}
v_resetjp_4458_:
{
lean_object* v_fst_4461_; lean_object* v_snd_4462_; lean_object* v___x_4464_; uint8_t v_isShared_4465_; uint8_t v_isSharedCheck_4478_; 
v_fst_4461_ = lean_ctor_get(v_a_4457_, 0);
v_snd_4462_ = lean_ctor_get(v_a_4457_, 1);
v_isSharedCheck_4478_ = !lean_is_exclusive(v_a_4457_);
if (v_isSharedCheck_4478_ == 0)
{
v___x_4464_ = v_a_4457_;
v_isShared_4465_ = v_isSharedCheck_4478_;
goto v_resetjp_4463_;
}
else
{
lean_inc(v_snd_4462_);
lean_inc(v_fst_4461_);
lean_dec(v_a_4457_);
v___x_4464_ = lean_box(0);
v_isShared_4465_ = v_isSharedCheck_4478_;
goto v_resetjp_4463_;
}
v_resetjp_4463_:
{
lean_object* v___x_4467_; 
if (v_isShared_4465_ == 0)
{
lean_ctor_set(v___x_4464_, 1, v_value_4438_);
lean_ctor_set(v___x_4464_, 0, v_fst_4450_);
v___x_4467_ = v___x_4464_;
goto v_reusejp_4466_;
}
else
{
lean_object* v_reuseFailAlloc_4477_; 
v_reuseFailAlloc_4477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4477_, 0, v_fst_4450_);
lean_ctor_set(v_reuseFailAlloc_4477_, 1, v_value_4438_);
v___x_4467_ = v_reuseFailAlloc_4477_;
goto v_reusejp_4466_;
}
v_reusejp_4466_:
{
lean_object* v___x_4469_; 
if (v_isShared_4453_ == 0)
{
lean_ctor_set(v___x_4452_, 1, v___x_4467_);
lean_ctor_set(v___x_4452_, 0, v_snd_4462_);
v___x_4469_ = v___x_4452_;
goto v_reusejp_4468_;
}
else
{
lean_object* v_reuseFailAlloc_4476_; 
v_reuseFailAlloc_4476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4476_, 0, v_snd_4462_);
lean_ctor_set(v_reuseFailAlloc_4476_, 1, v___x_4467_);
v___x_4469_ = v_reuseFailAlloc_4476_;
goto v_reusejp_4468_;
}
v_reusejp_4468_:
{
lean_object* v___x_4471_; 
if (v_isShared_4447_ == 0)
{
lean_ctor_set(v___x_4446_, 1, v___x_4469_);
lean_ctor_set(v___x_4446_, 0, v_fst_4461_);
v___x_4471_ = v___x_4446_;
goto v_reusejp_4470_;
}
else
{
lean_object* v_reuseFailAlloc_4475_; 
v_reuseFailAlloc_4475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4475_, 0, v_fst_4461_);
lean_ctor_set(v_reuseFailAlloc_4475_, 1, v___x_4469_);
v___x_4471_ = v_reuseFailAlloc_4475_;
goto v_reusejp_4470_;
}
v_reusejp_4470_:
{
lean_object* v___x_4473_; 
if (v_isShared_4460_ == 0)
{
lean_ctor_set(v___x_4459_, 0, v___x_4471_);
v___x_4473_ = v___x_4459_;
goto v_reusejp_4472_;
}
else
{
lean_object* v_reuseFailAlloc_4474_; 
v_reuseFailAlloc_4474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4474_, 0, v___x_4471_);
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
else
{
lean_object* v_a_4480_; lean_object* v___x_4482_; uint8_t v_isShared_4483_; uint8_t v_isSharedCheck_4487_; 
lean_del_object(v___x_4452_);
lean_dec(v_fst_4450_);
lean_del_object(v___x_4446_);
lean_dec(v_value_4438_);
v_a_4480_ = lean_ctor_get(v___x_4456_, 0);
v_isSharedCheck_4487_ = !lean_is_exclusive(v___x_4456_);
if (v_isSharedCheck_4487_ == 0)
{
v___x_4482_ = v___x_4456_;
v_isShared_4483_ = v_isSharedCheck_4487_;
goto v_resetjp_4481_;
}
else
{
lean_inc(v_a_4480_);
lean_dec(v___x_4456_);
v___x_4482_ = lean_box(0);
v_isShared_4483_ = v_isSharedCheck_4487_;
goto v_resetjp_4481_;
}
v_resetjp_4481_:
{
lean_object* v___x_4485_; 
if (v_isShared_4483_ == 0)
{
v___x_4485_ = v___x_4482_;
goto v_reusejp_4484_;
}
else
{
lean_object* v_reuseFailAlloc_4486_; 
v_reuseFailAlloc_4486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4486_, 0, v_a_4480_);
v___x_4485_ = v_reuseFailAlloc_4486_;
goto v_reusejp_4484_;
}
v_reusejp_4484_:
{
return v___x_4485_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg___boxed(lean_object* v_e_4492_, lean_object* v_idx_4493_, lean_object* v_value_4494_, lean_object* v_a_4495_, lean_object* v_a_4496_, lean_object* v_a_4497_, lean_object* v_a_4498_, lean_object* v_a_4499_){
_start:
{
lean_object* v_res_4500_; 
v_res_4500_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(v_e_4492_, v_idx_4493_, v_value_4494_, v_a_4495_, v_a_4496_, v_a_4497_, v_a_4498_);
lean_dec(v_a_4498_);
lean_dec_ref(v_a_4497_);
lean_dec(v_a_4496_);
lean_dec_ref(v_a_4495_);
lean_dec(v_idx_4493_);
return v_res_4500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry(lean_object* v_00_u03b1_4501_, lean_object* v_e_4502_, lean_object* v_idx_4503_, lean_object* v_value_4504_, lean_object* v_a_4505_, lean_object* v_a_4506_, lean_object* v_a_4507_, lean_object* v_a_4508_){
_start:
{
lean_object* v___x_4510_; 
v___x_4510_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(v_e_4502_, v_idx_4503_, v_value_4504_, v_a_4505_, v_a_4506_, v_a_4507_, v_a_4508_);
return v___x_4510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___boxed(lean_object* v_00_u03b1_4511_, lean_object* v_e_4512_, lean_object* v_idx_4513_, lean_object* v_value_4514_, lean_object* v_a_4515_, lean_object* v_a_4516_, lean_object* v_a_4517_, lean_object* v_a_4518_, lean_object* v_a_4519_){
_start:
{
lean_object* v_res_4520_; 
v_res_4520_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry(v_00_u03b1_4511_, v_e_4512_, v_idx_4513_, v_value_4514_, v_a_4515_, v_a_4516_, v_a_4517_, v_a_4518_);
lean_dec(v_a_4518_);
lean_dec_ref(v_a_4517_);
lean_dec(v_a_4516_);
lean_dec_ref(v_a_4515_);
lean_dec(v_idx_4513_);
return v_res_4520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_ImportData_new(){
_start:
{
lean_object* v___x_4524_; lean_object* v___x_4525_; 
v___x_4524_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_ImportData_new___closed__0));
v___x_4525_ = lean_st_mk_ref(v___x_4524_);
return v___x_4525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_ImportData_new___boxed(lean_object* v_a_4526_){
_start:
{
lean_object* v_res_4527_; 
v_res_4527_ = l_Lean_Meta_LazyDiscrTree_ImportData_new();
return v_res_4527_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4528_; 
v___x_4528_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_4528_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_4529_; lean_object* v___x_4530_; 
v___x_4529_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0_spec__0___redArg___closed__0);
v___x_4530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4530_, 0, v___x_4529_);
return v___x_4530_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0_spec__0___redArg(){
_start:
{
lean_object* v___x_4532_; 
v___x_4532_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0_spec__0___redArg___closed__1);
return v___x_4532_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0_spec__0___redArg___boxed(lean_object* v___dummy_4533_){
_start:
{
lean_object* v_res_4534_; 
v_res_4534_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0_spec__0___redArg();
return v_res_4534_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0(void){
_start:
{
lean_object* v___x_4535_; lean_object* v___x_4536_; 
v___x_4535_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0_spec__0___redArg___closed__0);
v___x_4536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4536_, 0, v___x_4535_);
return v___x_4536_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1(void){
_start:
{
lean_object* v___x_4537_; lean_object* v___x_4538_; 
v___x_4537_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0);
v___x_4538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4538_, 0, v___x_4537_);
lean_ctor_set(v___x_4538_, 1, v___x_4537_);
return v___x_4538_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2(void){
_start:
{
lean_object* v___x_4539_; 
v___x_4539_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0_spec__0___redArg();
return v___x_4539_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3(void){
_start:
{
lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; 
v___x_4540_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0);
v___x_4541_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2);
v___x_4542_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_4542_, 0, v___x_4541_);
lean_ctor_set(v___x_4542_, 1, v___x_4540_);
lean_ctor_set(v___x_4542_, 2, v___x_4540_);
lean_ctor_set(v___x_4542_, 3, v___x_4540_);
lean_ctor_set(v___x_4542_, 4, v___x_4540_);
lean_ctor_set(v___x_4542_, 5, v___x_4540_);
lean_ctor_set(v___x_4542_, 6, v___x_4540_);
return v___x_4542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Cache_empty(lean_object* v_ngen_4543_){
_start:
{
lean_object* v___x_4544_; lean_object* v___x_4545_; lean_object* v___x_4546_; 
v___x_4544_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1);
v___x_4545_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3);
v___x_4546_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4546_, 0, v_ngen_4543_);
lean_ctor_set(v___x_4546_, 1, v___x_4544_);
lean_ctor_set(v___x_4546_, 2, v___x_4545_);
return v___x_4546_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0_spec__0(lean_object* v_00_u03b2_4547_){
_start:
{
lean_object* v___x_4548_; 
v___x_4548_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2);
return v___x_4548_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0___redArg(){
_start:
{
lean_object* v___x_4550_; 
v___x_4550_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2);
return v___x_4550_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0___redArg___boxed(lean_object* v___dummy_4551_){
_start:
{
lean_object* v_res_4552_; 
v_res_4552_ = l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0___redArg();
return v_res_4552_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0(lean_object* v_00_u03b2_4553_){
_start:
{
lean_object* v___x_4554_; 
v___x_4554_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2);
return v___x_4554_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName(lean_object* v_env_4555_, lean_object* v_declName_4556_){
_start:
{
uint8_t v___x_4557_; 
v___x_4557_ = l_Lean_isPrivateName(v_declName_4556_);
if (v___x_4557_ == 0)
{
return v___x_4557_;
}
else
{
lean_object* v___x_4558_; 
v___x_4558_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4555_, v_declName_4556_);
if (lean_obj_tag(v___x_4558_) == 0)
{
return v___x_4557_;
}
else
{
lean_object* v_val_4559_; lean_object* v___x_4560_; uint8_t v_isModule_4561_; lean_object* v_modules_4562_; uint8_t v___x_4563_; 
v_val_4559_ = lean_ctor_get(v___x_4558_, 0);
lean_inc(v_val_4559_);
lean_dec_ref_known(v___x_4558_, 1);
v___x_4560_ = l_Lean_Environment_header(v_env_4555_);
v_isModule_4561_ = lean_ctor_get_uint8(v___x_4560_, sizeof(void*)*8 + 4);
v_modules_4562_ = lean_ctor_get(v___x_4560_, 3);
lean_inc_ref(v_modules_4562_);
lean_dec_ref(v___x_4560_);
v___x_4563_ = 0;
if (v_isModule_4561_ == 0)
{
lean_dec_ref(v_modules_4562_);
lean_dec(v_val_4559_);
return v___x_4563_;
}
else
{
lean_object* v___x_4564_; uint8_t v___x_4565_; 
v___x_4564_ = lean_array_get_size(v_modules_4562_);
v___x_4565_ = lean_nat_dec_lt(v_val_4559_, v___x_4564_);
if (v___x_4565_ == 0)
{
lean_dec_ref(v_modules_4562_);
lean_dec(v_val_4559_);
return v___x_4563_;
}
else
{
lean_object* v___x_4566_; lean_object* v_toImport_4567_; uint8_t v_importAll_4568_; 
v___x_4566_ = lean_array_fget(v_modules_4562_, v_val_4559_);
lean_dec(v_val_4559_);
lean_dec_ref(v_modules_4562_);
v_toImport_4567_ = lean_ctor_get(v___x_4566_, 0);
lean_inc_ref(v_toImport_4567_);
lean_dec(v___x_4566_);
v_importAll_4568_ = lean_ctor_get_uint8(v_toImport_4567_, sizeof(void*)*1);
lean_dec_ref(v_toImport_4567_);
return v_importAll_4568_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName___boxed(lean_object* v_env_4569_, lean_object* v_declName_4570_){
_start:
{
uint8_t v_res_4571_; lean_object* v_r_4572_; 
v_res_4571_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName(v_env_4569_, v_declName_4570_);
lean_dec(v_declName_4570_);
lean_dec_ref(v_env_4569_);
v_r_4572_ = lean_box(v_res_4571_);
return v_r_4572_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_LazyDiscrTree_blacklistInsertion(lean_object* v_env_4578_, lean_object* v_declName_4579_){
_start:
{
uint8_t v___x_4580_; 
lean_inc(v_declName_4579_);
lean_inc_ref(v_env_4578_);
v___x_4580_ = l_Lean_Meta_allowCompletion(v_env_4578_, v_declName_4579_);
if (v___x_4580_ == 0)
{
uint8_t v___x_4581_; 
lean_dec(v_declName_4579_);
lean_dec_ref(v_env_4578_);
v___x_4581_ = 1;
return v___x_4581_;
}
else
{
lean_object* v___x_4582_; uint8_t v___x_4583_; 
v___x_4582_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__1));
v___x_4583_ = lean_name_eq(v_declName_4579_, v___x_4582_);
if (v___x_4583_ == 0)
{
uint8_t v___x_4592_; 
lean_inc(v_declName_4579_);
v___x_4592_ = l_Lean_Name_isInternalDetail(v_declName_4579_);
if (v___x_4592_ == 0)
{
lean_dec_ref(v_env_4578_);
goto v___jp_4588_;
}
else
{
uint8_t v___x_4593_; 
v___x_4593_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName(v_env_4578_, v_declName_4579_);
lean_dec_ref(v_env_4578_);
if (v___x_4593_ == 0)
{
lean_dec(v_declName_4579_);
return v___x_4592_;
}
else
{
goto v___jp_4588_;
}
}
}
else
{
lean_dec(v_declName_4579_);
lean_dec_ref(v_env_4578_);
return v___x_4583_;
}
v___jp_4584_:
{
if (lean_obj_tag(v_declName_4579_) == 1)
{
lean_object* v_str_4585_; lean_object* v___x_4586_; uint8_t v___x_4587_; 
v_str_4585_ = lean_ctor_get(v_declName_4579_, 1);
lean_inc_ref(v_str_4585_);
lean_dec_ref_known(v_declName_4579_, 2);
v___x_4586_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__2));
v___x_4587_ = lean_string_dec_eq(v_str_4585_, v___x_4586_);
lean_dec_ref(v_str_4585_);
return v___x_4587_;
}
else
{
lean_dec(v_declName_4579_);
return v___x_4583_;
}
}
v___jp_4588_:
{
if (lean_obj_tag(v_declName_4579_) == 1)
{
lean_object* v_str_4589_; lean_object* v___x_4590_; uint8_t v___x_4591_; 
v_str_4589_ = lean_ctor_get(v_declName_4579_, 1);
v___x_4590_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__3));
v___x_4591_ = lean_string_dec_eq(v_str_4589_, v___x_4590_);
if (v___x_4591_ == 0)
{
goto v___jp_4584_;
}
else
{
lean_dec_ref_known(v_declName_4579_, 2);
return v___x_4591_;
}
}
else
{
goto v___jp_4584_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_blacklistInsertion___boxed(lean_object* v_env_4594_, lean_object* v_declName_4595_){
_start:
{
uint8_t v_res_4596_; lean_object* v_r_4597_; 
v_res_4596_ = l_Lean_Meta_LazyDiscrTree_blacklistInsertion(v_env_4594_, v_declName_4595_);
v_r_4597_ = lean_box(v_res_4596_);
return v_r_4597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(lean_object* v_opts_4598_, lean_object* v_opt_4599_){
_start:
{
lean_object* v_name_4600_; lean_object* v_defValue_4601_; lean_object* v_map_4602_; lean_object* v___x_4603_; 
v_name_4600_ = lean_ctor_get(v_opt_4599_, 0);
v_defValue_4601_ = lean_ctor_get(v_opt_4599_, 1);
v_map_4602_ = lean_ctor_get(v_opts_4598_, 0);
v___x_4603_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4602_, v_name_4600_);
if (lean_obj_tag(v___x_4603_) == 0)
{
lean_inc(v_defValue_4601_);
return v_defValue_4601_;
}
else
{
lean_object* v_val_4604_; 
v_val_4604_ = lean_ctor_get(v___x_4603_, 0);
lean_inc(v_val_4604_);
lean_dec_ref_known(v___x_4603_, 1);
if (lean_obj_tag(v_val_4604_) == 3)
{
lean_object* v_v_4605_; 
v_v_4605_ = lean_ctor_get(v_val_4604_, 0);
lean_inc(v_v_4605_);
lean_dec_ref_known(v_val_4604_, 1);
return v_v_4605_;
}
else
{
lean_dec(v_val_4604_);
lean_inc(v_defValue_4601_);
return v_defValue_4601_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0___boxed(lean_object* v_opts_4606_, lean_object* v_opt_4607_){
_start:
{
lean_object* v_res_4608_; 
v_res_4608_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(v_opts_4606_, v_opt_4607_);
lean_dec_ref(v_opt_4607_);
lean_dec_ref(v_opts_4606_);
return v_res_4608_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1___redArg(lean_object* v_as_4609_, size_t v_i_4610_, size_t v_stop_4611_, lean_object* v_b_4612_){
_start:
{
uint8_t v___x_4613_; 
v___x_4613_ = lean_usize_dec_eq(v_i_4610_, v_stop_4611_);
if (v___x_4613_ == 0)
{
lean_object* v___x_4614_; lean_object* v_key_4615_; lean_object* v_entry_4616_; lean_object* v___x_4617_; size_t v___x_4618_; size_t v___x_4619_; 
v___x_4614_ = lean_array_uget_borrowed(v_as_4609_, v_i_4610_);
v_key_4615_ = lean_ctor_get(v___x_4614_, 0);
v_entry_4616_ = lean_ctor_get(v___x_4614_, 1);
lean_inc_ref(v_entry_4616_);
lean_inc(v_key_4615_);
v___x_4617_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg(v_b_4612_, v_key_4615_, v_entry_4616_);
v___x_4618_ = ((size_t)1ULL);
v___x_4619_ = lean_usize_add(v_i_4610_, v___x_4618_);
v_i_4610_ = v___x_4619_;
v_b_4612_ = v___x_4617_;
goto _start;
}
else
{
return v_b_4612_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1___redArg___boxed(lean_object* v_as_4621_, lean_object* v_i_4622_, lean_object* v_stop_4623_, lean_object* v_b_4624_){
_start:
{
size_t v_i_boxed_4625_; size_t v_stop_boxed_4626_; lean_object* v_res_4627_; 
v_i_boxed_4625_ = lean_unbox_usize(v_i_4622_);
lean_dec(v_i_4622_);
v_stop_boxed_4626_ = lean_unbox_usize(v_stop_4623_);
lean_dec(v_stop_4623_);
v_res_4627_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1___redArg(v_as_4621_, v_i_boxed_4625_, v_stop_boxed_4626_, v_b_4624_);
lean_dec_ref(v_as_4621_);
return v_res_4627_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0(void){
_start:
{
lean_object* v___x_4628_; lean_object* v___x_4629_; 
v___x_4628_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_LazyDiscrTree_Cache_empty_spec__0_spec__0___redArg___closed__0);
v___x_4629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4629_, 0, v___x_4628_);
return v___x_4629_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1(void){
_start:
{
lean_object* v___x_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; 
v___x_4630_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_4631_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0);
v___x_4632_ = lean_unsigned_to_nat(0u);
v___x_4633_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_4633_, 0, v___x_4632_);
lean_ctor_set(v___x_4633_, 1, v___x_4632_);
lean_ctor_set(v___x_4633_, 2, v___x_4632_);
lean_ctor_set(v___x_4633_, 3, v___x_4632_);
lean_ctor_set(v___x_4633_, 4, v___x_4631_);
lean_ctor_set(v___x_4633_, 5, v___x_4631_);
lean_ctor_set(v___x_4633_, 6, v___x_4631_);
lean_ctor_set(v___x_4633_, 7, v___x_4631_);
lean_ctor_set(v___x_4633_, 8, v___x_4631_);
lean_ctor_set(v___x_4633_, 9, v___x_4631_);
lean_ctor_set(v___x_4633_, 10, v___x_4631_);
lean_ctor_set(v___x_4633_, 11, v___x_4630_);
return v___x_4633_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2(void){
_start:
{
lean_object* v___x_4634_; lean_object* v___x_4635_; lean_object* v___x_4636_; 
v___x_4634_ = lean_unsigned_to_nat(32u);
v___x_4635_ = lean_mk_empty_array_with_capacity(v___x_4634_);
v___x_4636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4636_, 0, v___x_4635_);
return v___x_4636_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3(void){
_start:
{
size_t v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; lean_object* v___x_4641_; lean_object* v___x_4642_; 
v___x_4637_ = ((size_t)5ULL);
v___x_4638_ = lean_unsigned_to_nat(0u);
v___x_4639_ = lean_unsigned_to_nat(32u);
v___x_4640_ = lean_mk_empty_array_with_capacity(v___x_4639_);
v___x_4641_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2);
v___x_4642_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4642_, 0, v___x_4641_);
lean_ctor_set(v___x_4642_, 1, v___x_4640_);
lean_ctor_set(v___x_4642_, 2, v___x_4638_);
lean_ctor_set(v___x_4642_, 3, v___x_4638_);
lean_ctor_set_usize(v___x_4642_, 4, v___x_4637_);
return v___x_4642_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4(void){
_start:
{
lean_object* v___x_4643_; lean_object* v___x_4644_; 
v___x_4643_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0);
v___x_4644_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4644_, 0, v___x_4643_);
lean_ctor_set(v___x_4644_, 1, v___x_4643_);
lean_ctor_set(v___x_4644_, 2, v___x_4643_);
lean_ctor_set(v___x_4644_, 3, v___x_4643_);
lean_ctor_set(v___x_4644_, 4, v___x_4643_);
return v___x_4644_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5(void){
_start:
{
lean_object* v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; 
v___x_4645_ = lean_box(1);
v___x_4646_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3);
v___x_4647_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0);
v___x_4648_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4648_, 0, v___x_4647_);
lean_ctor_set(v___x_4648_, 1, v___x_4646_);
lean_ctor_set(v___x_4648_, 2, v___x_4645_);
return v___x_4648_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__7(void){
_start:
{
lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; 
v___x_4651_ = lean_unsigned_to_nat(1u);
v___x_4652_ = l_Lean_firstFrontendMacroScope;
v___x_4653_ = lean_nat_add(v___x_4652_, v___x_4651_);
return v___x_4653_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__9(void){
_start:
{
lean_object* v___x_4658_; uint64_t v___x_4659_; lean_object* v___x_4660_; 
v___x_4658_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3);
v___x_4659_ = 0ULL;
v___x_4660_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4660_, 0, v___x_4658_);
lean_ctor_set_uint64(v___x_4660_, sizeof(void*)*1, v___x_4659_);
return v___x_4660_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10(void){
_start:
{
lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4664_; 
v___x_4661_ = lean_unsigned_to_nat(0u);
v___x_4662_ = l_Lean_Options_empty;
v___x_4663_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6));
v___x_4664_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4664_, 0, v___x_4663_);
lean_ctor_set(v___x_4664_, 1, v___x_4662_);
lean_ctor_set(v___x_4664_, 2, v___x_4663_);
lean_ctor_set(v___x_4664_, 3, v___x_4661_);
lean_ctor_set(v___x_4664_, 4, v___x_4661_);
lean_ctor_set(v___x_4664_, 5, v___x_4661_);
return v___x_4664_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11(void){
_start:
{
lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; 
v___x_4665_ = l_Lean_NameSet_empty;
v___x_4666_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3);
v___x_4667_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4667_, 0, v___x_4666_);
lean_ctor_set(v___x_4667_, 1, v___x_4666_);
lean_ctor_set(v___x_4667_, 2, v___x_4665_);
return v___x_4667_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12(void){
_start:
{
lean_object* v___x_4668_; lean_object* v___x_4669_; uint8_t v___x_4670_; lean_object* v___x_4671_; 
v___x_4668_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3);
v___x_4669_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0);
v___x_4670_ = 1;
v___x_4671_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4671_, 0, v___x_4669_);
lean_ctor_set(v___x_4671_, 1, v___x_4669_);
lean_ctor_set(v___x_4671_, 2, v___x_4668_);
lean_ctor_set_uint8(v___x_4671_, sizeof(void*)*3, v___x_4670_);
return v___x_4671_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13(void){
_start:
{
lean_object* v___x_4672_; lean_object* v___x_4673_; 
v___x_4672_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0);
v___x_4673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4673_, 0, v___x_4672_);
lean_ctor_set(v___x_4673_, 1, v___x_4672_);
return v___x_4673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(lean_object* v_cctx_4674_, lean_object* v_env_4675_, lean_object* v_modName_4676_, lean_object* v_d_4677_, lean_object* v_cacheRef_4678_, lean_object* v_tree_4679_, lean_object* v_act_4680_, lean_object* v_c_4681_){
_start:
{
uint8_t v___x_4683_; 
lean_inc_ref(v_c_4681_);
v___x_4683_ = l_Lean_AsyncConstantInfo_isUnsafe(v_c_4681_);
if (v___x_4683_ == 0)
{
lean_object* v_name_4684_; uint8_t v___x_4685_; 
v_name_4684_ = lean_ctor_get(v_c_4681_, 0);
lean_inc_n(v_name_4684_, 2);
lean_inc_ref(v_env_4675_);
v___x_4685_ = l_Lean_Meta_LazyDiscrTree_blacklistInsertion(v_env_4675_, v_name_4684_);
if (v___x_4685_ == 0)
{
lean_object* v___x_4686_; uint8_t v___x_4687_; lean_object* v___x_4688_; lean_object* v_ngen_4689_; lean_object* v_core_4690_; lean_object* v_meta_4691_; lean_object* v___x_4693_; uint8_t v_isShared_4694_; uint8_t v_isSharedCheck_4817_; 
v___x_4686_ = lean_box(1);
v___x_4687_ = 1;
v___x_4688_ = lean_st_ref_get(v_cacheRef_4678_);
v_ngen_4689_ = lean_ctor_get(v___x_4688_, 0);
v_core_4690_ = lean_ctor_get(v___x_4688_, 1);
v_meta_4691_ = lean_ctor_get(v___x_4688_, 2);
v_isSharedCheck_4817_ = !lean_is_exclusive(v___x_4688_);
if (v_isSharedCheck_4817_ == 0)
{
v___x_4693_ = v___x_4688_;
v_isShared_4694_ = v_isSharedCheck_4817_;
goto v_resetjp_4692_;
}
else
{
lean_inc(v_meta_4691_);
lean_inc(v_core_4690_);
lean_inc(v_ngen_4689_);
lean_dec(v___x_4688_);
v___x_4693_ = lean_box(0);
v_isShared_4694_ = v_isSharedCheck_4817_;
goto v_resetjp_4692_;
}
v_resetjp_4692_:
{
lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; lean_object* v___x_4701_; uint8_t v___x_4702_; uint8_t v___x_4703_; uint8_t v___x_4704_; lean_object* v___x_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___y_4720_; uint16_t v___y_4721_; lean_object* v_fileName_4722_; lean_object* v_fileMap_4723_; lean_object* v_currNamespace_4724_; lean_object* v_openDecls_4725_; lean_object* v_initHeartbeats_4726_; lean_object* v_maxHeartbeats_4727_; lean_object* v_quotContext_4728_; lean_object* v_currMacroScope_4729_; lean_object* v_cancelTk_x3f_4730_; lean_object* v_inheritedTraceOptions_4731_; lean_object* v_currRecDepth_4732_; lean_object* v_ref_4733_; uint8_t v_suppressElabErrors_4734_; uint8_t v_checkDeprecated_4735_; uint8_t v_isRecordingDeps_4736_; lean_object* v___x_4763_; lean_object* v___x_4764_; lean_object* v_toCold_4765_; lean_object* v_currRecDepth_4766_; lean_object* v_ref_4767_; uint8_t v_suppressElabErrors_4768_; uint8_t v_checkDeprecated_4769_; uint8_t v_isRecordingDeps_4770_; lean_object* v_fileName_4771_; lean_object* v_fileMap_4772_; lean_object* v_options_4773_; lean_object* v_currNamespace_4774_; lean_object* v_openDecls_4775_; lean_object* v_initHeartbeats_4776_; lean_object* v_maxHeartbeats_4777_; lean_object* v_quotContext_4778_; lean_object* v_currMacroScope_4779_; lean_object* v_cancelTk_x3f_4780_; uint8_t v___y_4782_; lean_object* v___y_4783_; uint16_t v___y_4784_; lean_object* v___y_4807_; 
v___x_4695_ = lean_unsigned_to_nat(0u);
v___x_4696_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4697_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3);
v___x_4698_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4699_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4699_, 0, v___x_4696_);
lean_ctor_set(v___x_4699_, 1, v_meta_4691_);
lean_ctor_set(v___x_4699_, 2, v___x_4686_);
lean_ctor_set(v___x_4699_, 3, v___x_4697_);
lean_ctor_set(v___x_4699_, 4, v___x_4698_);
lean_inc_ref(v_ngen_4689_);
v___x_4700_ = l_Lean_Meta_LazyDiscrTree_Cache_empty(v_ngen_4689_);
v___x_4701_ = lean_st_ref_swap(v_cacheRef_4678_, v___x_4700_);
lean_dec(v___x_4701_);
v___x_4702_ = 2;
v___x_4703_ = 0;
v___x_4704_ = 2;
v___x_4705_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_4705_, 0, v___x_4685_);
lean_ctor_set_uint8(v___x_4705_, 1, v___x_4685_);
lean_ctor_set_uint8(v___x_4705_, 2, v___x_4685_);
lean_ctor_set_uint8(v___x_4705_, 3, v___x_4685_);
lean_ctor_set_uint8(v___x_4705_, 4, v___x_4685_);
lean_ctor_set_uint8(v___x_4705_, 5, v___x_4687_);
lean_ctor_set_uint8(v___x_4705_, 6, v___x_4687_);
lean_ctor_set_uint8(v___x_4705_, 7, v___x_4685_);
lean_ctor_set_uint8(v___x_4705_, 8, v___x_4687_);
lean_ctor_set_uint8(v___x_4705_, 9, v___x_4702_);
lean_ctor_set_uint8(v___x_4705_, 10, v___x_4703_);
lean_ctor_set_uint8(v___x_4705_, 11, v___x_4687_);
lean_ctor_set_uint8(v___x_4705_, 12, v___x_4687_);
lean_ctor_set_uint8(v___x_4705_, 13, v___x_4687_);
lean_ctor_set_uint8(v___x_4705_, 14, v___x_4704_);
lean_ctor_set_uint8(v___x_4705_, 15, v___x_4687_);
lean_ctor_set_uint8(v___x_4705_, 16, v___x_4687_);
lean_ctor_set_uint8(v___x_4705_, 17, v___x_4687_);
lean_ctor_set_uint8(v___x_4705_, 18, v___x_4687_);
lean_ctor_set_uint8(v___x_4705_, 19, v___x_4685_);
v___x_4706_ = l_Lean_Meta_Config_toConfigWithKey(v___x_4705_);
v___x_4707_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5);
v___x_4708_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6));
v___x_4709_ = lean_box(0);
v___x_4710_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4710_, 0, v___x_4706_);
lean_ctor_set(v___x_4710_, 1, v___x_4686_);
lean_ctor_set(v___x_4710_, 2, v___x_4707_);
lean_ctor_set(v___x_4710_, 3, v___x_4708_);
lean_ctor_set(v___x_4710_, 4, v___x_4709_);
lean_ctor_set(v___x_4710_, 5, v___x_4695_);
lean_ctor_set(v___x_4710_, 6, v___x_4709_);
lean_ctor_set_uint8(v___x_4710_, sizeof(void*)*7, v___x_4685_);
lean_ctor_set_uint8(v___x_4710_, sizeof(void*)*7 + 1, v___x_4685_);
lean_ctor_set_uint8(v___x_4710_, sizeof(void*)*7 + 2, v___x_4685_);
lean_ctor_set_uint8(v___x_4710_, sizeof(void*)*7 + 3, v___x_4687_);
v___x_4711_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__7, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__7_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__7);
v___x_4712_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__8));
v___x_4713_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__9, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__9_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__9);
v___x_4714_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10);
v___x_4715_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11);
v___x_4716_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12);
v___x_4717_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4717_, 0, v_env_4675_);
lean_ctor_set(v___x_4717_, 1, v___x_4711_);
lean_ctor_set(v___x_4717_, 2, v_ngen_4689_);
lean_ctor_set(v___x_4717_, 3, v___x_4712_);
lean_ctor_set(v___x_4717_, 4, v___x_4713_);
lean_ctor_set(v___x_4717_, 5, v_core_4690_);
lean_ctor_set(v___x_4717_, 6, v___x_4714_);
lean_ctor_set(v___x_4717_, 7, v___x_4715_);
lean_ctor_set(v___x_4717_, 8, v___x_4716_);
lean_ctor_set(v___x_4717_, 9, v___x_4708_);
v___x_4718_ = lean_st_mk_ref(v___x_4717_);
v___x_4763_ = l_Lean_inheritedTraceOptions;
v___x_4764_ = lean_st_ref_get(v___x_4763_);
v_toCold_4765_ = lean_ctor_get(v_cctx_4674_, 0);
lean_inc_ref(v_toCold_4765_);
v_currRecDepth_4766_ = lean_ctor_get(v_cctx_4674_, 1);
lean_inc(v_currRecDepth_4766_);
v_ref_4767_ = lean_ctor_get(v_cctx_4674_, 2);
lean_inc(v_ref_4767_);
v_suppressElabErrors_4768_ = lean_ctor_get_uint8(v_cctx_4674_, sizeof(void*)*3 + 2);
v_checkDeprecated_4769_ = lean_ctor_get_uint8(v_cctx_4674_, sizeof(void*)*3 + 3);
v_isRecordingDeps_4770_ = lean_ctor_get_uint8(v_cctx_4674_, sizeof(void*)*3 + 4);
lean_dec_ref(v_cctx_4674_);
v_fileName_4771_ = lean_ctor_get(v_toCold_4765_, 0);
lean_inc_ref(v_fileName_4771_);
v_fileMap_4772_ = lean_ctor_get(v_toCold_4765_, 1);
lean_inc_ref(v_fileMap_4772_);
v_options_4773_ = lean_ctor_get(v_toCold_4765_, 2);
lean_inc_ref(v_options_4773_);
v_currNamespace_4774_ = lean_ctor_get(v_toCold_4765_, 4);
lean_inc(v_currNamespace_4774_);
v_openDecls_4775_ = lean_ctor_get(v_toCold_4765_, 5);
lean_inc(v_openDecls_4775_);
v_initHeartbeats_4776_ = lean_ctor_get(v_toCold_4765_, 6);
lean_inc(v_initHeartbeats_4776_);
v_maxHeartbeats_4777_ = lean_ctor_get(v_toCold_4765_, 7);
lean_inc(v_maxHeartbeats_4777_);
v_quotContext_4778_ = lean_ctor_get(v_toCold_4765_, 8);
lean_inc(v_quotContext_4778_);
v_currMacroScope_4779_ = lean_ctor_get(v_toCold_4765_, 9);
lean_inc(v_currMacroScope_4779_);
v_cancelTk_x3f_4780_ = lean_ctor_get(v_toCold_4765_, 10);
lean_inc(v_cancelTk_x3f_4780_);
lean_dec_ref(v_toCold_4765_);
if (v_isRecordingDeps_4770_ == 0)
{
v___y_4807_ = v_options_4773_;
goto v___jp_4806_;
}
else
{
lean_object* v___x_4816_; 
v___x_4816_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_4773_);
v___y_4807_ = v___x_4816_;
goto v___jp_4806_;
}
v___jp_4719_:
{
lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; 
v___x_4737_ = l_Lean_maxRecDepth;
v___x_4738_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(v___y_4720_, v___x_4737_);
v___x_4739_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_4739_, 0, v_fileName_4722_);
lean_ctor_set(v___x_4739_, 1, v_fileMap_4723_);
lean_ctor_set(v___x_4739_, 2, v___y_4720_);
lean_ctor_set(v___x_4739_, 3, v___x_4738_);
lean_ctor_set(v___x_4739_, 4, v_currNamespace_4724_);
lean_ctor_set(v___x_4739_, 5, v_openDecls_4725_);
lean_ctor_set(v___x_4739_, 6, v_initHeartbeats_4726_);
lean_ctor_set(v___x_4739_, 7, v_maxHeartbeats_4727_);
lean_ctor_set(v___x_4739_, 8, v_quotContext_4728_);
lean_ctor_set(v___x_4739_, 9, v_currMacroScope_4729_);
lean_ctor_set(v___x_4739_, 10, v_cancelTk_x3f_4730_);
lean_ctor_set(v___x_4739_, 11, v_inheritedTraceOptions_4731_);
v___x_4740_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_4740_, 0, v___x_4739_);
lean_ctor_set(v___x_4740_, 1, v_currRecDepth_4732_);
lean_ctor_set(v___x_4740_, 2, v_ref_4733_);
lean_ctor_set_uint16(v___x_4740_, sizeof(void*)*3, v___y_4721_);
lean_ctor_set_uint8(v___x_4740_, sizeof(void*)*3 + 2, v_suppressElabErrors_4734_);
lean_ctor_set_uint8(v___x_4740_, sizeof(void*)*3 + 3, v_checkDeprecated_4735_);
lean_ctor_set_uint8(v___x_4740_, sizeof(void*)*3 + 4, v_isRecordingDeps_4736_);
v___x_4741_ = lean_st_mk_ref(v___x_4699_);
lean_inc(v___x_4718_);
lean_inc(v___x_4741_);
lean_inc(v_name_4684_);
v___x_4742_ = lean_apply_7(v_act_4680_, v_name_4684_, v_c_4681_, v___x_4710_, v___x_4741_, v___x_4740_, v___x_4718_, lean_box(0));
if (lean_obj_tag(v___x_4742_) == 0)
{
lean_object* v_a_4743_; lean_object* v___x_4744_; lean_object* v___x_4745_; lean_object* v_ngen_4746_; lean_object* v_cache_4747_; lean_object* v_cache_4748_; lean_object* v___x_4750_; 
lean_dec(v_name_4684_);
lean_dec(v_modName_4676_);
v_a_4743_ = lean_ctor_get(v___x_4742_, 0);
lean_inc(v_a_4743_);
lean_dec_ref_known(v___x_4742_, 1);
v___x_4744_ = lean_st_ref_get(v___x_4741_);
lean_dec(v___x_4741_);
v___x_4745_ = lean_st_ref_get(v___x_4718_);
lean_dec(v___x_4718_);
v_ngen_4746_ = lean_ctor_get(v___x_4745_, 2);
lean_inc_ref(v_ngen_4746_);
v_cache_4747_ = lean_ctor_get(v___x_4745_, 5);
lean_inc_ref(v_cache_4747_);
lean_dec(v___x_4745_);
v_cache_4748_ = lean_ctor_get(v___x_4744_, 1);
lean_inc_ref(v_cache_4748_);
lean_dec(v___x_4744_);
if (v_isShared_4694_ == 0)
{
lean_ctor_set(v___x_4693_, 2, v_cache_4748_);
lean_ctor_set(v___x_4693_, 1, v_cache_4747_);
lean_ctor_set(v___x_4693_, 0, v_ngen_4746_);
v___x_4750_ = v___x_4693_;
goto v_reusejp_4749_;
}
else
{
lean_object* v_reuseFailAlloc_4757_; 
v_reuseFailAlloc_4757_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4757_, 0, v_ngen_4746_);
lean_ctor_set(v_reuseFailAlloc_4757_, 1, v_cache_4747_);
lean_ctor_set(v_reuseFailAlloc_4757_, 2, v_cache_4748_);
v___x_4750_ = v_reuseFailAlloc_4757_;
goto v_reusejp_4749_;
}
v_reusejp_4749_:
{
lean_object* v___x_4751_; lean_object* v___x_4752_; uint8_t v___x_4753_; 
v___x_4751_ = lean_st_ref_swap(v_cacheRef_4678_, v___x_4750_);
lean_dec(v___x_4751_);
v___x_4752_ = lean_array_get_size(v_a_4743_);
v___x_4753_ = lean_nat_dec_lt(v___x_4695_, v___x_4752_);
if (v___x_4753_ == 0)
{
lean_dec(v_a_4743_);
return v_tree_4679_;
}
else
{
size_t v___x_4754_; size_t v___x_4755_; lean_object* v___x_4756_; 
v___x_4754_ = ((size_t)0ULL);
v___x_4755_ = lean_usize_of_nat(v___x_4752_);
v___x_4756_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1___redArg(v_a_4743_, v___x_4754_, v___x_4755_, v_tree_4679_);
lean_dec(v_a_4743_);
return v___x_4756_;
}
}
}
else
{
lean_object* v_a_4758_; lean_object* v___x_4759_; lean_object* v___x_4760_; lean_object* v___x_4761_; lean_object* v___x_4762_; 
lean_dec(v___x_4741_);
lean_dec(v___x_4718_);
lean_del_object(v___x_4693_);
v_a_4758_ = lean_ctor_get(v___x_4742_, 0);
lean_inc(v_a_4758_);
lean_dec_ref_known(v___x_4742_, 1);
v___x_4759_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4759_, 0, v_modName_4676_);
lean_ctor_set(v___x_4759_, 1, v_name_4684_);
lean_ctor_set(v___x_4759_, 2, v_a_4758_);
v___x_4760_ = lean_st_ref_take(v_d_4677_);
v___x_4761_ = lean_array_push(v___x_4760_, v___x_4759_);
v___x_4762_ = lean_st_ref_put(v_d_4677_, v___x_4761_);
return v_tree_4679_;
}
}
v___jp_4781_:
{
lean_object* v___x_4785_; lean_object* v_env_4786_; lean_object* v_nextMacroScope_4787_; lean_object* v_ngen_4788_; lean_object* v_auxDeclNGen_4789_; lean_object* v_traceState_4790_; lean_object* v_recordedDeps_4791_; lean_object* v_messages_4792_; lean_object* v_infoState_4793_; lean_object* v_snapshotTasks_4794_; lean_object* v___x_4796_; uint8_t v_isShared_4797_; uint8_t v_isSharedCheck_4804_; 
v___x_4785_ = lean_st_ref_take(v___x_4718_);
v_env_4786_ = lean_ctor_get(v___x_4785_, 0);
v_nextMacroScope_4787_ = lean_ctor_get(v___x_4785_, 1);
v_ngen_4788_ = lean_ctor_get(v___x_4785_, 2);
v_auxDeclNGen_4789_ = lean_ctor_get(v___x_4785_, 3);
v_traceState_4790_ = lean_ctor_get(v___x_4785_, 4);
v_recordedDeps_4791_ = lean_ctor_get(v___x_4785_, 6);
v_messages_4792_ = lean_ctor_get(v___x_4785_, 7);
v_infoState_4793_ = lean_ctor_get(v___x_4785_, 8);
v_snapshotTasks_4794_ = lean_ctor_get(v___x_4785_, 9);
v_isSharedCheck_4804_ = !lean_is_exclusive(v___x_4785_);
if (v_isSharedCheck_4804_ == 0)
{
lean_object* v_unused_4805_; 
v_unused_4805_ = lean_ctor_get(v___x_4785_, 5);
lean_dec(v_unused_4805_);
v___x_4796_ = v___x_4785_;
v_isShared_4797_ = v_isSharedCheck_4804_;
goto v_resetjp_4795_;
}
else
{
lean_inc(v_snapshotTasks_4794_);
lean_inc(v_infoState_4793_);
lean_inc(v_messages_4792_);
lean_inc(v_recordedDeps_4791_);
lean_inc(v_traceState_4790_);
lean_inc(v_auxDeclNGen_4789_);
lean_inc(v_ngen_4788_);
lean_inc(v_nextMacroScope_4787_);
lean_inc(v_env_4786_);
lean_dec(v___x_4785_);
v___x_4796_ = lean_box(0);
v_isShared_4797_ = v_isSharedCheck_4804_;
goto v_resetjp_4795_;
}
v_resetjp_4795_:
{
lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4801_; 
v___x_4798_ = l_Lean_Kernel_enableDiag(v_env_4786_, v___y_4782_);
v___x_4799_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13);
if (v_isShared_4797_ == 0)
{
lean_ctor_set(v___x_4796_, 5, v___x_4799_);
lean_ctor_set(v___x_4796_, 0, v___x_4798_);
v___x_4801_ = v___x_4796_;
goto v_reusejp_4800_;
}
else
{
lean_object* v_reuseFailAlloc_4803_; 
v_reuseFailAlloc_4803_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4803_, 0, v___x_4798_);
lean_ctor_set(v_reuseFailAlloc_4803_, 1, v_nextMacroScope_4787_);
lean_ctor_set(v_reuseFailAlloc_4803_, 2, v_ngen_4788_);
lean_ctor_set(v_reuseFailAlloc_4803_, 3, v_auxDeclNGen_4789_);
lean_ctor_set(v_reuseFailAlloc_4803_, 4, v_traceState_4790_);
lean_ctor_set(v_reuseFailAlloc_4803_, 5, v___x_4799_);
lean_ctor_set(v_reuseFailAlloc_4803_, 6, v_recordedDeps_4791_);
lean_ctor_set(v_reuseFailAlloc_4803_, 7, v_messages_4792_);
lean_ctor_set(v_reuseFailAlloc_4803_, 8, v_infoState_4793_);
lean_ctor_set(v_reuseFailAlloc_4803_, 9, v_snapshotTasks_4794_);
v___x_4801_ = v_reuseFailAlloc_4803_;
goto v_reusejp_4800_;
}
v_reusejp_4800_:
{
lean_object* v___x_4802_; 
v___x_4802_ = lean_st_ref_put(v___x_4718_, v___x_4801_);
v___y_4720_ = v___y_4783_;
v___y_4721_ = v___y_4784_;
v_fileName_4722_ = v_fileName_4771_;
v_fileMap_4723_ = v_fileMap_4772_;
v_currNamespace_4724_ = v_currNamespace_4774_;
v_openDecls_4725_ = v_openDecls_4775_;
v_initHeartbeats_4726_ = v_initHeartbeats_4776_;
v_maxHeartbeats_4727_ = v_maxHeartbeats_4777_;
v_quotContext_4728_ = v_quotContext_4778_;
v_currMacroScope_4729_ = v_currMacroScope_4779_;
v_cancelTk_x3f_4730_ = v_cancelTk_x3f_4780_;
v_inheritedTraceOptions_4731_ = v___x_4764_;
v_currRecDepth_4732_ = v_currRecDepth_4766_;
v_ref_4733_ = v_ref_4767_;
v_suppressElabErrors_4734_ = v_suppressElabErrors_4768_;
v_checkDeprecated_4735_ = v_checkDeprecated_4769_;
v_isRecordingDeps_4736_ = v_isRecordingDeps_4770_;
goto v___jp_4719_;
}
}
}
v___jp_4806_:
{
uint16_t v___x_4808_; lean_object* v___x_4809_; lean_object* v_env_4810_; uint8_t v___x_4811_; uint16_t v___x_4812_; uint16_t v___x_4813_; uint16_t v___x_4814_; uint8_t v___x_4815_; 
v___x_4808_ = l_Lean_OptionFlags_ofOptions(v___y_4807_);
v___x_4809_ = lean_st_ref_get(v___x_4718_);
v_env_4810_ = lean_ctor_get(v___x_4809_, 0);
lean_inc_ref(v_env_4810_);
lean_dec(v___x_4809_);
v___x_4811_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4810_);
lean_dec_ref(v_env_4810_);
v___x_4812_ = 512;
v___x_4813_ = lean_uint16_land(v___x_4808_, v___x_4812_);
v___x_4814_ = 0;
v___x_4815_ = lean_uint16_dec_eq(v___x_4813_, v___x_4814_);
if (v___x_4815_ == 0)
{
if (v___x_4811_ == 0)
{
v___y_4782_ = v___x_4687_;
v___y_4783_ = v___y_4807_;
v___y_4784_ = v___x_4808_;
goto v___jp_4781_;
}
else
{
v___y_4720_ = v___y_4807_;
v___y_4721_ = v___x_4808_;
v_fileName_4722_ = v_fileName_4771_;
v_fileMap_4723_ = v_fileMap_4772_;
v_currNamespace_4724_ = v_currNamespace_4774_;
v_openDecls_4725_ = v_openDecls_4775_;
v_initHeartbeats_4726_ = v_initHeartbeats_4776_;
v_maxHeartbeats_4727_ = v_maxHeartbeats_4777_;
v_quotContext_4728_ = v_quotContext_4778_;
v_currMacroScope_4729_ = v_currMacroScope_4779_;
v_cancelTk_x3f_4730_ = v_cancelTk_x3f_4780_;
v_inheritedTraceOptions_4731_ = v___x_4764_;
v_currRecDepth_4732_ = v_currRecDepth_4766_;
v_ref_4733_ = v_ref_4767_;
v_suppressElabErrors_4734_ = v_suppressElabErrors_4768_;
v_checkDeprecated_4735_ = v_checkDeprecated_4769_;
v_isRecordingDeps_4736_ = v_isRecordingDeps_4770_;
goto v___jp_4719_;
}
}
else
{
if (v___x_4811_ == 0)
{
v___y_4720_ = v___y_4807_;
v___y_4721_ = v___x_4808_;
v_fileName_4722_ = v_fileName_4771_;
v_fileMap_4723_ = v_fileMap_4772_;
v_currNamespace_4724_ = v_currNamespace_4774_;
v_openDecls_4725_ = v_openDecls_4775_;
v_initHeartbeats_4726_ = v_initHeartbeats_4776_;
v_maxHeartbeats_4727_ = v_maxHeartbeats_4777_;
v_quotContext_4728_ = v_quotContext_4778_;
v_currMacroScope_4729_ = v_currMacroScope_4779_;
v_cancelTk_x3f_4730_ = v_cancelTk_x3f_4780_;
v_inheritedTraceOptions_4731_ = v___x_4764_;
v_currRecDepth_4732_ = v_currRecDepth_4766_;
v_ref_4733_ = v_ref_4767_;
v_suppressElabErrors_4734_ = v_suppressElabErrors_4768_;
v_checkDeprecated_4735_ = v_checkDeprecated_4769_;
v_isRecordingDeps_4736_ = v_isRecordingDeps_4770_;
goto v___jp_4719_;
}
else
{
v___y_4782_ = v___x_4685_;
v___y_4783_ = v___y_4807_;
v___y_4784_ = v___x_4808_;
goto v___jp_4781_;
}
}
}
}
}
else
{
lean_dec(v_name_4684_);
lean_dec_ref(v_c_4681_);
lean_dec_ref(v_act_4680_);
lean_dec(v_modName_4676_);
lean_dec_ref(v_env_4675_);
lean_dec_ref(v_cctx_4674_);
return v_tree_4679_;
}
}
else
{
lean_dec_ref(v_c_4681_);
lean_dec_ref(v_act_4680_);
lean_dec(v_modName_4676_);
lean_dec_ref(v_env_4675_);
lean_dec_ref(v_cctx_4674_);
return v_tree_4679_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___boxed(lean_object* v_cctx_4818_, lean_object* v_env_4819_, lean_object* v_modName_4820_, lean_object* v_d_4821_, lean_object* v_cacheRef_4822_, lean_object* v_tree_4823_, lean_object* v_act_4824_, lean_object* v_c_4825_, lean_object* v_a_4826_){
_start:
{
lean_object* v_res_4827_; 
v_res_4827_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_4818_, v_env_4819_, v_modName_4820_, v_d_4821_, v_cacheRef_4822_, v_tree_4823_, v_act_4824_, v_c_4825_);
lean_dec(v_cacheRef_4822_);
lean_dec(v_d_4821_);
return v_res_4827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData(lean_object* v_00_u03b1_4828_, lean_object* v_cctx_4829_, lean_object* v_env_4830_, lean_object* v_modName_4831_, lean_object* v_d_4832_, lean_object* v_cacheRef_4833_, lean_object* v_tree_4834_, lean_object* v_act_4835_, lean_object* v_c_4836_){
_start:
{
lean_object* v___x_4838_; 
v___x_4838_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_4829_, v_env_4830_, v_modName_4831_, v_d_4832_, v_cacheRef_4833_, v_tree_4834_, v_act_4835_, v_c_4836_);
return v___x_4838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___boxed(lean_object* v_00_u03b1_4839_, lean_object* v_cctx_4840_, lean_object* v_env_4841_, lean_object* v_modName_4842_, lean_object* v_d_4843_, lean_object* v_cacheRef_4844_, lean_object* v_tree_4845_, lean_object* v_act_4846_, lean_object* v_c_4847_, lean_object* v_a_4848_){
_start:
{
lean_object* v_res_4849_; 
v_res_4849_ = l_Lean_Meta_LazyDiscrTree_addConstImportData(v_00_u03b1_4839_, v_cctx_4840_, v_env_4841_, v_modName_4842_, v_d_4843_, v_cacheRef_4844_, v_tree_4845_, v_act_4846_, v_c_4847_);
lean_dec(v_cacheRef_4844_);
lean_dec(v_d_4843_);
return v_res_4849_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1(lean_object* v_00_u03b1_4850_, lean_object* v_as_4851_, size_t v_i_4852_, size_t v_stop_4853_, lean_object* v_b_4854_){
_start:
{
lean_object* v___x_4855_; 
v___x_4855_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1___redArg(v_as_4851_, v_i_4852_, v_stop_4853_, v_b_4854_);
return v___x_4855_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1___boxed(lean_object* v_00_u03b1_4856_, lean_object* v_as_4857_, lean_object* v_i_4858_, lean_object* v_stop_4859_, lean_object* v_b_4860_){
_start:
{
size_t v_i_boxed_4861_; size_t v_stop_boxed_4862_; lean_object* v_res_4863_; 
v_i_boxed_4861_ = lean_unbox_usize(v_i_4858_);
lean_dec(v_i_4858_);
v_stop_boxed_4862_ = lean_unbox_usize(v_stop_4859_);
lean_dec(v_stop_4859_);
v_res_4863_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1(v_00_u03b1_4856_, v_as_4857_, v_i_boxed_4861_, v_stop_boxed_4862_, v_b_4860_);
lean_dec_ref(v_as_4857_);
return v_res_4863_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___redArg___closed__0(void){
_start:
{
lean_object* v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; 
v___x_4864_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__0));
v___x_4865_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1);
v___x_4866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4866_, 0, v___x_4865_);
lean_ctor_set(v___x_4866_, 1, v___x_4864_);
return v___x_4866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___redArg(){
_start:
{
lean_object* v___x_4868_; 
v___x_4868_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___redArg___closed__0);
return v___x_4868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___redArg___boxed(lean_object* v___dummy_4869_){
_start:
{
lean_object* v_res_4870_; 
v_res_4870_ = l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___redArg();
return v_res_4870_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0(void){
_start:
{
lean_object* v___x_4871_; 
v___x_4871_ = l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___redArg();
return v___x_4871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults(lean_object* v_00_u03b1_4872_){
_start:
{
lean_object* v___x_4873_; 
v___x_4873_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0);
return v___x_4873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_append___redArg(lean_object* v_x_4874_, lean_object* v_y_4875_){
_start:
{
lean_object* v_tree_4876_; lean_object* v_errors_4877_; lean_object* v_tree_4878_; lean_object* v_errors_4879_; lean_object* v___x_4881_; uint8_t v_isShared_4882_; uint8_t v_isSharedCheck_4888_; 
v_tree_4876_ = lean_ctor_get(v_x_4874_, 0);
lean_inc_ref(v_tree_4876_);
v_errors_4877_ = lean_ctor_get(v_x_4874_, 1);
lean_inc_ref(v_errors_4877_);
lean_dec_ref(v_x_4874_);
v_tree_4878_ = lean_ctor_get(v_y_4875_, 0);
v_errors_4879_ = lean_ctor_get(v_y_4875_, 1);
v_isSharedCheck_4888_ = !lean_is_exclusive(v_y_4875_);
if (v_isSharedCheck_4888_ == 0)
{
v___x_4881_ = v_y_4875_;
v_isShared_4882_ = v_isSharedCheck_4888_;
goto v_resetjp_4880_;
}
else
{
lean_inc(v_errors_4879_);
lean_inc(v_tree_4878_);
lean_dec(v_y_4875_);
v___x_4881_ = lean_box(0);
v_isShared_4882_ = v_isSharedCheck_4888_;
goto v_resetjp_4880_;
}
v_resetjp_4880_:
{
lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4886_; 
v___x_4883_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg(v_tree_4876_, v_tree_4878_);
v___x_4884_ = l_Array_append___redArg(v_errors_4877_, v_errors_4879_);
lean_dec_ref(v_errors_4879_);
if (v_isShared_4882_ == 0)
{
lean_ctor_set(v___x_4881_, 1, v___x_4884_);
lean_ctor_set(v___x_4881_, 0, v___x_4883_);
v___x_4886_ = v___x_4881_;
goto v_reusejp_4885_;
}
else
{
lean_object* v_reuseFailAlloc_4887_; 
v_reuseFailAlloc_4887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4887_, 0, v___x_4883_);
lean_ctor_set(v_reuseFailAlloc_4887_, 1, v___x_4884_);
v___x_4886_ = v_reuseFailAlloc_4887_;
goto v_reusejp_4885_;
}
v_reusejp_4885_:
{
return v___x_4886_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_append(lean_object* v_00_u03b1_4889_, lean_object* v_x_4890_, lean_object* v_y_4891_){
_start:
{
lean_object* v___x_4892_; 
v___x_4892_ = l_Lean_Meta_LazyDiscrTree_InitResults_append___redArg(v_x_4890_, v_y_4891_);
return v___x_4892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___redArg(){
_start:
{
lean_object* v___x_4895_; 
v___x_4895_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___redArg___closed__0));
return v___x_4895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___redArg___boxed(lean_object* v___dummy_4896_){
_start:
{
lean_object* v_res_4897_; 
v_res_4897_ = l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___redArg();
return v_res_4897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_instAppend(lean_object* v_00_u03b1_4898_){
_start:
{
lean_object* v___x_4899_; 
v___x_4899_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___redArg___closed__0));
return v___x_4899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat___redArg(lean_object* v_d_4900_, lean_object* v_tree_4901_){
_start:
{
lean_object* v___x_4903_; lean_object* v___x_4904_; lean_object* v___x_4905_; 
v___x_4903_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_ImportData_new___closed__0));
v___x_4904_ = lean_st_ref_swap(v_d_4900_, v___x_4903_);
v___x_4905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4905_, 0, v_tree_4901_);
lean_ctor_set(v___x_4905_, 1, v___x_4904_);
return v___x_4905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat___redArg___boxed(lean_object* v_d_4906_, lean_object* v_tree_4907_, lean_object* v_a_4908_){
_start:
{
lean_object* v_res_4909_; 
v_res_4909_ = l_Lean_Meta_LazyDiscrTree_toFlat___redArg(v_d_4906_, v_tree_4907_);
lean_dec(v_d_4906_);
return v_res_4909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat(lean_object* v_00_u03b1_4910_, lean_object* v_d_4911_, lean_object* v_tree_4912_){
_start:
{
lean_object* v___x_4914_; 
v___x_4914_ = l_Lean_Meta_LazyDiscrTree_toFlat___redArg(v_d_4911_, v_tree_4912_);
return v___x_4914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat___boxed(lean_object* v_00_u03b1_4915_, lean_object* v_d_4916_, lean_object* v_tree_4917_, lean_object* v_a_4918_){
_start:
{
lean_object* v_res_4919_; 
v_res_4919_ = l_Lean_Meta_LazyDiscrTree_toFlat(v_00_u03b1_4915_, v_d_4916_, v_tree_4917_);
lean_dec(v_d_4916_);
return v_res_4919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(lean_object* v_cctx_4920_, lean_object* v_env_4921_, lean_object* v_act_4922_, lean_object* v_d_4923_, lean_object* v_cacheRef_4924_, lean_object* v_tree_4925_, lean_object* v_mname_4926_, lean_object* v_mdata_4927_, lean_object* v_i_4928_){
_start:
{
lean_object* v_constants_4930_; lean_object* v___x_4931_; uint8_t v___x_4932_; 
v_constants_4930_ = lean_ctor_get(v_mdata_4927_, 2);
v___x_4931_ = lean_array_get_size(v_constants_4930_);
v___x_4932_ = lean_nat_dec_lt(v_i_4928_, v___x_4931_);
if (v___x_4932_ == 0)
{
lean_dec(v_i_4928_);
lean_dec(v_mname_4926_);
lean_dec_ref(v_act_4922_);
lean_dec_ref(v_env_4921_);
lean_dec_ref(v_cctx_4920_);
return v_tree_4925_;
}
else
{
lean_object* v___x_4933_; lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; 
v___x_4933_ = lean_array_fget_borrowed(v_constants_4930_, v_i_4928_);
lean_inc(v___x_4933_);
v___x_4934_ = l_Lean_AsyncConstantInfo_ofConstantInfo(v___x_4933_);
lean_inc_ref(v_act_4922_);
lean_inc(v_mname_4926_);
lean_inc_ref(v_env_4921_);
lean_inc_ref(v_cctx_4920_);
v___x_4935_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_4920_, v_env_4921_, v_mname_4926_, v_d_4923_, v_cacheRef_4924_, v_tree_4925_, v_act_4922_, v___x_4934_);
v___x_4936_ = lean_unsigned_to_nat(1u);
v___x_4937_ = lean_nat_add(v_i_4928_, v___x_4936_);
lean_dec(v_i_4928_);
v_tree_4925_ = v___x_4935_;
v_i_4928_ = v___x_4937_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg___boxed(lean_object* v_cctx_4939_, lean_object* v_env_4940_, lean_object* v_act_4941_, lean_object* v_d_4942_, lean_object* v_cacheRef_4943_, lean_object* v_tree_4944_, lean_object* v_mname_4945_, lean_object* v_mdata_4946_, lean_object* v_i_4947_, lean_object* v_a_4948_){
_start:
{
lean_object* v_res_4949_; 
v_res_4949_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(v_cctx_4939_, v_env_4940_, v_act_4941_, v_d_4942_, v_cacheRef_4943_, v_tree_4944_, v_mname_4945_, v_mdata_4946_, v_i_4947_);
lean_dec_ref(v_mdata_4946_);
lean_dec(v_cacheRef_4943_);
lean_dec(v_d_4942_);
return v_res_4949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule(lean_object* v_00_u03b1_4950_, lean_object* v_cctx_4951_, lean_object* v_env_4952_, lean_object* v_act_4953_, lean_object* v_d_4954_, lean_object* v_cacheRef_4955_, lean_object* v_tree_4956_, lean_object* v_mname_4957_, lean_object* v_mdata_4958_, lean_object* v_i_4959_){
_start:
{
lean_object* v___x_4961_; 
v___x_4961_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(v_cctx_4951_, v_env_4952_, v_act_4953_, v_d_4954_, v_cacheRef_4955_, v_tree_4956_, v_mname_4957_, v_mdata_4958_, v_i_4959_);
return v___x_4961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule___boxed(lean_object* v_00_u03b1_4962_, lean_object* v_cctx_4963_, lean_object* v_env_4964_, lean_object* v_act_4965_, lean_object* v_d_4966_, lean_object* v_cacheRef_4967_, lean_object* v_tree_4968_, lean_object* v_mname_4969_, lean_object* v_mdata_4970_, lean_object* v_i_4971_, lean_object* v_a_4972_){
_start:
{
lean_object* v_res_4973_; 
v_res_4973_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule(v_00_u03b1_4962_, v_cctx_4963_, v_env_4964_, v_act_4965_, v_d_4966_, v_cacheRef_4967_, v_tree_4968_, v_mname_4969_, v_mdata_4970_, v_i_4971_);
lean_dec_ref(v_mdata_4970_);
lean_dec(v_cacheRef_4967_);
lean_dec(v_d_4966_);
return v_res_4973_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg(lean_object* v_cctx_4974_, lean_object* v_env_4975_, lean_object* v_act_4976_, lean_object* v_d_4977_, lean_object* v_cacheRef_4978_, lean_object* v_tree_4979_, lean_object* v_start_4980_, lean_object* v_stop_4981_){
_start:
{
uint8_t v___x_4983_; 
v___x_4983_ = lean_nat_dec_lt(v_start_4980_, v_stop_4981_);
if (v___x_4983_ == 0)
{
lean_object* v___x_4984_; 
lean_dec(v_start_4980_);
lean_dec_ref(v_act_4976_);
lean_dec_ref(v_env_4975_);
lean_dec_ref(v_cctx_4974_);
v___x_4984_ = l_Lean_Meta_LazyDiscrTree_toFlat___redArg(v_d_4977_, v_tree_4979_);
return v___x_4984_;
}
else
{
lean_object* v___x_4985_; lean_object* v_moduleNames_4986_; lean_object* v_moduleData_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; lean_object* v_mname_4990_; lean_object* v_mdata_4991_; lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; lean_object* v___x_4995_; 
v___x_4985_ = l_Lean_Environment_header(v_env_4975_);
v_moduleNames_4986_ = lean_ctor_get(v___x_4985_, 4);
lean_inc_ref(v_moduleNames_4986_);
v_moduleData_4987_ = lean_ctor_get(v___x_4985_, 7);
lean_inc_ref(v_moduleData_4987_);
lean_dec_ref(v___x_4985_);
v___x_4988_ = lean_box(0);
v___x_4989_ = l_Lean_instInhabitedModuleData_default;
v_mname_4990_ = lean_array_get(v___x_4988_, v_moduleNames_4986_, v_start_4980_);
lean_dec_ref(v_moduleNames_4986_);
v_mdata_4991_ = lean_array_get(v___x_4989_, v_moduleData_4987_, v_start_4980_);
lean_dec_ref(v_moduleData_4987_);
v___x_4992_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_act_4976_);
lean_inc_ref(v_env_4975_);
lean_inc_ref(v_cctx_4974_);
v___x_4993_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(v_cctx_4974_, v_env_4975_, v_act_4976_, v_d_4977_, v_cacheRef_4978_, v_tree_4979_, v_mname_4990_, v_mdata_4991_, v___x_4992_);
lean_dec(v_mdata_4991_);
v___x_4994_ = lean_unsigned_to_nat(1u);
v___x_4995_ = lean_nat_add(v_start_4980_, v___x_4994_);
lean_dec(v_start_4980_);
v_tree_4979_ = v___x_4993_;
v_start_4980_ = v___x_4995_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg___boxed(lean_object* v_cctx_4997_, lean_object* v_env_4998_, lean_object* v_act_4999_, lean_object* v_d_5000_, lean_object* v_cacheRef_5001_, lean_object* v_tree_5002_, lean_object* v_start_5003_, lean_object* v_stop_5004_, lean_object* v_a_5005_){
_start:
{
lean_object* v_res_5006_; 
v_res_5006_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg(v_cctx_4997_, v_env_4998_, v_act_4999_, v_d_5000_, v_cacheRef_5001_, v_tree_5002_, v_start_5003_, v_stop_5004_);
lean_dec(v_stop_5004_);
lean_dec(v_cacheRef_5001_);
lean_dec(v_d_5000_);
return v_res_5006_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go(lean_object* v_00_u03b1_5007_, lean_object* v_cctx_5008_, lean_object* v_env_5009_, lean_object* v_act_5010_, lean_object* v_d_5011_, lean_object* v_cacheRef_5012_, lean_object* v_tree_5013_, lean_object* v_start_5014_, lean_object* v_stop_5015_){
_start:
{
lean_object* v___x_5017_; 
v___x_5017_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg(v_cctx_5008_, v_env_5009_, v_act_5010_, v_d_5011_, v_cacheRef_5012_, v_tree_5013_, v_start_5014_, v_stop_5015_);
return v___x_5017_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___boxed(lean_object* v_00_u03b1_5018_, lean_object* v_cctx_5019_, lean_object* v_env_5020_, lean_object* v_act_5021_, lean_object* v_d_5022_, lean_object* v_cacheRef_5023_, lean_object* v_tree_5024_, lean_object* v_start_5025_, lean_object* v_stop_5026_, lean_object* v_a_5027_){
_start:
{
lean_object* v_res_5028_; 
v_res_5028_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go(v_00_u03b1_5018_, v_cctx_5019_, v_env_5020_, v_act_5021_, v_d_5022_, v_cacheRef_5023_, v_tree_5024_, v_start_5025_, v_stop_5026_);
lean_dec(v_stop_5026_);
lean_dec(v_cacheRef_5023_);
lean_dec(v_d_5022_);
return v_res_5028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___redArg(lean_object* v_cctx_5029_, lean_object* v_ngen_5030_, lean_object* v_env_5031_, lean_object* v_act_5032_, lean_object* v_start_5033_, lean_object* v_stop_5034_){
_start:
{
lean_object* v___x_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; lean_object* v___x_5040_; 
v___x_5036_ = l_Lean_Meta_LazyDiscrTree_Cache_empty(v_ngen_5030_);
v___x_5037_ = lean_st_mk_ref(v___x_5036_);
v___x_5038_ = l_Lean_Meta_LazyDiscrTree_ImportData_new();
v___x_5039_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1);
v___x_5040_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg(v_cctx_5029_, v_env_5031_, v_act_5032_, v___x_5038_, v___x_5037_, v___x_5039_, v_start_5033_, v_stop_5034_);
lean_dec(v___x_5037_);
lean_dec(v___x_5038_);
return v___x_5040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___redArg___boxed(lean_object* v_cctx_5041_, lean_object* v_ngen_5042_, lean_object* v_env_5043_, lean_object* v_act_5044_, lean_object* v_start_5045_, lean_object* v_stop_5046_, lean_object* v_a_5047_){
_start:
{
lean_object* v_res_5048_; 
v_res_5048_ = l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___redArg(v_cctx_5041_, v_ngen_5042_, v_env_5043_, v_act_5044_, v_start_5045_, v_stop_5046_);
lean_dec(v_stop_5046_);
return v_res_5048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq(lean_object* v_00_u03b1_5049_, lean_object* v_cctx_5050_, lean_object* v_ngen_5051_, lean_object* v_env_5052_, lean_object* v_act_5053_, lean_object* v_start_5054_, lean_object* v_stop_5055_){
_start:
{
lean_object* v___x_5057_; 
v___x_5057_ = l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___redArg(v_cctx_5050_, v_ngen_5051_, v_env_5052_, v_act_5053_, v_start_5054_, v_stop_5055_);
return v___x_5057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed(lean_object* v_00_u03b1_5058_, lean_object* v_cctx_5059_, lean_object* v_ngen_5060_, lean_object* v_env_5061_, lean_object* v_act_5062_, lean_object* v_start_5063_, lean_object* v_stop_5064_, lean_object* v_a_5065_){
_start:
{
lean_object* v_res_5066_; 
v_res_5066_ = l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq(v_00_u03b1_5058_, v_cctx_5059_, v_ngen_5060_, v_env_5061_, v_act_5062_, v_start_5063_, v_stop_5064_);
lean_dec(v_stop_5064_);
return v_res_5066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___redArg___lam__0(lean_object* v_inst_5067_, lean_object* v_x1_5068_, lean_object* v_x2_5069_){
_start:
{
lean_object* v___x_5070_; lean_object* v___x_5071_; 
v___x_5070_ = lean_task_get_own(v_x2_5069_);
v___x_5071_ = lean_apply_2(v_inst_5067_, v_x1_5068_, v___x_5070_);
return v___x_5071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___redArg(lean_object* v_inst_5072_, lean_object* v_z_5073_, lean_object* v_tasks_5074_){
_start:
{
lean_object* v___x_5075_; lean_object* v___x_5076_; lean_object* v___x_5077_; uint8_t v___x_5078_; 
v___x_5075_ = lean_unsigned_to_nat(0u);
v___x_5076_ = lean_array_get_size(v_tasks_5074_);
v___x_5077_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__9));
v___x_5078_ = lean_nat_dec_lt(v___x_5075_, v___x_5076_);
if (v___x_5078_ == 0)
{
lean_dec_ref(v_tasks_5074_);
lean_dec(v_inst_5072_);
return v_z_5073_;
}
else
{
lean_object* v___f_5079_; size_t v___x_5080_; size_t v___x_5081_; lean_object* v___x_5082_; 
v___f_5079_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_combineGet___redArg___lam__0), 3, 1);
lean_closure_set(v___f_5079_, 0, v_inst_5072_);
v___x_5080_ = ((size_t)0ULL);
v___x_5081_ = lean_usize_of_nat(v___x_5076_);
v___x_5082_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_5077_, v___f_5079_, v_tasks_5074_, v___x_5080_, v___x_5081_, v_z_5073_);
return v___x_5082_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet(lean_object* v_00_u03b1_5083_, lean_object* v_inst_5084_, lean_object* v_z_5085_, lean_object* v_tasks_5086_){
_start:
{
lean_object* v___x_5087_; 
v___x_5087_ = l_Lean_Meta_LazyDiscrTree_combineGet___redArg(v_inst_5084_, v_z_5085_, v_tasks_5086_);
return v___x_5087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg___lam__0(lean_object* v_toPure_5088_, lean_object* v___x_5089_, lean_object* v_____r_5090_){
_start:
{
lean_object* v___x_5091_; 
v___x_5091_ = lean_apply_2(v_toPure_5088_, lean_box(0), v___x_5089_);
return v___x_5091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg___lam__1(lean_object* v_toPure_5092_, lean_object* v_setNGen_5093_, lean_object* v_toBind_5094_, lean_object* v_ngen_5095_){
_start:
{
lean_object* v_namePrefix_5096_; lean_object* v_idx_5097_; lean_object* v___x_5099_; uint8_t v_isShared_5100_; uint8_t v_isSharedCheck_5111_; 
v_namePrefix_5096_ = lean_ctor_get(v_ngen_5095_, 0);
v_idx_5097_ = lean_ctor_get(v_ngen_5095_, 1);
v_isSharedCheck_5111_ = !lean_is_exclusive(v_ngen_5095_);
if (v_isSharedCheck_5111_ == 0)
{
v___x_5099_ = v_ngen_5095_;
v_isShared_5100_ = v_isSharedCheck_5111_;
goto v_resetjp_5098_;
}
else
{
lean_inc(v_idx_5097_);
lean_inc(v_namePrefix_5096_);
lean_dec(v_ngen_5095_);
v___x_5099_ = lean_box(0);
v_isShared_5100_ = v_isSharedCheck_5111_;
goto v_resetjp_5098_;
}
v_resetjp_5098_:
{
lean_object* v___x_5101_; lean_object* v___x_5102_; lean_object* v___x_5104_; 
lean_inc(v_idx_5097_);
lean_inc(v_namePrefix_5096_);
v___x_5101_ = l_Lean_Name_num___override(v_namePrefix_5096_, v_idx_5097_);
v___x_5102_ = lean_unsigned_to_nat(1u);
if (v_isShared_5100_ == 0)
{
lean_ctor_set(v___x_5099_, 1, v___x_5102_);
lean_ctor_set(v___x_5099_, 0, v___x_5101_);
v___x_5104_ = v___x_5099_;
goto v_reusejp_5103_;
}
else
{
lean_object* v_reuseFailAlloc_5110_; 
v_reuseFailAlloc_5110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5110_, 0, v___x_5101_);
lean_ctor_set(v_reuseFailAlloc_5110_, 1, v___x_5102_);
v___x_5104_ = v_reuseFailAlloc_5110_;
goto v_reusejp_5103_;
}
v_reusejp_5103_:
{
lean_object* v___f_5105_; lean_object* v___x_5106_; lean_object* v___x_5107_; lean_object* v___x_5108_; lean_object* v___x_5109_; 
v___f_5105_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5105_, 0, v_toPure_5092_);
lean_closure_set(v___f_5105_, 1, v___x_5104_);
v___x_5106_ = lean_nat_add(v_idx_5097_, v___x_5102_);
lean_dec(v_idx_5097_);
v___x_5107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5107_, 0, v_namePrefix_5096_);
lean_ctor_set(v___x_5107_, 1, v___x_5106_);
v___x_5108_ = lean_apply_1(v_setNGen_5093_, v___x_5107_);
v___x_5109_ = lean_apply_4(v_toBind_5094_, lean_box(0), lean_box(0), v___x_5108_, v___f_5105_);
return v___x_5109_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg(lean_object* v_inst_5112_, lean_object* v_inst_5113_){
_start:
{
lean_object* v_toApplicative_5114_; lean_object* v_toBind_5115_; lean_object* v_getNGen_5116_; lean_object* v_setNGen_5117_; lean_object* v_toPure_5118_; lean_object* v___f_5119_; lean_object* v___x_5120_; 
v_toApplicative_5114_ = lean_ctor_get(v_inst_5112_, 0);
lean_inc_ref(v_toApplicative_5114_);
v_toBind_5115_ = lean_ctor_get(v_inst_5112_, 1);
lean_inc_n(v_toBind_5115_, 2);
lean_dec_ref(v_inst_5112_);
v_getNGen_5116_ = lean_ctor_get(v_inst_5113_, 0);
lean_inc(v_getNGen_5116_);
v_setNGen_5117_ = lean_ctor_get(v_inst_5113_, 1);
lean_inc(v_setNGen_5117_);
lean_dec_ref(v_inst_5113_);
v_toPure_5118_ = lean_ctor_get(v_toApplicative_5114_, 1);
lean_inc(v_toPure_5118_);
lean_dec_ref(v_toApplicative_5114_);
v___f_5119_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg___lam__1), 4, 3);
lean_closure_set(v___f_5119_, 0, v_toPure_5118_);
lean_closure_set(v___f_5119_, 1, v_setNGen_5117_);
lean_closure_set(v___f_5119_, 2, v_toBind_5115_);
v___x_5120_ = lean_apply_4(v_toBind_5115_, lean_box(0), lean_box(0), v_getNGen_5116_, v___f_5119_);
return v___x_5120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen(lean_object* v_M_5121_, lean_object* v_inst_5122_, lean_object* v_inst_5123_){
_start:
{
lean_object* v___x_5124_; 
v___x_5124_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg(v_inst_5122_, v_inst_5123_);
return v___x_5124_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg(lean_object* v_cctx_5125_, lean_object* v_env_5126_, lean_object* v_modName_5127_, lean_object* v_d_5128_, lean_object* v_val_5129_, lean_object* v_act_5130_, lean_object* v_as_5131_, size_t v_sz_5132_, size_t v_i_5133_, lean_object* v_b_5134_){
_start:
{
uint8_t v___x_5136_; 
v___x_5136_ = lean_usize_dec_lt(v_i_5133_, v_sz_5132_);
if (v___x_5136_ == 0)
{
lean_dec_ref(v_act_5130_);
lean_dec(v_modName_5127_);
lean_dec_ref(v_env_5126_);
lean_dec_ref(v_cctx_5125_);
return v_b_5134_;
}
else
{
lean_object* v_a_5137_; lean_object* v___x_5138_; size_t v___x_5139_; size_t v___x_5140_; 
v_a_5137_ = lean_array_uget_borrowed(v_as_5131_, v_i_5133_);
lean_inc(v_a_5137_);
lean_inc_ref(v_act_5130_);
lean_inc(v_modName_5127_);
lean_inc_ref(v_env_5126_);
lean_inc_ref(v_cctx_5125_);
v___x_5138_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_5125_, v_env_5126_, v_modName_5127_, v_d_5128_, v_val_5129_, v_b_5134_, v_act_5130_, v_a_5137_);
v___x_5139_ = ((size_t)1ULL);
v___x_5140_ = lean_usize_add(v_i_5133_, v___x_5139_);
v_i_5133_ = v___x_5140_;
v_b_5134_ = v___x_5138_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg___boxed(lean_object* v_cctx_5142_, lean_object* v_env_5143_, lean_object* v_modName_5144_, lean_object* v_d_5145_, lean_object* v_val_5146_, lean_object* v_act_5147_, lean_object* v_as_5148_, lean_object* v_sz_5149_, lean_object* v_i_5150_, lean_object* v_b_5151_, lean_object* v___y_5152_){
_start:
{
size_t v_sz_boxed_5153_; size_t v_i_boxed_5154_; lean_object* v_res_5155_; 
v_sz_boxed_5153_ = lean_unbox_usize(v_sz_5149_);
lean_dec(v_sz_5149_);
v_i_boxed_5154_ = lean_unbox_usize(v_i_5150_);
lean_dec(v_i_5150_);
v_res_5155_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg(v_cctx_5142_, v_env_5143_, v_modName_5144_, v_d_5145_, v_val_5146_, v_act_5147_, v_as_5148_, v_sz_boxed_5153_, v_i_boxed_5154_, v_b_5151_);
lean_dec_ref(v_as_5148_);
lean_dec(v_val_5146_);
lean_dec(v_d_5145_);
return v_res_5155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(lean_object* v_cctx_5156_, lean_object* v_ngen_5157_, lean_object* v_env_5158_, lean_object* v_d_5159_, lean_object* v_act_5160_){
_start:
{
lean_object* v___x_5162_; lean_object* v_mainModule_5163_; lean_object* v___x_5164_; lean_object* v___x_5165_; lean_object* v___x_5166_; uint8_t v___x_5167_; lean_object* v___x_5168_; size_t v_sz_5169_; size_t v___x_5170_; lean_object* v___x_5171_; 
v___x_5162_ = l_Lean_Environment_header(v_env_5158_);
v_mainModule_5163_ = lean_ctor_get(v___x_5162_, 0);
lean_inc(v_mainModule_5163_);
lean_dec_ref(v___x_5162_);
v___x_5164_ = l_Lean_Meta_LazyDiscrTree_Cache_empty(v_ngen_5157_);
v___x_5165_ = lean_st_mk_ref(v___x_5164_);
v___x_5166_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1);
v___x_5167_ = 1;
v___x_5168_ = l_Lean_Environment_getLocalConstantInfos(v_env_5158_, v___x_5167_);
v_sz_5169_ = lean_array_size(v___x_5168_);
v___x_5170_ = ((size_t)0ULL);
v___x_5171_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg(v_cctx_5156_, v_env_5158_, v_mainModule_5163_, v_d_5159_, v___x_5165_, v_act_5160_, v___x_5168_, v_sz_5169_, v___x_5170_, v___x_5166_);
lean_dec_ref(v___x_5168_);
lean_dec(v___x_5165_);
return v___x_5171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg___boxed(lean_object* v_cctx_5172_, lean_object* v_ngen_5173_, lean_object* v_env_5174_, lean_object* v_d_5175_, lean_object* v_act_5176_, lean_object* v_a_5177_){
_start:
{
lean_object* v_res_5178_; 
v_res_5178_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(v_cctx_5172_, v_ngen_5173_, v_env_5174_, v_d_5175_, v_act_5176_);
lean_dec(v_d_5175_);
return v_res_5178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree(lean_object* v_00_u03b1_5179_, lean_object* v_cctx_5180_, lean_object* v_ngen_5181_, lean_object* v_env_5182_, lean_object* v_d_5183_, lean_object* v_act_5184_){
_start:
{
lean_object* v___x_5186_; 
v___x_5186_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(v_cctx_5180_, v_ngen_5181_, v_env_5182_, v_d_5183_, v_act_5184_);
return v___x_5186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___boxed(lean_object* v_00_u03b1_5187_, lean_object* v_cctx_5188_, lean_object* v_ngen_5189_, lean_object* v_env_5190_, lean_object* v_d_5191_, lean_object* v_act_5192_, lean_object* v_a_5193_){
_start:
{
lean_object* v_res_5194_; 
v_res_5194_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree(v_00_u03b1_5187_, v_cctx_5188_, v_ngen_5189_, v_env_5190_, v_d_5191_, v_act_5192_);
lean_dec(v_d_5191_);
return v_res_5194_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0(lean_object* v_00_u03b1_5195_, lean_object* v_cctx_5196_, lean_object* v_env_5197_, lean_object* v_modName_5198_, lean_object* v_d_5199_, lean_object* v_val_5200_, lean_object* v_act_5201_, lean_object* v_as_5202_, size_t v_sz_5203_, size_t v_i_5204_, lean_object* v_b_5205_){
_start:
{
lean_object* v___x_5207_; 
v___x_5207_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg(v_cctx_5196_, v_env_5197_, v_modName_5198_, v_d_5199_, v_val_5200_, v_act_5201_, v_as_5202_, v_sz_5203_, v_i_5204_, v_b_5205_);
return v___x_5207_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___boxed(lean_object* v_00_u03b1_5208_, lean_object* v_cctx_5209_, lean_object* v_env_5210_, lean_object* v_modName_5211_, lean_object* v_d_5212_, lean_object* v_val_5213_, lean_object* v_act_5214_, lean_object* v_as_5215_, lean_object* v_sz_5216_, lean_object* v_i_5217_, lean_object* v_b_5218_, lean_object* v___y_5219_){
_start:
{
size_t v_sz_boxed_5220_; size_t v_i_boxed_5221_; lean_object* v_res_5222_; 
v_sz_boxed_5220_ = lean_unbox_usize(v_sz_5216_);
lean_dec(v_sz_5216_);
v_i_boxed_5221_ = lean_unbox_usize(v_i_5217_);
lean_dec(v_i_5217_);
v_res_5222_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0(v_00_u03b1_5208_, v_cctx_5209_, v_env_5210_, v_modName_5211_, v_d_5212_, v_val_5213_, v_act_5214_, v_as_5215_, v_sz_boxed_5220_, v_i_boxed_5221_, v_b_5218_);
lean_dec_ref(v_as_5215_);
lean_dec(v_val_5213_);
lean_dec(v_d_5212_);
return v_res_5222_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(lean_object* v_x_5223_, lean_object* v_x_5224_, lean_object* v___y_5225_, lean_object* v___y_5226_, lean_object* v___y_5227_, lean_object* v___y_5228_){
_start:
{
if (lean_obj_tag(v_x_5224_) == 0)
{
lean_object* v___x_5230_; 
v___x_5230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5230_, 0, v_x_5223_);
return v___x_5230_;
}
else
{
lean_object* v_head_5231_; lean_object* v_tail_5232_; lean_object* v___x_5233_; 
v_head_5231_ = lean_ctor_get(v_x_5224_, 0);
lean_inc(v_head_5231_);
v_tail_5232_ = lean_ctor_get(v_x_5224_, 1);
lean_inc(v_tail_5232_);
lean_dec_ref_known(v_x_5224_, 2);
v___x_5233_ = l_Lean_Meta_LazyDiscrTree_dropKey___redArg(v_x_5223_, v_head_5231_, v___y_5225_, v___y_5226_, v___y_5227_, v___y_5228_);
if (lean_obj_tag(v___x_5233_) == 0)
{
lean_object* v_a_5234_; 
v_a_5234_ = lean_ctor_get(v___x_5233_, 0);
lean_inc(v_a_5234_);
lean_dec_ref_known(v___x_5233_, 1);
v_x_5223_ = v_a_5234_;
v_x_5224_ = v_tail_5232_;
goto _start;
}
else
{
lean_dec(v_tail_5232_);
return v___x_5233_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg___boxed(lean_object* v_x_5236_, lean_object* v_x_5237_, lean_object* v___y_5238_, lean_object* v___y_5239_, lean_object* v___y_5240_, lean_object* v___y_5241_, lean_object* v___y_5242_){
_start:
{
lean_object* v_res_5243_; 
v_res_5243_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_x_5236_, v_x_5237_, v___y_5238_, v___y_5239_, v___y_5240_, v___y_5241_);
lean_dec(v___y_5241_);
lean_dec_ref(v___y_5240_);
lean_dec(v___y_5239_);
lean_dec_ref(v___y_5238_);
return v_res_5243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys___redArg(lean_object* v_t_5244_, lean_object* v_keys_5245_, lean_object* v_a_5246_, lean_object* v_a_5247_, lean_object* v_a_5248_, lean_object* v_a_5249_){
_start:
{
lean_object* v___x_5251_; 
v___x_5251_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_t_5244_, v_keys_5245_, v_a_5246_, v_a_5247_, v_a_5248_, v_a_5249_);
return v___x_5251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys___redArg___boxed(lean_object* v_t_5252_, lean_object* v_keys_5253_, lean_object* v_a_5254_, lean_object* v_a_5255_, lean_object* v_a_5256_, lean_object* v_a_5257_, lean_object* v_a_5258_){
_start:
{
lean_object* v_res_5259_; 
v_res_5259_ = l_Lean_Meta_LazyDiscrTree_dropKeys___redArg(v_t_5252_, v_keys_5253_, v_a_5254_, v_a_5255_, v_a_5256_, v_a_5257_);
lean_dec(v_a_5257_);
lean_dec_ref(v_a_5256_);
lean_dec(v_a_5255_);
lean_dec_ref(v_a_5254_);
return v_res_5259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys(lean_object* v_00_u03b1_5260_, lean_object* v_t_5261_, lean_object* v_keys_5262_, lean_object* v_a_5263_, lean_object* v_a_5264_, lean_object* v_a_5265_, lean_object* v_a_5266_){
_start:
{
lean_object* v___x_5268_; 
v___x_5268_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_t_5261_, v_keys_5262_, v_a_5263_, v_a_5264_, v_a_5265_, v_a_5266_);
return v___x_5268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys___boxed(lean_object* v_00_u03b1_5269_, lean_object* v_t_5270_, lean_object* v_keys_5271_, lean_object* v_a_5272_, lean_object* v_a_5273_, lean_object* v_a_5274_, lean_object* v_a_5275_, lean_object* v_a_5276_){
_start:
{
lean_object* v_res_5277_; 
v_res_5277_ = l_Lean_Meta_LazyDiscrTree_dropKeys(v_00_u03b1_5269_, v_t_5270_, v_keys_5271_, v_a_5272_, v_a_5273_, v_a_5274_, v_a_5275_);
lean_dec(v_a_5275_);
lean_dec_ref(v_a_5274_);
lean_dec(v_a_5273_);
lean_dec_ref(v_a_5272_);
return v_res_5277_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0(lean_object* v_00_u03b1_5278_, lean_object* v_x_5279_, lean_object* v_x_5280_, lean_object* v___y_5281_, lean_object* v___y_5282_, lean_object* v___y_5283_, lean_object* v___y_5284_){
_start:
{
lean_object* v___x_5286_; 
v___x_5286_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_x_5279_, v_x_5280_, v___y_5281_, v___y_5282_, v___y_5283_, v___y_5284_);
return v___x_5286_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___boxed(lean_object* v_00_u03b1_5287_, lean_object* v_x_5288_, lean_object* v_x_5289_, lean_object* v___y_5290_, lean_object* v___y_5291_, lean_object* v___y_5292_, lean_object* v___y_5293_, lean_object* v___y_5294_){
_start:
{
lean_object* v_res_5295_; 
v_res_5295_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0(v_00_u03b1_5287_, v_x_5288_, v_x_5289_, v___y_5290_, v___y_5291_, v___y_5292_, v___y_5293_);
lean_dec(v___y_5293_);
lean_dec_ref(v___y_5292_);
lean_dec(v___y_5291_);
lean_dec_ref(v___y_5290_);
return v_res_5295_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(lean_object* v_as_5296_, size_t v_sz_5297_, size_t v_i_5298_, lean_object* v_b_5299_, lean_object* v___y_5300_, lean_object* v___y_5301_, lean_object* v___y_5302_, lean_object* v___y_5303_, lean_object* v___y_5304_){
_start:
{
uint8_t v___x_5306_; 
v___x_5306_ = lean_usize_dec_lt(v_i_5298_, v_sz_5297_);
if (v___x_5306_ == 0)
{
lean_object* v___x_5307_; 
v___x_5307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5307_, 0, v_b_5299_);
return v___x_5307_;
}
else
{
lean_object* v_a_5308_; lean_object* v___x_5309_; 
v_a_5308_ = lean_array_uget_borrowed(v_as_5296_, v_i_5298_);
v___x_5309_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(v_a_5308_, v_b_5299_, v___y_5300_, v___y_5301_, v___y_5302_, v___y_5303_, v___y_5304_);
if (lean_obj_tag(v___x_5309_) == 0)
{
lean_object* v_a_5310_; lean_object* v___x_5312_; uint8_t v_isShared_5313_; uint8_t v_isSharedCheck_5322_; 
v_a_5310_ = lean_ctor_get(v___x_5309_, 0);
v_isSharedCheck_5322_ = !lean_is_exclusive(v___x_5309_);
if (v_isSharedCheck_5322_ == 0)
{
v___x_5312_ = v___x_5309_;
v_isShared_5313_ = v_isSharedCheck_5322_;
goto v_resetjp_5311_;
}
else
{
lean_inc(v_a_5310_);
lean_dec(v___x_5309_);
v___x_5312_ = lean_box(0);
v_isShared_5313_ = v_isSharedCheck_5322_;
goto v_resetjp_5311_;
}
v_resetjp_5311_:
{
if (lean_obj_tag(v_a_5310_) == 0)
{
lean_object* v_a_5314_; lean_object* v___x_5316_; 
v_a_5314_ = lean_ctor_get(v_a_5310_, 0);
lean_inc(v_a_5314_);
lean_dec_ref_known(v_a_5310_, 1);
if (v_isShared_5313_ == 0)
{
lean_ctor_set(v___x_5312_, 0, v_a_5314_);
v___x_5316_ = v___x_5312_;
goto v_reusejp_5315_;
}
else
{
lean_object* v_reuseFailAlloc_5317_; 
v_reuseFailAlloc_5317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5317_, 0, v_a_5314_);
v___x_5316_ = v_reuseFailAlloc_5317_;
goto v_reusejp_5315_;
}
v_reusejp_5315_:
{
return v___x_5316_;
}
}
else
{
lean_object* v_a_5318_; size_t v___x_5319_; size_t v___x_5320_; 
lean_del_object(v___x_5312_);
v_a_5318_ = lean_ctor_get(v_a_5310_, 0);
lean_inc(v_a_5318_);
lean_dec_ref_known(v_a_5310_, 1);
v___x_5319_ = ((size_t)1ULL);
v___x_5320_ = lean_usize_add(v_i_5298_, v___x_5319_);
v_i_5298_ = v___x_5320_;
v_b_5299_ = v_a_5318_;
goto _start;
}
}
}
else
{
lean_object* v_a_5323_; lean_object* v___x_5325_; uint8_t v_isShared_5326_; uint8_t v_isSharedCheck_5330_; 
v_a_5323_ = lean_ctor_get(v___x_5309_, 0);
v_isSharedCheck_5330_ = !lean_is_exclusive(v___x_5309_);
if (v_isSharedCheck_5330_ == 0)
{
v___x_5325_ = v___x_5309_;
v_isShared_5326_ = v_isSharedCheck_5330_;
goto v_resetjp_5324_;
}
else
{
lean_inc(v_a_5323_);
lean_dec(v___x_5309_);
v___x_5325_ = lean_box(0);
v_isShared_5326_ = v_isSharedCheck_5330_;
goto v_resetjp_5324_;
}
v_resetjp_5324_:
{
lean_object* v___x_5328_; 
if (v_isShared_5326_ == 0)
{
v___x_5328_ = v___x_5325_;
goto v_reusejp_5327_;
}
else
{
lean_object* v_reuseFailAlloc_5329_; 
v_reuseFailAlloc_5329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5329_, 0, v_a_5323_);
v___x_5328_ = v_reuseFailAlloc_5329_;
goto v_reusejp_5327_;
}
v_reusejp_5327_:
{
return v___x_5328_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(lean_object* v_next_5331_, lean_object* v_a_5332_, lean_object* v_a_5333_, lean_object* v_a_5334_, lean_object* v_a_5335_, lean_object* v_a_5336_){
_start:
{
lean_object* v___x_5338_; uint8_t v___x_5339_; 
v___x_5338_ = lean_unsigned_to_nat(0u);
v___x_5339_ = lean_nat_dec_eq(v_next_5331_, v___x_5338_);
if (v___x_5339_ == 0)
{
lean_object* v___x_5340_; 
v___x_5340_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_next_5331_, v_a_5332_, v_a_5333_, v_a_5334_, v_a_5335_, v_a_5336_);
if (lean_obj_tag(v___x_5340_) == 0)
{
lean_object* v_a_5341_; lean_object* v_snd_5342_; lean_object* v_fst_5343_; lean_object* v_fst_5344_; lean_object* v_snd_5345_; lean_object* v___x_5346_; 
v_a_5341_ = lean_ctor_get(v___x_5340_, 0);
lean_inc(v_a_5341_);
lean_dec_ref_known(v___x_5340_, 1);
v_snd_5342_ = lean_ctor_get(v_a_5341_, 1);
lean_inc(v_snd_5342_);
v_fst_5343_ = lean_ctor_get(v_a_5341_, 0);
lean_inc(v_fst_5343_);
lean_dec(v_a_5341_);
v_fst_5344_ = lean_ctor_get(v_snd_5342_, 0);
lean_inc(v_fst_5344_);
v_snd_5345_ = lean_ctor_get(v_snd_5342_, 1);
lean_inc(v_snd_5345_);
lean_dec(v_snd_5342_);
v___x_5346_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_fst_5344_, v_a_5332_, v_a_5333_, v_a_5334_, v_a_5335_, v_a_5336_);
if (lean_obj_tag(v___x_5346_) == 0)
{
lean_object* v_a_5347_; lean_object* v_buckets_5348_; lean_object* v___x_5349_; size_t v_sz_5350_; size_t v___x_5351_; lean_object* v___x_5352_; 
v_a_5347_ = lean_ctor_get(v___x_5346_, 0);
lean_inc(v_a_5347_);
lean_dec_ref_known(v___x_5346_, 1);
v_buckets_5348_ = lean_ctor_get(v_snd_5345_, 1);
v___x_5349_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v_sz_5350_ = lean_array_size(v_buckets_5348_);
v___x_5351_ = ((size_t)0ULL);
v___x_5352_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(v_buckets_5348_, v_sz_5350_, v___x_5351_, v___x_5349_, v_a_5332_, v_a_5333_, v_a_5334_, v_a_5335_, v_a_5336_);
if (lean_obj_tag(v___x_5352_) == 0)
{
lean_object* v_a_5353_; lean_object* v___x_5355_; uint8_t v_isShared_5356_; uint8_t v_isSharedCheck_5366_; 
v_a_5353_ = lean_ctor_get(v___x_5352_, 0);
v_isSharedCheck_5366_ = !lean_is_exclusive(v___x_5352_);
if (v_isSharedCheck_5366_ == 0)
{
v___x_5355_ = v___x_5352_;
v_isShared_5356_ = v_isSharedCheck_5366_;
goto v_resetjp_5354_;
}
else
{
lean_inc(v_a_5353_);
lean_dec(v___x_5352_);
v___x_5355_ = lean_box(0);
v_isShared_5356_ = v_isSharedCheck_5366_;
goto v_resetjp_5354_;
}
v_resetjp_5354_:
{
lean_object* v___x_5357_; lean_object* v___x_5358_; lean_object* v___x_5359_; lean_object* v___x_5360_; lean_object* v___x_5361_; lean_object* v___x_5362_; lean_object* v___x_5364_; 
v___x_5357_ = lean_st_ref_take(v_a_5332_);
v___x_5358_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5358_, 0, v___x_5349_);
lean_ctor_set(v___x_5358_, 1, v_fst_5344_);
lean_ctor_set(v___x_5358_, 2, v_snd_5345_);
lean_ctor_set(v___x_5358_, 3, v___x_5349_);
v___x_5359_ = lean_array_set(v___x_5357_, v_next_5331_, v___x_5358_);
v___x_5360_ = lean_st_ref_put(v_a_5332_, v___x_5359_);
v___x_5361_ = l_Array_append___redArg(v_fst_5343_, v_a_5347_);
lean_dec(v_a_5347_);
v___x_5362_ = l_Array_append___redArg(v___x_5361_, v_a_5353_);
lean_dec(v_a_5353_);
if (v_isShared_5356_ == 0)
{
lean_ctor_set(v___x_5355_, 0, v___x_5362_);
v___x_5364_ = v___x_5355_;
goto v_reusejp_5363_;
}
else
{
lean_object* v_reuseFailAlloc_5365_; 
v_reuseFailAlloc_5365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5365_, 0, v___x_5362_);
v___x_5364_ = v_reuseFailAlloc_5365_;
goto v_reusejp_5363_;
}
v_reusejp_5363_:
{
return v___x_5364_;
}
}
}
else
{
lean_dec(v_a_5347_);
lean_dec(v_snd_5345_);
lean_dec(v_fst_5344_);
lean_dec(v_fst_5343_);
return v___x_5352_;
}
}
else
{
lean_dec(v_snd_5345_);
lean_dec(v_fst_5344_);
lean_dec(v_fst_5343_);
return v___x_5346_;
}
}
else
{
lean_object* v_a_5367_; lean_object* v___x_5369_; uint8_t v_isShared_5370_; uint8_t v_isSharedCheck_5374_; 
v_a_5367_ = lean_ctor_get(v___x_5340_, 0);
v_isSharedCheck_5374_ = !lean_is_exclusive(v___x_5340_);
if (v_isSharedCheck_5374_ == 0)
{
v___x_5369_ = v___x_5340_;
v_isShared_5370_ = v_isSharedCheck_5374_;
goto v_resetjp_5368_;
}
else
{
lean_inc(v_a_5367_);
lean_dec(v___x_5340_);
v___x_5369_ = lean_box(0);
v_isShared_5370_ = v_isSharedCheck_5374_;
goto v_resetjp_5368_;
}
v_resetjp_5368_:
{
lean_object* v___x_5372_; 
if (v_isShared_5370_ == 0)
{
v___x_5372_ = v___x_5369_;
goto v_reusejp_5371_;
}
else
{
lean_object* v_reuseFailAlloc_5373_; 
v_reuseFailAlloc_5373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5373_, 0, v_a_5367_);
v___x_5372_ = v_reuseFailAlloc_5373_;
goto v_reusejp_5371_;
}
v_reusejp_5371_:
{
return v___x_5372_;
}
}
}
}
else
{
lean_object* v___x_5375_; lean_object* v___x_5376_; 
v___x_5375_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___x_5376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5376_, 0, v___x_5375_);
return v___x_5376_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(lean_object* v_a_5377_, lean_object* v_a_5378_, lean_object* v___y_5379_, lean_object* v___y_5380_, lean_object* v___y_5381_, lean_object* v___y_5382_, lean_object* v___y_5383_){
_start:
{
if (lean_obj_tag(v_a_5377_) == 0)
{
lean_object* v___x_5385_; lean_object* v___x_5386_; 
v___x_5385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5385_, 0, v_a_5378_);
v___x_5386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5386_, 0, v___x_5385_);
return v___x_5386_;
}
else
{
lean_object* v_value_5387_; lean_object* v_tail_5388_; lean_object* v___x_5389_; 
v_value_5387_ = lean_ctor_get(v_a_5377_, 1);
v_tail_5388_ = lean_ctor_get(v_a_5377_, 2);
v___x_5389_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_value_5387_, v___y_5379_, v___y_5380_, v___y_5381_, v___y_5382_, v___y_5383_);
if (lean_obj_tag(v___x_5389_) == 0)
{
lean_object* v_a_5390_; lean_object* v___x_5391_; 
v_a_5390_ = lean_ctor_get(v___x_5389_, 0);
lean_inc(v_a_5390_);
lean_dec_ref_known(v___x_5389_, 1);
v___x_5391_ = l_Array_append___redArg(v_a_5378_, v_a_5390_);
lean_dec(v_a_5390_);
v_a_5377_ = v_tail_5388_;
v_a_5378_ = v___x_5391_;
goto _start;
}
else
{
lean_object* v_a_5393_; lean_object* v___x_5395_; uint8_t v_isShared_5396_; uint8_t v_isSharedCheck_5400_; 
lean_dec_ref(v_a_5378_);
v_a_5393_ = lean_ctor_get(v___x_5389_, 0);
v_isSharedCheck_5400_ = !lean_is_exclusive(v___x_5389_);
if (v_isSharedCheck_5400_ == 0)
{
v___x_5395_ = v___x_5389_;
v_isShared_5396_ = v_isSharedCheck_5400_;
goto v_resetjp_5394_;
}
else
{
lean_inc(v_a_5393_);
lean_dec(v___x_5389_);
v___x_5395_ = lean_box(0);
v_isShared_5396_ = v_isSharedCheck_5400_;
goto v_resetjp_5394_;
}
v_resetjp_5394_:
{
lean_object* v___x_5398_; 
if (v_isShared_5396_ == 0)
{
v___x_5398_ = v___x_5395_;
goto v_reusejp_5397_;
}
else
{
lean_object* v_reuseFailAlloc_5399_; 
v_reuseFailAlloc_5399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5399_, 0, v_a_5393_);
v___x_5398_ = v_reuseFailAlloc_5399_;
goto v_reusejp_5397_;
}
v_reusejp_5397_:
{
return v___x_5398_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg___boxed(lean_object* v_a_5401_, lean_object* v_a_5402_, lean_object* v___y_5403_, lean_object* v___y_5404_, lean_object* v___y_5405_, lean_object* v___y_5406_, lean_object* v___y_5407_, lean_object* v___y_5408_){
_start:
{
lean_object* v_res_5409_; 
v_res_5409_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(v_a_5401_, v_a_5402_, v___y_5403_, v___y_5404_, v___y_5405_, v___y_5406_, v___y_5407_);
lean_dec(v___y_5407_);
lean_dec_ref(v___y_5406_);
lean_dec(v___y_5405_);
lean_dec_ref(v___y_5404_);
lean_dec(v___y_5403_);
lean_dec(v_a_5401_);
return v_res_5409_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg___boxed(lean_object* v_as_5410_, lean_object* v_sz_5411_, lean_object* v_i_5412_, lean_object* v_b_5413_, lean_object* v___y_5414_, lean_object* v___y_5415_, lean_object* v___y_5416_, lean_object* v___y_5417_, lean_object* v___y_5418_, lean_object* v___y_5419_){
_start:
{
size_t v_sz_boxed_5420_; size_t v_i_boxed_5421_; lean_object* v_res_5422_; 
v_sz_boxed_5420_ = lean_unbox_usize(v_sz_5411_);
lean_dec(v_sz_5411_);
v_i_boxed_5421_ = lean_unbox_usize(v_i_5412_);
lean_dec(v_i_5412_);
v_res_5422_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(v_as_5410_, v_sz_boxed_5420_, v_i_boxed_5421_, v_b_5413_, v___y_5414_, v___y_5415_, v___y_5416_, v___y_5417_, v___y_5418_);
lean_dec(v___y_5418_);
lean_dec_ref(v___y_5417_);
lean_dec(v___y_5416_);
lean_dec_ref(v___y_5415_);
lean_dec(v___y_5414_);
lean_dec_ref(v_as_5410_);
return v_res_5422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg___boxed(lean_object* v_next_5423_, lean_object* v_a_5424_, lean_object* v_a_5425_, lean_object* v_a_5426_, lean_object* v_a_5427_, lean_object* v_a_5428_, lean_object* v_a_5429_){
_start:
{
lean_object* v_res_5430_; 
v_res_5430_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_next_5423_, v_a_5424_, v_a_5425_, v_a_5426_, v_a_5427_, v_a_5428_);
lean_dec(v_a_5428_);
lean_dec_ref(v_a_5427_);
lean_dec(v_a_5426_);
lean_dec_ref(v_a_5425_);
lean_dec(v_a_5424_);
lean_dec(v_next_5423_);
return v_res_5430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux(lean_object* v_00_u03b1_5431_, lean_object* v_next_5432_, lean_object* v_a_5433_, lean_object* v_a_5434_, lean_object* v_a_5435_, lean_object* v_a_5436_, lean_object* v_a_5437_){
_start:
{
lean_object* v___x_5439_; 
v___x_5439_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_next_5432_, v_a_5433_, v_a_5434_, v_a_5435_, v_a_5436_, v_a_5437_);
return v___x_5439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___boxed(lean_object* v_00_u03b1_5440_, lean_object* v_next_5441_, lean_object* v_a_5442_, lean_object* v_a_5443_, lean_object* v_a_5444_, lean_object* v_a_5445_, lean_object* v_a_5446_, lean_object* v_a_5447_){
_start:
{
lean_object* v_res_5448_; 
v_res_5448_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux(v_00_u03b1_5440_, v_next_5441_, v_a_5442_, v_a_5443_, v_a_5444_, v_a_5445_, v_a_5446_);
lean_dec(v_a_5446_);
lean_dec_ref(v_a_5445_);
lean_dec(v_a_5444_);
lean_dec_ref(v_a_5443_);
lean_dec(v_a_5442_);
lean_dec(v_next_5441_);
return v_res_5448_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0(lean_object* v_00_u03b1_5449_, lean_object* v_a_5450_, lean_object* v_a_5451_, lean_object* v___y_5452_, lean_object* v___y_5453_, lean_object* v___y_5454_, lean_object* v___y_5455_, lean_object* v___y_5456_){
_start:
{
lean_object* v___x_5458_; 
v___x_5458_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(v_a_5450_, v_a_5451_, v___y_5452_, v___y_5453_, v___y_5454_, v___y_5455_, v___y_5456_);
return v___x_5458_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___boxed(lean_object* v_00_u03b1_5459_, lean_object* v_a_5460_, lean_object* v_a_5461_, lean_object* v___y_5462_, lean_object* v___y_5463_, lean_object* v___y_5464_, lean_object* v___y_5465_, lean_object* v___y_5466_, lean_object* v___y_5467_){
_start:
{
lean_object* v_res_5468_; 
v_res_5468_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0(v_00_u03b1_5459_, v_a_5460_, v_a_5461_, v___y_5462_, v___y_5463_, v___y_5464_, v___y_5465_, v___y_5466_);
lean_dec(v___y_5466_);
lean_dec_ref(v___y_5465_);
lean_dec(v___y_5464_);
lean_dec_ref(v___y_5463_);
lean_dec(v___y_5462_);
lean_dec(v_a_5460_);
return v_res_5468_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1(lean_object* v_00_u03b1_5469_, lean_object* v_as_5470_, size_t v_sz_5471_, size_t v_i_5472_, lean_object* v_b_5473_, lean_object* v___y_5474_, lean_object* v___y_5475_, lean_object* v___y_5476_, lean_object* v___y_5477_, lean_object* v___y_5478_){
_start:
{
lean_object* v___x_5480_; 
v___x_5480_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(v_as_5470_, v_sz_5471_, v_i_5472_, v_b_5473_, v___y_5474_, v___y_5475_, v___y_5476_, v___y_5477_, v___y_5478_);
return v___x_5480_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___boxed(lean_object* v_00_u03b1_5481_, lean_object* v_as_5482_, lean_object* v_sz_5483_, lean_object* v_i_5484_, lean_object* v_b_5485_, lean_object* v___y_5486_, lean_object* v___y_5487_, lean_object* v___y_5488_, lean_object* v___y_5489_, lean_object* v___y_5490_, lean_object* v___y_5491_){
_start:
{
size_t v_sz_boxed_5492_; size_t v_i_boxed_5493_; lean_object* v_res_5494_; 
v_sz_boxed_5492_ = lean_unbox_usize(v_sz_5483_);
lean_dec(v_sz_5483_);
v_i_boxed_5493_ = lean_unbox_usize(v_i_5484_);
lean_dec(v_i_5484_);
v_res_5494_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1(v_00_u03b1_5481_, v_as_5482_, v_sz_boxed_5492_, v_i_boxed_5493_, v_b_5485_, v___y_5486_, v___y_5487_, v___y_5488_, v___y_5489_, v___y_5490_);
lean_dec(v___y_5490_);
lean_dec_ref(v___y_5489_);
lean_dec(v___y_5488_);
lean_dec_ref(v___y_5487_);
lean_dec(v___y_5486_);
lean_dec_ref(v_as_5482_);
return v_res_5494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg(lean_object* v_next_5495_, lean_object* v_rest_5496_, lean_object* v_a_5497_, lean_object* v_a_5498_, lean_object* v_a_5499_, lean_object* v_a_5500_, lean_object* v_a_5501_){
_start:
{
lean_object* v___x_5503_; uint8_t v___x_5504_; 
v___x_5503_ = lean_unsigned_to_nat(0u);
v___x_5504_ = lean_nat_dec_eq(v_next_5495_, v___x_5503_);
if (v___x_5504_ == 0)
{
lean_object* v___x_5505_; 
v___x_5505_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_next_5495_, v_a_5497_, v_a_5498_, v_a_5499_, v_a_5500_, v_a_5501_);
if (lean_obj_tag(v___x_5505_) == 0)
{
lean_object* v_a_5506_; lean_object* v_snd_5507_; 
v_a_5506_ = lean_ctor_get(v___x_5505_, 0);
lean_inc(v_a_5506_);
lean_dec_ref_known(v___x_5505_, 1);
v_snd_5507_ = lean_ctor_get(v_a_5506_, 1);
lean_inc(v_snd_5507_);
lean_dec(v_a_5506_);
if (lean_obj_tag(v_rest_5496_) == 0)
{
lean_object* v___x_5508_; 
lean_dec(v_snd_5507_);
v___x_5508_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_next_5495_, v_a_5497_, v_a_5498_, v_a_5499_, v_a_5500_, v_a_5501_);
lean_dec(v_next_5495_);
return v___x_5508_;
}
else
{
lean_object* v_fst_5509_; lean_object* v_snd_5510_; lean_object* v_head_5511_; lean_object* v_tail_5512_; lean_object* v___x_5513_; uint8_t v___x_5514_; 
lean_dec(v_next_5495_);
v_fst_5509_ = lean_ctor_get(v_snd_5507_, 0);
lean_inc(v_fst_5509_);
v_snd_5510_ = lean_ctor_get(v_snd_5507_, 1);
lean_inc(v_snd_5510_);
lean_dec(v_snd_5507_);
v_head_5511_ = lean_ctor_get(v_rest_5496_, 0);
v_tail_5512_ = lean_ctor_get(v_rest_5496_, 1);
v___x_5513_ = lean_box(3);
v___x_5514_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_head_5511_, v___x_5513_);
if (v___x_5514_ == 0)
{
lean_object* v___x_5515_; 
lean_dec(v_fst_5509_);
v___x_5515_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_snd_5510_, v_head_5511_, v___x_5503_);
lean_dec(v_snd_5510_);
v_next_5495_ = v___x_5515_;
v_rest_5496_ = v_tail_5512_;
goto _start;
}
else
{
lean_dec(v_snd_5510_);
v_next_5495_ = v_fst_5509_;
v_rest_5496_ = v_tail_5512_;
goto _start;
}
}
}
else
{
lean_object* v_a_5518_; lean_object* v___x_5520_; uint8_t v_isShared_5521_; uint8_t v_isSharedCheck_5525_; 
lean_dec(v_next_5495_);
v_a_5518_ = lean_ctor_get(v___x_5505_, 0);
v_isSharedCheck_5525_ = !lean_is_exclusive(v___x_5505_);
if (v_isSharedCheck_5525_ == 0)
{
v___x_5520_ = v___x_5505_;
v_isShared_5521_ = v_isSharedCheck_5525_;
goto v_resetjp_5519_;
}
else
{
lean_inc(v_a_5518_);
lean_dec(v___x_5505_);
v___x_5520_ = lean_box(0);
v_isShared_5521_ = v_isSharedCheck_5525_;
goto v_resetjp_5519_;
}
v_resetjp_5519_:
{
lean_object* v___x_5523_; 
if (v_isShared_5521_ == 0)
{
v___x_5523_ = v___x_5520_;
goto v_reusejp_5522_;
}
else
{
lean_object* v_reuseFailAlloc_5524_; 
v_reuseFailAlloc_5524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5524_, 0, v_a_5518_);
v___x_5523_ = v_reuseFailAlloc_5524_;
goto v_reusejp_5522_;
}
v_reusejp_5522_:
{
return v___x_5523_;
}
}
}
}
else
{
lean_object* v___x_5526_; lean_object* v___x_5527_; 
lean_dec(v_next_5495_);
v___x_5526_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___x_5527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5527_, 0, v___x_5526_);
return v___x_5527_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg___boxed(lean_object* v_next_5528_, lean_object* v_rest_5529_, lean_object* v_a_5530_, lean_object* v_a_5531_, lean_object* v_a_5532_, lean_object* v_a_5533_, lean_object* v_a_5534_, lean_object* v_a_5535_){
_start:
{
lean_object* v_res_5536_; 
v_res_5536_ = l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg(v_next_5528_, v_rest_5529_, v_a_5530_, v_a_5531_, v_a_5532_, v_a_5533_, v_a_5534_);
lean_dec(v_a_5534_);
lean_dec_ref(v_a_5533_);
lean_dec(v_a_5532_);
lean_dec_ref(v_a_5531_);
lean_dec(v_a_5530_);
lean_dec(v_rest_5529_);
return v_res_5536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux(lean_object* v_00_u03b1_5537_, lean_object* v_next_5538_, lean_object* v_rest_5539_, lean_object* v_a_5540_, lean_object* v_a_5541_, lean_object* v_a_5542_, lean_object* v_a_5543_, lean_object* v_a_5544_){
_start:
{
lean_object* v___x_5546_; 
v___x_5546_ = l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg(v_next_5538_, v_rest_5539_, v_a_5540_, v_a_5541_, v_a_5542_, v_a_5543_, v_a_5544_);
return v___x_5546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux___boxed(lean_object* v_00_u03b1_5547_, lean_object* v_next_5548_, lean_object* v_rest_5549_, lean_object* v_a_5550_, lean_object* v_a_5551_, lean_object* v_a_5552_, lean_object* v_a_5553_, lean_object* v_a_5554_, lean_object* v_a_5555_){
_start:
{
lean_object* v_res_5556_; 
v_res_5556_ = l_Lean_Meta_LazyDiscrTree_extractKeyAux(v_00_u03b1_5547_, v_next_5548_, v_rest_5549_, v_a_5550_, v_a_5551_, v_a_5552_, v_a_5553_, v_a_5554_);
lean_dec(v_a_5554_);
lean_dec_ref(v_a_5553_);
lean_dec(v_a_5552_);
lean_dec_ref(v_a_5551_);
lean_dec(v_a_5550_);
lean_dec(v_rest_5549_);
return v_res_5556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey___redArg(lean_object* v_t_5557_, lean_object* v_path_5558_, lean_object* v_a_5559_, lean_object* v_a_5560_, lean_object* v_a_5561_, lean_object* v_a_5562_){
_start:
{
if (lean_obj_tag(v_path_5558_) == 0)
{
lean_object* v___x_5564_; lean_object* v___x_5565_; lean_object* v___x_5566_; 
v___x_5564_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___x_5565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5565_, 0, v___x_5564_);
lean_ctor_set(v___x_5565_, 1, v_t_5557_);
v___x_5566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5566_, 0, v___x_5565_);
return v___x_5566_;
}
else
{
lean_object* v_head_5567_; lean_object* v_tail_5568_; lean_object* v_roots_5569_; lean_object* v___x_5570_; lean_object* v_idx_5571_; lean_object* v___x_5572_; lean_object* v___x_5573_; 
v_head_5567_ = lean_ctor_get(v_path_5558_, 0);
lean_inc(v_head_5567_);
v_tail_5568_ = lean_ctor_get(v_path_5558_, 1);
lean_inc(v_tail_5568_);
lean_dec_ref_known(v_path_5558_, 2);
v_roots_5569_ = lean_ctor_get(v_t_5557_, 1);
v___x_5570_ = lean_unsigned_to_nat(0u);
v_idx_5571_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_roots_5569_, v_head_5567_, v___x_5570_);
lean_dec(v_head_5567_);
v___x_5572_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_extractKeyAux___boxed), 9, 3);
lean_closure_set(v___x_5572_, 0, lean_box(0));
lean_closure_set(v___x_5572_, 1, v_idx_5571_);
lean_closure_set(v___x_5572_, 2, v_tail_5568_);
v___x_5573_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_t_5557_, v___x_5572_, v_a_5559_, v_a_5560_, v_a_5561_, v_a_5562_);
return v___x_5573_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey___redArg___boxed(lean_object* v_t_5574_, lean_object* v_path_5575_, lean_object* v_a_5576_, lean_object* v_a_5577_, lean_object* v_a_5578_, lean_object* v_a_5579_, lean_object* v_a_5580_){
_start:
{
lean_object* v_res_5581_; 
v_res_5581_ = l_Lean_Meta_LazyDiscrTree_extractKey___redArg(v_t_5574_, v_path_5575_, v_a_5576_, v_a_5577_, v_a_5578_, v_a_5579_);
lean_dec(v_a_5579_);
lean_dec_ref(v_a_5578_);
lean_dec(v_a_5577_);
lean_dec_ref(v_a_5576_);
return v_res_5581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey(lean_object* v_00_u03b1_5582_, lean_object* v_t_5583_, lean_object* v_path_5584_, lean_object* v_a_5585_, lean_object* v_a_5586_, lean_object* v_a_5587_, lean_object* v_a_5588_){
_start:
{
lean_object* v___x_5590_; 
v___x_5590_ = l_Lean_Meta_LazyDiscrTree_extractKey___redArg(v_t_5583_, v_path_5584_, v_a_5585_, v_a_5586_, v_a_5587_, v_a_5588_);
return v___x_5590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey___boxed(lean_object* v_00_u03b1_5591_, lean_object* v_t_5592_, lean_object* v_path_5593_, lean_object* v_a_5594_, lean_object* v_a_5595_, lean_object* v_a_5596_, lean_object* v_a_5597_, lean_object* v_a_5598_){
_start:
{
lean_object* v_res_5599_; 
v_res_5599_ = l_Lean_Meta_LazyDiscrTree_extractKey(v_00_u03b1_5591_, v_t_5592_, v_path_5593_, v_a_5594_, v_a_5595_, v_a_5596_, v_a_5597_);
lean_dec(v_a_5597_);
lean_dec_ref(v_a_5596_);
lean_dec(v_a_5595_);
lean_dec_ref(v_a_5594_);
return v_res_5599_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(lean_object* v_as_x27_5600_, lean_object* v_b_5601_, lean_object* v___y_5602_, lean_object* v___y_5603_, lean_object* v___y_5604_, lean_object* v___y_5605_){
_start:
{
if (lean_obj_tag(v_as_x27_5600_) == 0)
{
lean_object* v___x_5607_; 
v___x_5607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5607_, 0, v_b_5601_);
return v___x_5607_;
}
else
{
lean_object* v_head_5608_; lean_object* v_tail_5609_; lean_object* v_fst_5610_; lean_object* v_snd_5611_; lean_object* v___x_5612_; 
v_head_5608_ = lean_ctor_get(v_as_x27_5600_, 0);
v_tail_5609_ = lean_ctor_get(v_as_x27_5600_, 1);
v_fst_5610_ = lean_ctor_get(v_b_5601_, 0);
lean_inc(v_fst_5610_);
v_snd_5611_ = lean_ctor_get(v_b_5601_, 1);
lean_inc(v_snd_5611_);
lean_dec_ref(v_b_5601_);
lean_inc(v_head_5608_);
v___x_5612_ = l_Lean_Meta_LazyDiscrTree_extractKey___redArg(v_snd_5611_, v_head_5608_, v___y_5602_, v___y_5603_, v___y_5604_, v___y_5605_);
if (lean_obj_tag(v___x_5612_) == 0)
{
lean_object* v_a_5613_; lean_object* v_fst_5614_; lean_object* v_snd_5615_; lean_object* v___x_5617_; uint8_t v_isShared_5618_; uint8_t v_isSharedCheck_5624_; 
v_a_5613_ = lean_ctor_get(v___x_5612_, 0);
lean_inc(v_a_5613_);
lean_dec_ref_known(v___x_5612_, 1);
v_fst_5614_ = lean_ctor_get(v_a_5613_, 0);
v_snd_5615_ = lean_ctor_get(v_a_5613_, 1);
v_isSharedCheck_5624_ = !lean_is_exclusive(v_a_5613_);
if (v_isSharedCheck_5624_ == 0)
{
v___x_5617_ = v_a_5613_;
v_isShared_5618_ = v_isSharedCheck_5624_;
goto v_resetjp_5616_;
}
else
{
lean_inc(v_snd_5615_);
lean_inc(v_fst_5614_);
lean_dec(v_a_5613_);
v___x_5617_ = lean_box(0);
v_isShared_5618_ = v_isSharedCheck_5624_;
goto v_resetjp_5616_;
}
v_resetjp_5616_:
{
lean_object* v___x_5619_; lean_object* v___x_5621_; 
v___x_5619_ = l_Array_append___redArg(v_fst_5610_, v_fst_5614_);
lean_dec(v_fst_5614_);
if (v_isShared_5618_ == 0)
{
lean_ctor_set(v___x_5617_, 0, v___x_5619_);
v___x_5621_ = v___x_5617_;
goto v_reusejp_5620_;
}
else
{
lean_object* v_reuseFailAlloc_5623_; 
v_reuseFailAlloc_5623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5623_, 0, v___x_5619_);
lean_ctor_set(v_reuseFailAlloc_5623_, 1, v_snd_5615_);
v___x_5621_ = v_reuseFailAlloc_5623_;
goto v_reusejp_5620_;
}
v_reusejp_5620_:
{
v_as_x27_5600_ = v_tail_5609_;
v_b_5601_ = v___x_5621_;
goto _start;
}
}
}
else
{
lean_dec(v_fst_5610_);
return v___x_5612_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg___boxed(lean_object* v_as_x27_5625_, lean_object* v_b_5626_, lean_object* v___y_5627_, lean_object* v___y_5628_, lean_object* v___y_5629_, lean_object* v___y_5630_, lean_object* v___y_5631_){
_start:
{
lean_object* v_res_5632_; 
v_res_5632_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(v_as_x27_5625_, v_b_5626_, v___y_5627_, v___y_5628_, v___y_5629_, v___y_5630_);
lean_dec(v___y_5630_);
lean_dec_ref(v___y_5629_);
lean_dec(v___y_5628_);
lean_dec_ref(v___y_5627_);
lean_dec(v_as_x27_5625_);
return v_res_5632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(lean_object* v_t_5633_, lean_object* v_keys_5634_, lean_object* v_a_5635_, lean_object* v_a_5636_, lean_object* v_a_5637_, lean_object* v_a_5638_){
_start:
{
lean_object* v_allExtracted_5640_; lean_object* v___x_5641_; lean_object* v___x_5642_; 
v_allExtracted_5640_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___x_5641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5641_, 0, v_allExtracted_5640_);
lean_ctor_set(v___x_5641_, 1, v_t_5633_);
v___x_5642_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(v_keys_5634_, v___x_5641_, v_a_5635_, v_a_5636_, v_a_5637_, v_a_5638_);
if (lean_obj_tag(v___x_5642_) == 0)
{
lean_object* v_a_5643_; lean_object* v___x_5645_; uint8_t v_isShared_5646_; uint8_t v_isSharedCheck_5659_; 
v_a_5643_ = lean_ctor_get(v___x_5642_, 0);
v_isSharedCheck_5659_ = !lean_is_exclusive(v___x_5642_);
if (v_isSharedCheck_5659_ == 0)
{
v___x_5645_ = v___x_5642_;
v_isShared_5646_ = v_isSharedCheck_5659_;
goto v_resetjp_5644_;
}
else
{
lean_inc(v_a_5643_);
lean_dec(v___x_5642_);
v___x_5645_ = lean_box(0);
v_isShared_5646_ = v_isSharedCheck_5659_;
goto v_resetjp_5644_;
}
v_resetjp_5644_:
{
lean_object* v_fst_5647_; lean_object* v_snd_5648_; lean_object* v___x_5650_; uint8_t v_isShared_5651_; uint8_t v_isSharedCheck_5658_; 
v_fst_5647_ = lean_ctor_get(v_a_5643_, 0);
v_snd_5648_ = lean_ctor_get(v_a_5643_, 1);
v_isSharedCheck_5658_ = !lean_is_exclusive(v_a_5643_);
if (v_isSharedCheck_5658_ == 0)
{
v___x_5650_ = v_a_5643_;
v_isShared_5651_ = v_isSharedCheck_5658_;
goto v_resetjp_5649_;
}
else
{
lean_inc(v_snd_5648_);
lean_inc(v_fst_5647_);
lean_dec(v_a_5643_);
v___x_5650_ = lean_box(0);
v_isShared_5651_ = v_isSharedCheck_5658_;
goto v_resetjp_5649_;
}
v_resetjp_5649_:
{
lean_object* v___x_5653_; 
if (v_isShared_5651_ == 0)
{
v___x_5653_ = v___x_5650_;
goto v_reusejp_5652_;
}
else
{
lean_object* v_reuseFailAlloc_5657_; 
v_reuseFailAlloc_5657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5657_, 0, v_fst_5647_);
lean_ctor_set(v_reuseFailAlloc_5657_, 1, v_snd_5648_);
v___x_5653_ = v_reuseFailAlloc_5657_;
goto v_reusejp_5652_;
}
v_reusejp_5652_:
{
lean_object* v___x_5655_; 
if (v_isShared_5646_ == 0)
{
lean_ctor_set(v___x_5645_, 0, v___x_5653_);
v___x_5655_ = v___x_5645_;
goto v_reusejp_5654_;
}
else
{
lean_object* v_reuseFailAlloc_5656_; 
v_reuseFailAlloc_5656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5656_, 0, v___x_5653_);
v___x_5655_ = v_reuseFailAlloc_5656_;
goto v_reusejp_5654_;
}
v_reusejp_5654_:
{
return v___x_5655_;
}
}
}
}
}
else
{
return v___x_5642_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys___redArg___boxed(lean_object* v_t_5660_, lean_object* v_keys_5661_, lean_object* v_a_5662_, lean_object* v_a_5663_, lean_object* v_a_5664_, lean_object* v_a_5665_, lean_object* v_a_5666_){
_start:
{
lean_object* v_res_5667_; 
v_res_5667_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_t_5660_, v_keys_5661_, v_a_5662_, v_a_5663_, v_a_5664_, v_a_5665_);
lean_dec(v_a_5665_);
lean_dec_ref(v_a_5664_);
lean_dec(v_a_5663_);
lean_dec_ref(v_a_5662_);
lean_dec(v_keys_5661_);
return v_res_5667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys(lean_object* v_00_u03b1_5668_, lean_object* v_t_5669_, lean_object* v_keys_5670_, lean_object* v_a_5671_, lean_object* v_a_5672_, lean_object* v_a_5673_, lean_object* v_a_5674_){
_start:
{
lean_object* v___x_5676_; 
v___x_5676_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_t_5669_, v_keys_5670_, v_a_5671_, v_a_5672_, v_a_5673_, v_a_5674_);
return v___x_5676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys___boxed(lean_object* v_00_u03b1_5677_, lean_object* v_t_5678_, lean_object* v_keys_5679_, lean_object* v_a_5680_, lean_object* v_a_5681_, lean_object* v_a_5682_, lean_object* v_a_5683_, lean_object* v_a_5684_){
_start:
{
lean_object* v_res_5685_; 
v_res_5685_ = l_Lean_Meta_LazyDiscrTree_extractKeys(v_00_u03b1_5677_, v_t_5678_, v_keys_5679_, v_a_5680_, v_a_5681_, v_a_5682_, v_a_5683_);
lean_dec(v_a_5683_);
lean_dec_ref(v_a_5682_);
lean_dec(v_a_5681_);
lean_dec_ref(v_a_5680_);
lean_dec(v_keys_5679_);
return v_res_5685_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0(lean_object* v_00_u03b1_5686_, lean_object* v_as_5687_, lean_object* v_as_x27_5688_, lean_object* v_b_5689_, lean_object* v_a_5690_, lean_object* v___y_5691_, lean_object* v___y_5692_, lean_object* v___y_5693_, lean_object* v___y_5694_){
_start:
{
lean_object* v___x_5696_; 
v___x_5696_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(v_as_x27_5688_, v_b_5689_, v___y_5691_, v___y_5692_, v___y_5693_, v___y_5694_);
return v___x_5696_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___boxed(lean_object* v_00_u03b1_5697_, lean_object* v_as_5698_, lean_object* v_as_x27_5699_, lean_object* v_b_5700_, lean_object* v_a_5701_, lean_object* v___y_5702_, lean_object* v___y_5703_, lean_object* v___y_5704_, lean_object* v___y_5705_, lean_object* v___y_5706_){
_start:
{
lean_object* v_res_5707_; 
v_res_5707_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0(v_00_u03b1_5697_, v_as_5698_, v_as_x27_5699_, v_b_5700_, v_a_5701_, v___y_5702_, v___y_5703_, v___y_5704_, v___y_5705_);
lean_dec(v___y_5705_);
lean_dec_ref(v___y_5704_);
lean_dec(v___y_5703_);
lean_dec_ref(v___y_5702_);
lean_dec(v_as_x27_5699_);
lean_dec(v_as_5698_);
return v_res_5707_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1(void){
_start:
{
lean_object* v___x_5709_; lean_object* v___x_5710_; 
v___x_5709_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__0));
v___x_5710_ = l_Lean_stringToMessageData(v___x_5709_);
return v___x_5710_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3(void){
_start:
{
lean_object* v___x_5712_; lean_object* v___x_5713_; 
v___x_5712_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__2));
v___x_5713_ = l_Lean_stringToMessageData(v___x_5712_);
return v___x_5713_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5(void){
_start:
{
lean_object* v___x_5715_; lean_object* v___x_5716_; 
v___x_5715_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__4));
v___x_5716_ = l_Lean_stringToMessageData(v___x_5715_);
return v___x_5716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg(lean_object* v_inst_5717_, lean_object* v_inst_5718_, lean_object* v_inst_5719_, lean_object* v_inst_5720_, lean_object* v_f_5721_){
_start:
{
lean_object* v_module_5722_; lean_object* v_const_5723_; lean_object* v_exception_5724_; lean_object* v___x_5725_; lean_object* v___x_5726_; lean_object* v___x_5727_; lean_object* v___x_5728_; lean_object* v___x_5729_; lean_object* v___x_5730_; lean_object* v___x_5731_; lean_object* v___x_5732_; lean_object* v___x_5733_; lean_object* v___x_5734_; lean_object* v___x_5735_; lean_object* v___x_5736_; 
v_module_5722_ = lean_ctor_get(v_f_5721_, 0);
lean_inc(v_module_5722_);
v_const_5723_ = lean_ctor_get(v_f_5721_, 1);
lean_inc(v_const_5723_);
v_exception_5724_ = lean_ctor_get(v_f_5721_, 2);
lean_inc_ref(v_exception_5724_);
lean_dec_ref(v_f_5721_);
v___x_5725_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1);
v___x_5726_ = l_Lean_MessageData_ofName(v_const_5723_);
v___x_5727_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5727_, 0, v___x_5725_);
lean_ctor_set(v___x_5727_, 1, v___x_5726_);
v___x_5728_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3);
v___x_5729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5729_, 0, v___x_5727_);
lean_ctor_set(v___x_5729_, 1, v___x_5728_);
v___x_5730_ = l_Lean_MessageData_ofName(v_module_5722_);
v___x_5731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5731_, 0, v___x_5729_);
lean_ctor_set(v___x_5731_, 1, v___x_5730_);
v___x_5732_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5);
v___x_5733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5733_, 0, v___x_5731_);
lean_ctor_set(v___x_5733_, 1, v___x_5732_);
v___x_5734_ = l_Lean_Exception_toMessageData(v_exception_5724_);
v___x_5735_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5735_, 0, v___x_5733_);
lean_ctor_set(v___x_5735_, 1, v___x_5734_);
v___x_5736_ = l_Lean_logError___redArg(v_inst_5717_, v_inst_5718_, v_inst_5719_, v_inst_5720_, v___x_5735_);
return v___x_5736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure(lean_object* v_m_5737_, lean_object* v_inst_5738_, lean_object* v_inst_5739_, lean_object* v_inst_5740_, lean_object* v_inst_5741_, lean_object* v_f_5742_){
_start:
{
lean_object* v___x_5743_; 
v___x_5743_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg(v_inst_5738_, v_inst_5739_, v_inst_5740_, v_inst_5741_, v_f_5742_);
return v___x_5743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__0(lean_object* v_tasks_5744_, lean_object* v_toPure_5745_, lean_object* v_t_5746_){
_start:
{
lean_object* v___x_5747_; lean_object* v___x_5748_; 
v___x_5747_ = lean_array_push(v_tasks_5744_, v_t_5746_);
v___x_5748_ = lean_apply_2(v_toPure_5745_, lean_box(0), v___x_5747_);
return v___x_5748_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(lean_object* v_inst_5749_, lean_object* v_inst_5750_, lean_object* v_cctx_5751_, lean_object* v_env_5752_, lean_object* v_act_5753_, lean_object* v_constantsPerTask_5754_, lean_object* v_n_5755_, lean_object* v_ngen_5756_, lean_object* v_tasks_5757_, lean_object* v_start_5758_, lean_object* v_cnt_5759_, lean_object* v_idx_5760_){
_start:
{
lean_object* v___x_5761_; lean_object* v_toApplicative_5762_; lean_object* v_moduleData_5763_; lean_object* v_toBind_5764_; lean_object* v_toPure_5765_; lean_object* v___x_5766_; uint8_t v___x_5767_; 
v___x_5761_ = l_Lean_Environment_header(v_env_5752_);
v_toApplicative_5762_ = lean_ctor_get(v_inst_5749_, 0);
v_moduleData_5763_ = lean_ctor_get(v___x_5761_, 7);
lean_inc_ref(v_moduleData_5763_);
lean_dec_ref(v___x_5761_);
v_toBind_5764_ = lean_ctor_get(v_inst_5749_, 1);
v_toPure_5765_ = lean_ctor_get(v_toApplicative_5762_, 1);
v___x_5766_ = lean_array_get_size(v_moduleData_5763_);
v___x_5767_ = lean_nat_dec_lt(v_idx_5760_, v___x_5766_);
if (v___x_5767_ == 0)
{
uint8_t v___x_5768_; 
lean_inc(v_toPure_5765_);
lean_inc(v_toBind_5764_);
lean_dec_ref(v_moduleData_5763_);
lean_dec(v_idx_5760_);
lean_dec(v_cnt_5759_);
lean_dec(v_constantsPerTask_5754_);
lean_dec_ref(v_inst_5749_);
v___x_5768_ = lean_nat_dec_lt(v_start_5758_, v_n_5755_);
if (v___x_5768_ == 0)
{
lean_object* v___x_5769_; 
lean_dec(v_toBind_5764_);
lean_dec(v_start_5758_);
lean_dec_ref(v_ngen_5756_);
lean_dec(v_n_5755_);
lean_dec_ref(v_act_5753_);
lean_dec_ref(v_env_5752_);
lean_dec_ref(v_cctx_5751_);
lean_dec(v_inst_5750_);
v___x_5769_ = lean_apply_2(v_toPure_5765_, lean_box(0), v_tasks_5757_);
return v___x_5769_;
}
else
{
lean_object* v_namePrefix_5770_; lean_object* v_idx_5771_; lean_object* v___x_5773_; uint8_t v_isShared_5774_; uint8_t v_isSharedCheck_5786_; 
v_namePrefix_5770_ = lean_ctor_get(v_ngen_5756_, 0);
v_idx_5771_ = lean_ctor_get(v_ngen_5756_, 1);
v_isSharedCheck_5786_ = !lean_is_exclusive(v_ngen_5756_);
if (v_isSharedCheck_5786_ == 0)
{
v___x_5773_ = v_ngen_5756_;
v_isShared_5774_ = v_isSharedCheck_5786_;
goto v_resetjp_5772_;
}
else
{
lean_inc(v_idx_5771_);
lean_inc(v_namePrefix_5770_);
lean_dec(v_ngen_5756_);
v___x_5773_ = lean_box(0);
v_isShared_5774_ = v_isSharedCheck_5786_;
goto v_resetjp_5772_;
}
v_resetjp_5772_:
{
lean_object* v___f_5775_; lean_object* v___x_5776_; lean_object* v___x_5777_; lean_object* v___x_5779_; 
v___f_5775_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5775_, 0, v_tasks_5757_);
lean_closure_set(v___f_5775_, 1, v_toPure_5765_);
v___x_5776_ = l_Lean_Name_num___override(v_namePrefix_5770_, v_idx_5771_);
v___x_5777_ = lean_unsigned_to_nat(1u);
if (v_isShared_5774_ == 0)
{
lean_ctor_set(v___x_5773_, 1, v___x_5777_);
lean_ctor_set(v___x_5773_, 0, v___x_5776_);
v___x_5779_ = v___x_5773_;
goto v_reusejp_5778_;
}
else
{
lean_object* v_reuseFailAlloc_5785_; 
v_reuseFailAlloc_5785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5785_, 0, v___x_5776_);
lean_ctor_set(v_reuseFailAlloc_5785_, 1, v___x_5777_);
v___x_5779_ = v_reuseFailAlloc_5785_;
goto v_reusejp_5778_;
}
v_reusejp_5778_:
{
lean_object* v___x_5780_; lean_object* v___x_5781_; lean_object* v___x_5782_; lean_object* v___x_5783_; lean_object* v___x_5784_; 
v___x_5780_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_5780_, 0, lean_box(0));
lean_closure_set(v___x_5780_, 1, v_cctx_5751_);
lean_closure_set(v___x_5780_, 2, v___x_5779_);
lean_closure_set(v___x_5780_, 3, v_env_5752_);
lean_closure_set(v___x_5780_, 4, v_act_5753_);
lean_closure_set(v___x_5780_, 5, v_start_5758_);
lean_closure_set(v___x_5780_, 6, v_n_5755_);
v___x_5781_ = lean_unsigned_to_nat(0u);
v___x_5782_ = lean_alloc_closure((void*)(l_BaseIO_asTask___boxed), 4, 3);
lean_closure_set(v___x_5782_, 0, lean_box(0));
lean_closure_set(v___x_5782_, 1, v___x_5780_);
lean_closure_set(v___x_5782_, 2, v___x_5781_);
v___x_5783_ = lean_apply_2(v_inst_5750_, lean_box(0), v___x_5782_);
v___x_5784_ = lean_apply_4(v_toBind_5764_, lean_box(0), lean_box(0), v___x_5783_, v___f_5775_);
return v___x_5784_;
}
}
}
}
else
{
lean_object* v_mdata_5787_; lean_object* v_constants_5788_; lean_object* v___x_5789_; lean_object* v_cnt_5790_; uint8_t v___x_5791_; 
v_mdata_5787_ = lean_array_fget(v_moduleData_5763_, v_idx_5760_);
lean_dec_ref(v_moduleData_5763_);
v_constants_5788_ = lean_ctor_get(v_mdata_5787_, 2);
lean_inc_ref(v_constants_5788_);
lean_dec(v_mdata_5787_);
v___x_5789_ = lean_array_get_size(v_constants_5788_);
lean_dec_ref(v_constants_5788_);
v_cnt_5790_ = lean_nat_add(v_cnt_5759_, v___x_5789_);
lean_dec(v_cnt_5759_);
v___x_5791_ = lean_nat_dec_lt(v_constantsPerTask_5754_, v_cnt_5790_);
if (v___x_5791_ == 0)
{
lean_object* v___x_5792_; lean_object* v___x_5793_; 
v___x_5792_ = lean_unsigned_to_nat(1u);
v___x_5793_ = lean_nat_add(v_idx_5760_, v___x_5792_);
lean_dec(v_idx_5760_);
v_cnt_5759_ = v_cnt_5790_;
v_idx_5760_ = v___x_5793_;
goto _start;
}
else
{
lean_object* v_namePrefix_5795_; lean_object* v_idx_5796_; lean_object* v___x_5798_; uint8_t v_isShared_5799_; uint8_t v_isSharedCheck_5814_; 
lean_inc(v_toBind_5764_);
lean_dec(v_cnt_5790_);
v_namePrefix_5795_ = lean_ctor_get(v_ngen_5756_, 0);
v_idx_5796_ = lean_ctor_get(v_ngen_5756_, 1);
v_isSharedCheck_5814_ = !lean_is_exclusive(v_ngen_5756_);
if (v_isSharedCheck_5814_ == 0)
{
v___x_5798_ = v_ngen_5756_;
v_isShared_5799_ = v_isSharedCheck_5814_;
goto v_resetjp_5797_;
}
else
{
lean_inc(v_idx_5796_);
lean_inc(v_namePrefix_5795_);
lean_dec(v_ngen_5756_);
v___x_5798_ = lean_box(0);
v_isShared_5799_ = v_isSharedCheck_5814_;
goto v_resetjp_5797_;
}
v_resetjp_5797_:
{
lean_object* v___x_5800_; lean_object* v___x_5801_; lean_object* v___x_5803_; 
lean_inc(v_idx_5796_);
lean_inc(v_namePrefix_5795_);
v___x_5800_ = l_Lean_Name_num___override(v_namePrefix_5795_, v_idx_5796_);
v___x_5801_ = lean_unsigned_to_nat(1u);
if (v_isShared_5799_ == 0)
{
lean_ctor_set(v___x_5798_, 1, v___x_5801_);
lean_ctor_set(v___x_5798_, 0, v___x_5800_);
v___x_5803_ = v___x_5798_;
goto v_reusejp_5802_;
}
else
{
lean_object* v_reuseFailAlloc_5813_; 
v_reuseFailAlloc_5813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5813_, 0, v___x_5800_);
lean_ctor_set(v_reuseFailAlloc_5813_, 1, v___x_5801_);
v___x_5803_ = v_reuseFailAlloc_5813_;
goto v_reusejp_5802_;
}
v_reusejp_5802_:
{
lean_object* v___x_5804_; lean_object* v___x_5805_; lean_object* v___x_5806_; lean_object* v___f_5807_; lean_object* v___x_5808_; lean_object* v___x_5809_; lean_object* v___x_5810_; lean_object* v___x_5811_; lean_object* v___x_5812_; 
v___x_5804_ = lean_nat_add(v_idx_5796_, v___x_5801_);
lean_dec(v_idx_5796_);
v___x_5805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5805_, 0, v_namePrefix_5795_);
lean_ctor_set(v___x_5805_, 1, v___x_5804_);
v___x_5806_ = lean_nat_add(v_idx_5760_, v___x_5801_);
lean_dec(v_idx_5760_);
lean_inc(v___x_5806_);
lean_inc_ref(v_act_5753_);
lean_inc_ref(v_env_5752_);
lean_inc_ref(v_cctx_5751_);
lean_inc(v_inst_5750_);
v___f_5807_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__1), 11, 10);
lean_closure_set(v___f_5807_, 0, v_tasks_5757_);
lean_closure_set(v___f_5807_, 1, v_inst_5749_);
lean_closure_set(v___f_5807_, 2, v_inst_5750_);
lean_closure_set(v___f_5807_, 3, v_cctx_5751_);
lean_closure_set(v___f_5807_, 4, v_env_5752_);
lean_closure_set(v___f_5807_, 5, v_act_5753_);
lean_closure_set(v___f_5807_, 6, v_constantsPerTask_5754_);
lean_closure_set(v___f_5807_, 7, v_n_5755_);
lean_closure_set(v___f_5807_, 8, v___x_5805_);
lean_closure_set(v___f_5807_, 9, v___x_5806_);
v___x_5808_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_5808_, 0, lean_box(0));
lean_closure_set(v___x_5808_, 1, v_cctx_5751_);
lean_closure_set(v___x_5808_, 2, v___x_5803_);
lean_closure_set(v___x_5808_, 3, v_env_5752_);
lean_closure_set(v___x_5808_, 4, v_act_5753_);
lean_closure_set(v___x_5808_, 5, v_start_5758_);
lean_closure_set(v___x_5808_, 6, v___x_5806_);
v___x_5809_ = lean_unsigned_to_nat(0u);
v___x_5810_ = lean_alloc_closure((void*)(l_BaseIO_asTask___boxed), 4, 3);
lean_closure_set(v___x_5810_, 0, lean_box(0));
lean_closure_set(v___x_5810_, 1, v___x_5808_);
lean_closure_set(v___x_5810_, 2, v___x_5809_);
v___x_5811_ = lean_apply_2(v_inst_5750_, lean_box(0), v___x_5810_);
v___x_5812_ = lean_apply_4(v_toBind_5764_, lean_box(0), lean_box(0), v___x_5811_, v___f_5807_);
return v___x_5812_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__1(lean_object* v_tasks_5815_, lean_object* v_inst_5816_, lean_object* v_inst_5817_, lean_object* v_cctx_5818_, lean_object* v_env_5819_, lean_object* v_act_5820_, lean_object* v_constantsPerTask_5821_, lean_object* v_n_5822_, lean_object* v___x_5823_, lean_object* v___x_5824_, lean_object* v_t_5825_){
_start:
{
lean_object* v___x_5826_; lean_object* v___x_5827_; lean_object* v___x_5828_; 
v___x_5826_ = lean_array_push(v_tasks_5815_, v_t_5825_);
v___x_5827_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_5824_);
v___x_5828_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(v_inst_5816_, v_inst_5817_, v_cctx_5818_, v_env_5819_, v_act_5820_, v_constantsPerTask_5821_, v_n_5822_, v___x_5823_, v___x_5826_, v___x_5824_, v___x_5827_, v___x_5824_);
return v___x_5828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go(lean_object* v_m_5829_, lean_object* v_00_u03b1_5830_, lean_object* v_inst_5831_, lean_object* v_inst_5832_, lean_object* v_cctx_5833_, lean_object* v_env_5834_, lean_object* v_act_5835_, lean_object* v_constantsPerTask_5836_, lean_object* v_n_5837_, lean_object* v_ngen_5838_, lean_object* v_tasks_5839_, lean_object* v_start_5840_, lean_object* v_cnt_5841_, lean_object* v_idx_5842_){
_start:
{
lean_object* v___x_5843_; 
v___x_5843_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(v_inst_5831_, v_inst_5832_, v_cctx_5833_, v_env_5834_, v_act_5835_, v_constantsPerTask_5836_, v_n_5837_, v_ngen_5838_, v_tasks_5839_, v_start_5840_, v_cnt_5841_, v_idx_5842_);
return v___x_5843_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_getChildNgen_match__1_splitter___redArg(lean_object* v_x_5844_, lean_object* v_h__1_5845_){
_start:
{
lean_object* v_fst_5846_; lean_object* v_snd_5847_; lean_object* v___x_5848_; 
v_fst_5846_ = lean_ctor_get(v_x_5844_, 0);
lean_inc(v_fst_5846_);
v_snd_5847_ = lean_ctor_get(v_x_5844_, 1);
lean_inc(v_snd_5847_);
lean_dec_ref(v_x_5844_);
v___x_5848_ = lean_apply_2(v_h__1_5845_, v_fst_5846_, v_snd_5847_);
return v___x_5848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_getChildNgen_match__1_splitter(lean_object* v_motive_5849_, lean_object* v_x_5850_, lean_object* v_h__1_5851_){
_start:
{
lean_object* v_fst_5852_; lean_object* v_snd_5853_; lean_object* v___x_5854_; 
v_fst_5852_ = lean_ctor_get(v_x_5850_, 0);
lean_inc(v_fst_5852_);
v_snd_5853_ = lean_ctor_get(v_x_5850_, 1);
lean_inc(v_snd_5853_);
lean_dec_ref(v_x_5850_);
v___x_5854_ = lean_apply_2(v_h__1_5851_, v_fst_5852_, v_snd_5853_);
return v___x_5854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__0(lean_object* v_inst_5855_, lean_object* v_inst_5856_, lean_object* v_inst_5857_, lean_object* v_inst_5858_, lean_object* v_x_5859_, lean_object* v___y_5860_){
_start:
{
lean_object* v___x_5861_; 
v___x_5861_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg(v_inst_5855_, v_inst_5856_, v_inst_5857_, v_inst_5858_, v___y_5860_);
return v___x_5861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__1(lean_object* v_tree_5862_, lean_object* v_toPure_5863_, lean_object* v_____r_5864_){
_start:
{
lean_object* v___x_5865_; lean_object* v___x_5866_; 
v___x_5865_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_tree_5862_);
v___x_5866_ = lean_apply_2(v_toPure_5863_, lean_box(0), v___x_5865_);
return v___x_5866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__2(lean_object* v___x_5867_, lean_object* v___x_5868_, lean_object* v_toPure_5869_, lean_object* v_toBind_5870_, lean_object* v_inst_5871_, lean_object* v___f_5872_, lean_object* v_tasks_5873_){
_start:
{
lean_object* v___x_5874_; lean_object* v___x_5875_; lean_object* v___x_5876_; lean_object* v___x_5877_; lean_object* v___x_5878_; lean_object* v_r_5879_; lean_object* v_tree_5880_; lean_object* v_errors_5881_; lean_object* v___f_5882_; lean_object* v___x_5883_; lean_object* v___x_5884_; uint8_t v___x_5885_; 
v___x_5874_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__1);
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
v_tree_5880_ = lean_ctor_get(v_r_5879_, 0);
lean_inc_ref(v_tree_5880_);
v_errors_5881_ = lean_ctor_get(v_r_5879_, 1);
lean_inc_ref(v_errors_5881_);
lean_dec(v_r_5879_);
lean_inc(v_toPure_5869_);
v___f_5882_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__1), 3, 2);
lean_closure_set(v___f_5882_, 0, v_tree_5880_);
lean_closure_set(v___f_5882_, 1, v_toPure_5869_);
v___x_5883_ = lean_array_get_size(v_errors_5881_);
v___x_5884_ = lean_box(0);
v___x_5885_ = lean_nat_dec_lt(v___x_5867_, v___x_5883_);
lean_dec(v___x_5867_);
if (v___x_5885_ == 0)
{
lean_object* v___x_5886_; lean_object* v___x_5887_; 
lean_dec_ref(v_errors_5881_);
lean_dec(v___f_5872_);
lean_dec_ref(v_inst_5871_);
v___x_5886_ = lean_apply_2(v_toPure_5869_, lean_box(0), v___x_5884_);
v___x_5887_ = lean_apply_4(v_toBind_5870_, lean_box(0), lean_box(0), v___x_5886_, v___f_5882_);
return v___x_5887_;
}
else
{
size_t v___x_5888_; size_t v___x_5889_; lean_object* v___x_5890_; lean_object* v___x_5891_; 
lean_dec(v_toPure_5869_);
v___x_5888_ = ((size_t)0ULL);
v___x_5889_ = lean_usize_of_nat(v___x_5883_);
v___x_5890_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_5871_, v___f_5872_, v_errors_5881_, v___x_5888_, v___x_5889_, v___x_5884_);
v___x_5891_ = lean_apply_4(v_toBind_5870_, lean_box(0), lean_box(0), v___x_5890_, v___f_5882_);
return v___x_5891_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg(lean_object* v_inst_5894_, lean_object* v_inst_5895_, lean_object* v_inst_5896_, lean_object* v_inst_5897_, lean_object* v_inst_5898_, lean_object* v_cctx_5899_, lean_object* v_ngen_5900_, lean_object* v_env_5901_, lean_object* v_act_5902_, lean_object* v_constantsPerTask_5903_){
_start:
{
lean_object* v___x_5904_; lean_object* v_moduleData_5905_; lean_object* v_toApplicative_5906_; lean_object* v_toBind_5907_; lean_object* v_n_5908_; lean_object* v___x_5909_; lean_object* v___x_5910_; lean_object* v___x_5911_; lean_object* v_toPure_5912_; lean_object* v___f_5913_; lean_object* v___x_5914_; lean_object* v___f_5915_; lean_object* v___x_5916_; 
v___x_5904_ = l_Lean_Environment_header(v_env_5901_);
v_moduleData_5905_ = lean_ctor_get(v___x_5904_, 7);
lean_inc_ref(v_moduleData_5905_);
lean_dec_ref(v___x_5904_);
v_toApplicative_5906_ = lean_ctor_get(v_inst_5894_, 0);
v_toBind_5907_ = lean_ctor_get(v_inst_5894_, 1);
lean_inc_n(v_toBind_5907_, 2);
v_n_5908_ = lean_array_get_size(v_moduleData_5905_);
lean_dec_ref(v_moduleData_5905_);
v___x_5909_ = lean_unsigned_to_nat(0u);
v___x_5910_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
lean_inc_ref_n(v_inst_5894_, 2);
v___x_5911_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(v_inst_5894_, v_inst_5898_, v_cctx_5899_, v_env_5901_, v_act_5902_, v_constantsPerTask_5903_, v_n_5908_, v_ngen_5900_, v___x_5910_, v___x_5909_, v___x_5909_, v___x_5909_);
v_toPure_5912_ = lean_ctor_get(v_toApplicative_5906_, 1);
lean_inc(v_toPure_5912_);
v___f_5913_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__0), 6, 4);
lean_closure_set(v___f_5913_, 0, v_inst_5894_);
lean_closure_set(v___f_5913_, 1, v_inst_5895_);
lean_closure_set(v___f_5913_, 2, v_inst_5896_);
lean_closure_set(v___f_5913_, 3, v_inst_5897_);
v___x_5914_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___redArg___closed__0));
v___f_5915_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__2), 7, 6);
lean_closure_set(v___f_5915_, 0, v___x_5909_);
lean_closure_set(v___f_5915_, 1, v___x_5914_);
lean_closure_set(v___f_5915_, 2, v_toPure_5912_);
lean_closure_set(v___f_5915_, 3, v_toBind_5907_);
lean_closure_set(v___f_5915_, 4, v_inst_5894_);
lean_closure_set(v___f_5915_, 5, v___f_5913_);
v___x_5916_ = lean_apply_4(v_toBind_5907_, lean_box(0), lean_box(0), v___x_5911_, v___f_5915_);
return v___x_5916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree(lean_object* v_m_5917_, lean_object* v_00_u03b1_5918_, lean_object* v_inst_5919_, lean_object* v_inst_5920_, lean_object* v_inst_5921_, lean_object* v_inst_5922_, lean_object* v_inst_5923_, lean_object* v_cctx_5924_, lean_object* v_ngen_5925_, lean_object* v_env_5926_, lean_object* v_act_5927_, lean_object* v_constantsPerTask_5928_){
_start:
{
lean_object* v___x_5929_; 
v___x_5929_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg(v_inst_5919_, v_inst_5920_, v_inst_5921_, v_inst_5922_, v_inst_5923_, v_cctx_5924_, v_ngen_5925_, v_env_5926_, v_act_5927_, v_constantsPerTask_5928_);
return v___x_5929_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0(void){
_start:
{
lean_object* v___x_5930_; lean_object* v___x_5931_; lean_object* v___x_5932_; 
v___x_5930_ = lean_box(0);
v___x_5931_ = lean_unsigned_to_nat(16u);
v___x_5932_ = lean_mk_array(v___x_5931_, v___x_5930_);
return v___x_5932_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1(void){
_start:
{
lean_object* v___x_5933_; lean_object* v___x_5934_; lean_object* v___x_5935_; 
v___x_5933_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0, &l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0);
v___x_5934_ = lean_unsigned_to_nat(0u);
v___x_5935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5935_, 0, v___x_5934_);
lean_ctor_set(v___x_5935_, 1, v___x_5933_);
return v___x_5935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createTreeCtx(lean_object* v_ctx_5936_){
_start:
{
lean_object* v_toCold_5937_; lean_object* v_ref_5938_; lean_object* v___x_5940_; uint8_t v_isShared_5941_; uint8_t v_isSharedCheck_5973_; 
v_toCold_5937_ = lean_ctor_get(v_ctx_5936_, 0);
v_ref_5938_ = lean_ctor_get(v_ctx_5936_, 2);
v_isSharedCheck_5973_ = !lean_is_exclusive(v_ctx_5936_);
if (v_isSharedCheck_5973_ == 0)
{
lean_object* v_unused_5974_; 
v_unused_5974_ = lean_ctor_get(v_ctx_5936_, 1);
lean_dec(v_unused_5974_);
v___x_5940_ = v_ctx_5936_;
v_isShared_5941_ = v_isSharedCheck_5973_;
goto v_resetjp_5939_;
}
else
{
lean_inc(v_ref_5938_);
lean_inc(v_toCold_5937_);
lean_dec(v_ctx_5936_);
v___x_5940_ = lean_box(0);
v_isShared_5941_ = v_isSharedCheck_5973_;
goto v_resetjp_5939_;
}
v_resetjp_5939_:
{
lean_object* v_fileName_5942_; lean_object* v_fileMap_5943_; lean_object* v_options_5944_; lean_object* v_maxRecDepth_5945_; lean_object* v___x_5947_; uint8_t v_isShared_5948_; uint8_t v_isSharedCheck_5964_; 
v_fileName_5942_ = lean_ctor_get(v_toCold_5937_, 0);
v_fileMap_5943_ = lean_ctor_get(v_toCold_5937_, 1);
v_options_5944_ = lean_ctor_get(v_toCold_5937_, 2);
v_maxRecDepth_5945_ = lean_ctor_get(v_toCold_5937_, 3);
v_isSharedCheck_5964_ = !lean_is_exclusive(v_toCold_5937_);
if (v_isSharedCheck_5964_ == 0)
{
lean_object* v_unused_5965_; lean_object* v_unused_5966_; lean_object* v_unused_5967_; lean_object* v_unused_5968_; lean_object* v_unused_5969_; lean_object* v_unused_5970_; lean_object* v_unused_5971_; lean_object* v_unused_5972_; 
v_unused_5965_ = lean_ctor_get(v_toCold_5937_, 11);
lean_dec(v_unused_5965_);
v_unused_5966_ = lean_ctor_get(v_toCold_5937_, 10);
lean_dec(v_unused_5966_);
v_unused_5967_ = lean_ctor_get(v_toCold_5937_, 9);
lean_dec(v_unused_5967_);
v_unused_5968_ = lean_ctor_get(v_toCold_5937_, 8);
lean_dec(v_unused_5968_);
v_unused_5969_ = lean_ctor_get(v_toCold_5937_, 7);
lean_dec(v_unused_5969_);
v_unused_5970_ = lean_ctor_get(v_toCold_5937_, 6);
lean_dec(v_unused_5970_);
v_unused_5971_ = lean_ctor_get(v_toCold_5937_, 5);
lean_dec(v_unused_5971_);
v_unused_5972_ = lean_ctor_get(v_toCold_5937_, 4);
lean_dec(v_unused_5972_);
v___x_5947_ = v_toCold_5937_;
v_isShared_5948_ = v_isSharedCheck_5964_;
goto v_resetjp_5946_;
}
else
{
lean_inc(v_maxRecDepth_5945_);
lean_inc(v_options_5944_);
lean_inc(v_fileMap_5943_);
lean_inc(v_fileName_5942_);
lean_dec(v_toCold_5937_);
v___x_5947_ = lean_box(0);
v_isShared_5948_ = v_isSharedCheck_5964_;
goto v_resetjp_5946_;
}
v_resetjp_5946_:
{
lean_object* v___x_5949_; lean_object* v___x_5950_; lean_object* v___x_5951_; lean_object* v___x_5952_; lean_object* v___x_5953_; lean_object* v___x_5954_; lean_object* v___x_5956_; 
v___x_5949_ = lean_box(0);
v___x_5950_ = lean_box(0);
v___x_5951_ = lean_unsigned_to_nat(0u);
v___x_5952_ = l_Lean_firstFrontendMacroScope;
v___x_5953_ = lean_box(0);
v___x_5954_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1, &l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1);
lean_inc_ref(v_options_5944_);
if (v_isShared_5948_ == 0)
{
lean_ctor_set(v___x_5947_, 11, v___x_5954_);
lean_ctor_set(v___x_5947_, 10, v___x_5953_);
lean_ctor_set(v___x_5947_, 9, v___x_5952_);
lean_ctor_set(v___x_5947_, 8, v___x_5949_);
lean_ctor_set(v___x_5947_, 7, v___x_5951_);
lean_ctor_set(v___x_5947_, 6, v___x_5951_);
lean_ctor_set(v___x_5947_, 5, v___x_5950_);
lean_ctor_set(v___x_5947_, 4, v___x_5949_);
v___x_5956_ = v___x_5947_;
goto v_reusejp_5955_;
}
else
{
lean_object* v_reuseFailAlloc_5963_; 
v_reuseFailAlloc_5963_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_5963_, 0, v_fileName_5942_);
lean_ctor_set(v_reuseFailAlloc_5963_, 1, v_fileMap_5943_);
lean_ctor_set(v_reuseFailAlloc_5963_, 2, v_options_5944_);
lean_ctor_set(v_reuseFailAlloc_5963_, 3, v_maxRecDepth_5945_);
lean_ctor_set(v_reuseFailAlloc_5963_, 4, v___x_5949_);
lean_ctor_set(v_reuseFailAlloc_5963_, 5, v___x_5950_);
lean_ctor_set(v_reuseFailAlloc_5963_, 6, v___x_5951_);
lean_ctor_set(v_reuseFailAlloc_5963_, 7, v___x_5951_);
lean_ctor_set(v_reuseFailAlloc_5963_, 8, v___x_5949_);
lean_ctor_set(v_reuseFailAlloc_5963_, 9, v___x_5952_);
lean_ctor_set(v_reuseFailAlloc_5963_, 10, v___x_5953_);
lean_ctor_set(v_reuseFailAlloc_5963_, 11, v___x_5954_);
v___x_5956_ = v_reuseFailAlloc_5963_;
goto v_reusejp_5955_;
}
v_reusejp_5955_:
{
uint16_t v___x_5957_; uint8_t v___x_5958_; uint8_t v___x_5959_; lean_object* v___x_5961_; 
v___x_5957_ = l_Lean_OptionFlags_ofOptions(v_options_5944_);
lean_dec_ref(v_options_5944_);
v___x_5958_ = 0;
v___x_5959_ = 0;
if (v_isShared_5941_ == 0)
{
lean_ctor_set(v___x_5940_, 1, v___x_5951_);
lean_ctor_set(v___x_5940_, 0, v___x_5956_);
v___x_5961_ = v___x_5940_;
goto v_reusejp_5960_;
}
else
{
lean_object* v_reuseFailAlloc_5962_; 
v_reuseFailAlloc_5962_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_5962_, 0, v___x_5956_);
lean_ctor_set(v_reuseFailAlloc_5962_, 1, v___x_5951_);
lean_ctor_set(v_reuseFailAlloc_5962_, 2, v_ref_5938_);
v___x_5961_ = v_reuseFailAlloc_5962_;
goto v_reusejp_5960_;
}
v_reusejp_5960_:
{
lean_ctor_set_uint16(v___x_5961_, sizeof(void*)*3, v___x_5957_);
lean_ctor_set_uint8(v___x_5961_, sizeof(void*)*3 + 2, v___x_5958_);
lean_ctor_set_uint8(v___x_5961_, sizeof(void*)*3 + 3, v___x_5959_);
lean_ctor_set_uint8(v___x_5961_, sizeof(void*)*3 + 4, v___x_5958_);
return v___x_5961_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(lean_object* v_category_5975_, lean_object* v_opts_5976_, lean_object* v_act_5977_, lean_object* v_decl_5978_, lean_object* v___y_5979_, lean_object* v___y_5980_, lean_object* v___y_5981_, lean_object* v___y_5982_){
_start:
{
lean_object* v___x_5984_; lean_object* v___x_5985_; 
lean_inc(v___y_5982_);
lean_inc_ref(v___y_5981_);
lean_inc(v___y_5980_);
lean_inc_ref(v___y_5979_);
v___x_5984_ = lean_apply_4(v_act_5977_, v___y_5979_, v___y_5980_, v___y_5981_, v___y_5982_);
v___x_5985_ = l_Lean_profileitIOUnsafe___redArg(v_category_5975_, v_opts_5976_, v___x_5984_, v_decl_5978_);
return v___x_5985_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg___boxed(lean_object* v_category_5986_, lean_object* v_opts_5987_, lean_object* v_act_5988_, lean_object* v_decl_5989_, lean_object* v___y_5990_, lean_object* v___y_5991_, lean_object* v___y_5992_, lean_object* v___y_5993_, lean_object* v___y_5994_){
_start:
{
lean_object* v_res_5995_; 
v_res_5995_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v_category_5986_, v_opts_5987_, v_act_5988_, v_decl_5989_, v___y_5990_, v___y_5991_, v___y_5992_, v___y_5993_);
lean_dec(v___y_5993_);
lean_dec_ref(v___y_5992_);
lean_dec(v___y_5991_);
lean_dec_ref(v___y_5990_);
lean_dec_ref(v_opts_5987_);
lean_dec_ref(v_category_5986_);
return v_res_5995_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1(lean_object* v_00_u03b1_5996_, lean_object* v_category_5997_, lean_object* v_opts_5998_, lean_object* v_act_5999_, lean_object* v_decl_6000_, lean_object* v___y_6001_, lean_object* v___y_6002_, lean_object* v___y_6003_, lean_object* v___y_6004_){
_start:
{
lean_object* v___x_6006_; 
v___x_6006_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v_category_5997_, v_opts_5998_, v_act_5999_, v_decl_6000_, v___y_6001_, v___y_6002_, v___y_6003_, v___y_6004_);
return v___x_6006_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___boxed(lean_object* v_00_u03b1_6007_, lean_object* v_category_6008_, lean_object* v_opts_6009_, lean_object* v_act_6010_, lean_object* v_decl_6011_, lean_object* v___y_6012_, lean_object* v___y_6013_, lean_object* v___y_6014_, lean_object* v___y_6015_, lean_object* v___y_6016_){
_start:
{
lean_object* v_res_6017_; 
v_res_6017_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1(v_00_u03b1_6007_, v_category_6008_, v_opts_6009_, v_act_6010_, v_decl_6011_, v___y_6012_, v___y_6013_, v___y_6014_, v___y_6015_);
lean_dec(v___y_6015_);
lean_dec_ref(v___y_6014_);
lean_dec(v___y_6013_);
lean_dec_ref(v___y_6012_);
lean_dec_ref(v_opts_6009_);
lean_dec_ref(v_category_6008_);
return v_res_6017_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(lean_object* v_cctx_6018_, lean_object* v_env_6019_, lean_object* v_act_6020_, lean_object* v_constantsPerTask_6021_, lean_object* v_n_6022_, lean_object* v_ngen_6023_, lean_object* v_tasks_6024_, lean_object* v_start_6025_, lean_object* v_cnt_6026_, lean_object* v_idx_6027_){
_start:
{
lean_object* v___x_6029_; lean_object* v_moduleData_6030_; lean_object* v___x_6031_; uint8_t v___x_6032_; 
v___x_6029_ = l_Lean_Environment_header(v_env_6019_);
v_moduleData_6030_ = lean_ctor_get(v___x_6029_, 7);
lean_inc_ref(v_moduleData_6030_);
lean_dec_ref(v___x_6029_);
v___x_6031_ = lean_array_get_size(v_moduleData_6030_);
v___x_6032_ = lean_nat_dec_lt(v_idx_6027_, v___x_6031_);
if (v___x_6032_ == 0)
{
uint8_t v___x_6033_; 
lean_dec_ref(v_moduleData_6030_);
lean_dec(v_idx_6027_);
lean_dec(v_cnt_6026_);
v___x_6033_ = lean_nat_dec_lt(v_start_6025_, v_n_6022_);
if (v___x_6033_ == 0)
{
lean_object* v___x_6034_; 
lean_dec(v_start_6025_);
lean_dec_ref(v_ngen_6023_);
lean_dec(v_n_6022_);
lean_dec_ref(v_act_6020_);
lean_dec_ref(v_env_6019_);
lean_dec_ref(v_cctx_6018_);
v___x_6034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6034_, 0, v_tasks_6024_);
return v___x_6034_;
}
else
{
lean_object* v_namePrefix_6035_; lean_object* v_idx_6036_; lean_object* v___x_6038_; uint8_t v_isShared_6039_; uint8_t v_isSharedCheck_6050_; 
v_namePrefix_6035_ = lean_ctor_get(v_ngen_6023_, 0);
v_idx_6036_ = lean_ctor_get(v_ngen_6023_, 1);
v_isSharedCheck_6050_ = !lean_is_exclusive(v_ngen_6023_);
if (v_isSharedCheck_6050_ == 0)
{
v___x_6038_ = v_ngen_6023_;
v_isShared_6039_ = v_isSharedCheck_6050_;
goto v_resetjp_6037_;
}
else
{
lean_inc(v_idx_6036_);
lean_inc(v_namePrefix_6035_);
lean_dec(v_ngen_6023_);
v___x_6038_ = lean_box(0);
v_isShared_6039_ = v_isSharedCheck_6050_;
goto v_resetjp_6037_;
}
v_resetjp_6037_:
{
lean_object* v___x_6040_; lean_object* v___x_6041_; lean_object* v___x_6043_; 
v___x_6040_ = l_Lean_Name_num___override(v_namePrefix_6035_, v_idx_6036_);
v___x_6041_ = lean_unsigned_to_nat(1u);
if (v_isShared_6039_ == 0)
{
lean_ctor_set(v___x_6038_, 1, v___x_6041_);
lean_ctor_set(v___x_6038_, 0, v___x_6040_);
v___x_6043_ = v___x_6038_;
goto v_reusejp_6042_;
}
else
{
lean_object* v_reuseFailAlloc_6049_; 
v_reuseFailAlloc_6049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6049_, 0, v___x_6040_);
lean_ctor_set(v_reuseFailAlloc_6049_, 1, v___x_6041_);
v___x_6043_ = v_reuseFailAlloc_6049_;
goto v_reusejp_6042_;
}
v_reusejp_6042_:
{
lean_object* v___x_6044_; lean_object* v___x_6045_; lean_object* v___x_6046_; lean_object* v___x_6047_; lean_object* v___x_6048_; 
v___x_6044_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_6044_, 0, lean_box(0));
lean_closure_set(v___x_6044_, 1, v_cctx_6018_);
lean_closure_set(v___x_6044_, 2, v___x_6043_);
lean_closure_set(v___x_6044_, 3, v_env_6019_);
lean_closure_set(v___x_6044_, 4, v_act_6020_);
lean_closure_set(v___x_6044_, 5, v_start_6025_);
lean_closure_set(v___x_6044_, 6, v_n_6022_);
v___x_6045_ = lean_unsigned_to_nat(0u);
v___x_6046_ = lean_io_as_task(v___x_6044_, v___x_6045_);
v___x_6047_ = lean_array_push(v_tasks_6024_, v___x_6046_);
v___x_6048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6048_, 0, v___x_6047_);
return v___x_6048_;
}
}
}
}
else
{
lean_object* v_mdata_6051_; lean_object* v_constants_6052_; lean_object* v___x_6053_; lean_object* v_cnt_6054_; uint8_t v___x_6055_; 
v_mdata_6051_ = lean_array_fget(v_moduleData_6030_, v_idx_6027_);
lean_dec_ref(v_moduleData_6030_);
v_constants_6052_ = lean_ctor_get(v_mdata_6051_, 2);
lean_inc_ref(v_constants_6052_);
lean_dec(v_mdata_6051_);
v___x_6053_ = lean_array_get_size(v_constants_6052_);
lean_dec_ref(v_constants_6052_);
v_cnt_6054_ = lean_nat_add(v_cnt_6026_, v___x_6053_);
lean_dec(v_cnt_6026_);
v___x_6055_ = lean_nat_dec_lt(v_constantsPerTask_6021_, v_cnt_6054_);
if (v___x_6055_ == 0)
{
lean_object* v___x_6056_; lean_object* v___x_6057_; 
v___x_6056_ = lean_unsigned_to_nat(1u);
v___x_6057_ = lean_nat_add(v_idx_6027_, v___x_6056_);
lean_dec(v_idx_6027_);
v_cnt_6026_ = v_cnt_6054_;
v_idx_6027_ = v___x_6057_;
goto _start;
}
else
{
lean_object* v_namePrefix_6059_; lean_object* v_idx_6060_; lean_object* v___x_6062_; uint8_t v_isShared_6063_; uint8_t v_isSharedCheck_6077_; 
lean_dec(v_cnt_6054_);
v_namePrefix_6059_ = lean_ctor_get(v_ngen_6023_, 0);
v_idx_6060_ = lean_ctor_get(v_ngen_6023_, 1);
v_isSharedCheck_6077_ = !lean_is_exclusive(v_ngen_6023_);
if (v_isSharedCheck_6077_ == 0)
{
v___x_6062_ = v_ngen_6023_;
v_isShared_6063_ = v_isSharedCheck_6077_;
goto v_resetjp_6061_;
}
else
{
lean_inc(v_idx_6060_);
lean_inc(v_namePrefix_6059_);
lean_dec(v_ngen_6023_);
v___x_6062_ = lean_box(0);
v_isShared_6063_ = v_isSharedCheck_6077_;
goto v_resetjp_6061_;
}
v_resetjp_6061_:
{
lean_object* v___x_6064_; lean_object* v___x_6065_; lean_object* v___x_6067_; 
lean_inc(v_idx_6060_);
lean_inc(v_namePrefix_6059_);
v___x_6064_ = l_Lean_Name_num___override(v_namePrefix_6059_, v_idx_6060_);
v___x_6065_ = lean_unsigned_to_nat(1u);
if (v_isShared_6063_ == 0)
{
lean_ctor_set(v___x_6062_, 1, v___x_6065_);
lean_ctor_set(v___x_6062_, 0, v___x_6064_);
v___x_6067_ = v___x_6062_;
goto v_reusejp_6066_;
}
else
{
lean_object* v_reuseFailAlloc_6076_; 
v_reuseFailAlloc_6076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6076_, 0, v___x_6064_);
lean_ctor_set(v_reuseFailAlloc_6076_, 1, v___x_6065_);
v___x_6067_ = v_reuseFailAlloc_6076_;
goto v_reusejp_6066_;
}
v_reusejp_6066_:
{
lean_object* v___x_6068_; lean_object* v___x_6069_; lean_object* v___x_6070_; lean_object* v___x_6071_; lean_object* v___x_6072_; lean_object* v___x_6073_; lean_object* v___x_6074_; 
v___x_6068_ = lean_nat_add(v_idx_6060_, v___x_6065_);
lean_dec(v_idx_6060_);
v___x_6069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6069_, 0, v_namePrefix_6059_);
lean_ctor_set(v___x_6069_, 1, v___x_6068_);
v___x_6070_ = lean_nat_add(v_idx_6027_, v___x_6065_);
lean_dec(v_idx_6027_);
lean_inc_n(v___x_6070_, 2);
lean_inc_ref(v_act_6020_);
lean_inc_ref(v_env_6019_);
lean_inc_ref(v_cctx_6018_);
v___x_6071_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_6071_, 0, lean_box(0));
lean_closure_set(v___x_6071_, 1, v_cctx_6018_);
lean_closure_set(v___x_6071_, 2, v___x_6067_);
lean_closure_set(v___x_6071_, 3, v_env_6019_);
lean_closure_set(v___x_6071_, 4, v_act_6020_);
lean_closure_set(v___x_6071_, 5, v_start_6025_);
lean_closure_set(v___x_6071_, 6, v___x_6070_);
v___x_6072_ = lean_unsigned_to_nat(0u);
v___x_6073_ = lean_io_as_task(v___x_6071_, v___x_6072_);
v___x_6074_ = lean_array_push(v_tasks_6024_, v___x_6073_);
v_ngen_6023_ = v___x_6069_;
v_tasks_6024_ = v___x_6074_;
v_start_6025_ = v___x_6070_;
v_cnt_6026_ = v___x_6072_;
v_idx_6027_ = v___x_6070_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg___boxed(lean_object* v_cctx_6078_, lean_object* v_env_6079_, lean_object* v_act_6080_, lean_object* v_constantsPerTask_6081_, lean_object* v_n_6082_, lean_object* v_ngen_6083_, lean_object* v_tasks_6084_, lean_object* v_start_6085_, lean_object* v_cnt_6086_, lean_object* v_idx_6087_, lean_object* v___y_6088_){
_start:
{
lean_object* v_res_6089_; 
v_res_6089_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(v_cctx_6078_, v_env_6079_, v_act_6080_, v_constantsPerTask_6081_, v_n_6082_, v_ngen_6083_, v_tasks_6084_, v_start_6085_, v_cnt_6086_, v_idx_6087_);
lean_dec(v_constantsPerTask_6081_);
return v_res_6089_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0(uint8_t v_suppressElabErrors_6098_, lean_object* v_x_6099_){
_start:
{
if (lean_obj_tag(v_x_6099_) == 1)
{
lean_object* v_pre_6100_; 
v_pre_6100_ = lean_ctor_get(v_x_6099_, 0);
switch(lean_obj_tag(v_pre_6100_))
{
case 1:
{
lean_object* v_pre_6101_; 
v_pre_6101_ = lean_ctor_get(v_pre_6100_, 0);
switch(lean_obj_tag(v_pre_6101_))
{
case 0:
{
lean_object* v_str_6102_; lean_object* v_str_6103_; lean_object* v___x_6104_; uint8_t v___x_6105_; 
v_str_6102_ = lean_ctor_get(v_x_6099_, 1);
v_str_6103_ = lean_ctor_get(v_pre_6100_, 1);
v___x_6104_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__0));
v___x_6105_ = lean_string_dec_eq(v_str_6103_, v___x_6104_);
if (v___x_6105_ == 0)
{
lean_object* v___x_6106_; uint8_t v___x_6107_; 
v___x_6106_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__1));
v___x_6107_ = lean_string_dec_eq(v_str_6103_, v___x_6106_);
if (v___x_6107_ == 0)
{
return v___x_6107_;
}
else
{
lean_object* v___x_6108_; uint8_t v___x_6109_; 
v___x_6108_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__2));
v___x_6109_ = lean_string_dec_eq(v_str_6102_, v___x_6108_);
if (v___x_6109_ == 0)
{
return v___x_6109_;
}
else
{
return v_suppressElabErrors_6098_;
}
}
}
else
{
lean_object* v___x_6110_; uint8_t v___x_6111_; 
v___x_6110_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__3));
v___x_6111_ = lean_string_dec_eq(v_str_6102_, v___x_6110_);
if (v___x_6111_ == 0)
{
return v___x_6111_;
}
else
{
return v_suppressElabErrors_6098_;
}
}
}
case 1:
{
lean_object* v_pre_6112_; 
v_pre_6112_ = lean_ctor_get(v_pre_6101_, 0);
if (lean_obj_tag(v_pre_6112_) == 0)
{
lean_object* v_str_6113_; lean_object* v_str_6114_; lean_object* v_str_6115_; lean_object* v___x_6116_; uint8_t v___x_6117_; 
v_str_6113_ = lean_ctor_get(v_x_6099_, 1);
v_str_6114_ = lean_ctor_get(v_pre_6100_, 1);
v_str_6115_ = lean_ctor_get(v_pre_6101_, 1);
v___x_6116_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__4));
v___x_6117_ = lean_string_dec_eq(v_str_6115_, v___x_6116_);
if (v___x_6117_ == 0)
{
return v___x_6117_;
}
else
{
lean_object* v___x_6118_; uint8_t v___x_6119_; 
v___x_6118_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__5));
v___x_6119_ = lean_string_dec_eq(v_str_6114_, v___x_6118_);
if (v___x_6119_ == 0)
{
return v___x_6119_;
}
else
{
lean_object* v___x_6120_; uint8_t v___x_6121_; 
v___x_6120_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__6));
v___x_6121_ = lean_string_dec_eq(v_str_6113_, v___x_6120_);
if (v___x_6121_ == 0)
{
return v___x_6121_;
}
else
{
return v_suppressElabErrors_6098_;
}
}
}
}
else
{
uint8_t v___x_6122_; 
v___x_6122_ = 0;
return v___x_6122_;
}
}
default: 
{
uint8_t v___x_6123_; 
v___x_6123_ = 0;
return v___x_6123_;
}
}
}
case 0:
{
lean_object* v_str_6124_; lean_object* v___x_6125_; uint8_t v___x_6126_; 
v_str_6124_ = lean_ctor_get(v_x_6099_, 1);
v___x_6125_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__7));
v___x_6126_ = lean_string_dec_eq(v_str_6124_, v___x_6125_);
if (v___x_6126_ == 0)
{
return v___x_6126_;
}
else
{
return v_suppressElabErrors_6098_;
}
}
default: 
{
uint8_t v___x_6127_; 
v___x_6127_ = 0;
return v___x_6127_;
}
}
}
else
{
uint8_t v___x_6128_; 
v___x_6128_ = 0;
return v___x_6128_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___boxed(lean_object* v_suppressElabErrors_6129_, lean_object* v_x_6130_){
_start:
{
uint8_t v_suppressElabErrors_boxed_6131_; uint8_t v_res_6132_; lean_object* v_r_6133_; 
v_suppressElabErrors_boxed_6131_ = lean_unbox(v_suppressElabErrors_6129_);
v_res_6132_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0(v_suppressElabErrors_boxed_6131_, v_x_6130_);
lean_dec(v_x_6130_);
v_r_6133_ = lean_box(v_res_6132_);
return v_r_6133_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7_spec__9(lean_object* v_opts_6134_, lean_object* v_opt_6135_){
_start:
{
lean_object* v_name_6136_; lean_object* v_defValue_6137_; lean_object* v_map_6138_; lean_object* v___x_6139_; 
v_name_6136_ = lean_ctor_get(v_opt_6135_, 0);
v_defValue_6137_ = lean_ctor_get(v_opt_6135_, 1);
v_map_6138_ = lean_ctor_get(v_opts_6134_, 0);
v___x_6139_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_6138_, v_name_6136_);
if (lean_obj_tag(v___x_6139_) == 0)
{
uint8_t v___x_6140_; 
v___x_6140_ = lean_unbox(v_defValue_6137_);
return v___x_6140_;
}
else
{
lean_object* v_val_6141_; 
v_val_6141_ = lean_ctor_get(v___x_6139_, 0);
lean_inc(v_val_6141_);
lean_dec_ref_known(v___x_6139_, 1);
if (lean_obj_tag(v_val_6141_) == 1)
{
uint8_t v_v_6142_; 
v_v_6142_ = lean_ctor_get_uint8(v_val_6141_, 0);
lean_dec_ref_known(v_val_6141_, 0);
return v_v_6142_;
}
else
{
uint8_t v___x_6143_; 
lean_dec(v_val_6141_);
v___x_6143_ = lean_unbox(v_defValue_6137_);
return v___x_6143_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7_spec__9___boxed(lean_object* v_opts_6144_, lean_object* v_opt_6145_){
_start:
{
uint8_t v_res_6146_; lean_object* v_r_6147_; 
v_res_6146_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7_spec__9(v_opts_6144_, v_opt_6145_);
lean_dec_ref(v_opt_6145_);
lean_dec_ref(v_opts_6144_);
v_r_6147_ = lean_box(v_res_6146_);
return v_r_6147_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7(lean_object* v_ref_6149_, lean_object* v_msgData_6150_, uint8_t v_severity_6151_, uint8_t v_isSilent_6152_, lean_object* v___y_6153_, lean_object* v___y_6154_, lean_object* v___y_6155_, lean_object* v___y_6156_){
_start:
{
lean_object* v___y_6159_; uint8_t v___y_6160_; uint8_t v___y_6161_; lean_object* v___y_6162_; lean_object* v___y_6163_; lean_object* v___y_6164_; lean_object* v___y_6165_; lean_object* v_toCold_6166_; lean_object* v___y_6167_; lean_object* v___y_6196_; lean_object* v___y_6197_; lean_object* v___y_6198_; uint8_t v___y_6199_; uint8_t v___y_6200_; uint8_t v___y_6201_; lean_object* v___y_6202_; lean_object* v___y_6203_; uint8_t v___y_6223_; lean_object* v___y_6224_; lean_object* v___y_6225_; uint8_t v___y_6226_; uint8_t v___y_6227_; lean_object* v___y_6228_; lean_object* v___y_6229_; uint8_t v___y_6233_; uint8_t v___y_6234_; uint8_t v___x_6244_; uint8_t v___y_6246_; uint8_t v___x_6252_; 
v___x_6244_ = 2;
v___x_6252_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6151_, v___x_6244_);
if (v___x_6252_ == 0)
{
v___y_6246_ = v___x_6252_;
goto v___jp_6245_;
}
else
{
uint8_t v___x_6253_; 
lean_inc_ref(v_msgData_6150_);
v___x_6253_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_6150_);
if (v___x_6253_ == 0)
{
v___y_6246_ = v___x_6253_;
goto v___jp_6245_;
}
else
{
lean_object* v___x_6254_; lean_object* v___x_6255_; 
lean_dec_ref(v_msgData_6150_);
v___x_6254_ = lean_box(0);
v___x_6255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6255_, 0, v___x_6254_);
return v___x_6255_;
}
}
v___jp_6158_:
{
lean_object* v_currNamespace_6168_; lean_object* v_openDecls_6169_; lean_object* v___x_6170_; lean_object* v___x_6171_; lean_object* v___x_6172_; lean_object* v___x_6173_; lean_object* v_env_6174_; lean_object* v_nextMacroScope_6175_; lean_object* v_ngen_6176_; lean_object* v_auxDeclNGen_6177_; lean_object* v_traceState_6178_; lean_object* v_cache_6179_; lean_object* v_recordedDeps_6180_; lean_object* v_messages_6181_; lean_object* v_infoState_6182_; lean_object* v_snapshotTasks_6183_; lean_object* v___x_6185_; uint8_t v_isShared_6186_; uint8_t v_isSharedCheck_6194_; 
v_currNamespace_6168_ = lean_ctor_get(v_toCold_6166_, 4);
v_openDecls_6169_ = lean_ctor_get(v_toCold_6166_, 5);
lean_inc(v_openDecls_6169_);
lean_inc(v_currNamespace_6168_);
v___x_6170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6170_, 0, v_currNamespace_6168_);
lean_ctor_set(v___x_6170_, 1, v_openDecls_6169_);
v___x_6171_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6171_, 0, v___x_6170_);
lean_ctor_set(v___x_6171_, 1, v___y_6164_);
lean_inc_ref(v___y_6165_);
lean_inc_ref(v___y_6159_);
v___x_6172_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_6172_, 0, v___y_6159_);
lean_ctor_set(v___x_6172_, 1, v___y_6163_);
lean_ctor_set(v___x_6172_, 2, v___y_6162_);
lean_ctor_set(v___x_6172_, 3, v___y_6165_);
lean_ctor_set(v___x_6172_, 4, v___x_6171_);
lean_ctor_set_uint8(v___x_6172_, sizeof(void*)*5, v___y_6160_);
lean_ctor_set_uint8(v___x_6172_, sizeof(void*)*5 + 1, v___y_6161_);
lean_ctor_set_uint8(v___x_6172_, sizeof(void*)*5 + 2, v_isSilent_6152_);
v___x_6173_ = lean_st_ref_take(v___y_6167_);
v_env_6174_ = lean_ctor_get(v___x_6173_, 0);
v_nextMacroScope_6175_ = lean_ctor_get(v___x_6173_, 1);
v_ngen_6176_ = lean_ctor_get(v___x_6173_, 2);
v_auxDeclNGen_6177_ = lean_ctor_get(v___x_6173_, 3);
v_traceState_6178_ = lean_ctor_get(v___x_6173_, 4);
v_cache_6179_ = lean_ctor_get(v___x_6173_, 5);
v_recordedDeps_6180_ = lean_ctor_get(v___x_6173_, 6);
v_messages_6181_ = lean_ctor_get(v___x_6173_, 7);
v_infoState_6182_ = lean_ctor_get(v___x_6173_, 8);
v_snapshotTasks_6183_ = lean_ctor_get(v___x_6173_, 9);
v_isSharedCheck_6194_ = !lean_is_exclusive(v___x_6173_);
if (v_isSharedCheck_6194_ == 0)
{
v___x_6185_ = v___x_6173_;
v_isShared_6186_ = v_isSharedCheck_6194_;
goto v_resetjp_6184_;
}
else
{
lean_inc(v_snapshotTasks_6183_);
lean_inc(v_infoState_6182_);
lean_inc(v_messages_6181_);
lean_inc(v_recordedDeps_6180_);
lean_inc(v_cache_6179_);
lean_inc(v_traceState_6178_);
lean_inc(v_auxDeclNGen_6177_);
lean_inc(v_ngen_6176_);
lean_inc(v_nextMacroScope_6175_);
lean_inc(v_env_6174_);
lean_dec(v___x_6173_);
v___x_6185_ = lean_box(0);
v_isShared_6186_ = v_isSharedCheck_6194_;
goto v_resetjp_6184_;
}
v_resetjp_6184_:
{
lean_object* v___x_6187_; lean_object* v___x_6188_; lean_object* v___x_6190_; 
v___x_6187_ = lean_box(0);
v___x_6188_ = l_Lean_MessageLog_add(v___x_6172_, v_messages_6181_);
if (v_isShared_6186_ == 0)
{
lean_ctor_set(v___x_6185_, 7, v___x_6188_);
v___x_6190_ = v___x_6185_;
goto v_reusejp_6189_;
}
else
{
lean_object* v_reuseFailAlloc_6193_; 
v_reuseFailAlloc_6193_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6193_, 0, v_env_6174_);
lean_ctor_set(v_reuseFailAlloc_6193_, 1, v_nextMacroScope_6175_);
lean_ctor_set(v_reuseFailAlloc_6193_, 2, v_ngen_6176_);
lean_ctor_set(v_reuseFailAlloc_6193_, 3, v_auxDeclNGen_6177_);
lean_ctor_set(v_reuseFailAlloc_6193_, 4, v_traceState_6178_);
lean_ctor_set(v_reuseFailAlloc_6193_, 5, v_cache_6179_);
lean_ctor_set(v_reuseFailAlloc_6193_, 6, v_recordedDeps_6180_);
lean_ctor_set(v_reuseFailAlloc_6193_, 7, v___x_6188_);
lean_ctor_set(v_reuseFailAlloc_6193_, 8, v_infoState_6182_);
lean_ctor_set(v_reuseFailAlloc_6193_, 9, v_snapshotTasks_6183_);
v___x_6190_ = v_reuseFailAlloc_6193_;
goto v_reusejp_6189_;
}
v_reusejp_6189_:
{
lean_object* v___x_6191_; lean_object* v___x_6192_; 
v___x_6191_ = lean_st_ref_put(v___y_6167_, v___x_6190_);
v___x_6192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6192_, 0, v___x_6187_);
return v___x_6192_;
}
}
}
v___jp_6195_:
{
lean_object* v_fileName_6204_; lean_object* v_fileMap_6205_; lean_object* v___x_6206_; lean_object* v___x_6207_; lean_object* v_a_6208_; lean_object* v___x_6210_; uint8_t v_isShared_6211_; uint8_t v_isSharedCheck_6221_; 
v_fileName_6204_ = lean_ctor_get(v___y_6202_, 0);
v_fileMap_6205_ = lean_ctor_get(v___y_6202_, 1);
v___x_6206_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_6150_);
v___x_6207_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(v___x_6206_, v___y_6153_, v___y_6154_, v___y_6155_, v___y_6156_);
v_a_6208_ = lean_ctor_get(v___x_6207_, 0);
v_isSharedCheck_6221_ = !lean_is_exclusive(v___x_6207_);
if (v_isSharedCheck_6221_ == 0)
{
v___x_6210_ = v___x_6207_;
v_isShared_6211_ = v_isSharedCheck_6221_;
goto v_resetjp_6209_;
}
else
{
lean_inc(v_a_6208_);
lean_dec(v___x_6207_);
v___x_6210_ = lean_box(0);
v_isShared_6211_ = v_isSharedCheck_6221_;
goto v_resetjp_6209_;
}
v_resetjp_6209_:
{
lean_object* v___x_6212_; lean_object* v___x_6213_; lean_object* v___x_6214_; lean_object* v___x_6215_; 
lean_inc_ref_n(v_fileMap_6205_, 2);
v___x_6212_ = l_Lean_FileMap_toPosition(v_fileMap_6205_, v___y_6198_);
lean_dec(v___y_6198_);
v___x_6213_ = l_Lean_FileMap_toPosition(v_fileMap_6205_, v___y_6203_);
lean_dec(v___y_6203_);
v___x_6214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6214_, 0, v___x_6213_);
v___x_6215_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___closed__0));
if (v___y_6199_ == 0)
{
lean_del_object(v___x_6210_);
lean_dec_ref(v___y_6196_);
v___y_6159_ = v_fileName_6204_;
v___y_6160_ = v___y_6200_;
v___y_6161_ = v___y_6201_;
v___y_6162_ = v___x_6214_;
v___y_6163_ = v___x_6212_;
v___y_6164_ = v_a_6208_;
v___y_6165_ = v___x_6215_;
v_toCold_6166_ = v___y_6197_;
v___y_6167_ = v___y_6156_;
goto v___jp_6158_;
}
else
{
uint8_t v___x_6216_; 
lean_inc(v_a_6208_);
v___x_6216_ = l_Lean_MessageData_hasTag(v___y_6196_, v_a_6208_);
if (v___x_6216_ == 0)
{
lean_object* v___x_6217_; lean_object* v___x_6219_; 
lean_dec_ref_known(v___x_6214_, 1);
lean_dec_ref(v___x_6212_);
lean_dec(v_a_6208_);
v___x_6217_ = lean_box(0);
if (v_isShared_6211_ == 0)
{
lean_ctor_set(v___x_6210_, 0, v___x_6217_);
v___x_6219_ = v___x_6210_;
goto v_reusejp_6218_;
}
else
{
lean_object* v_reuseFailAlloc_6220_; 
v_reuseFailAlloc_6220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6220_, 0, v___x_6217_);
v___x_6219_ = v_reuseFailAlloc_6220_;
goto v_reusejp_6218_;
}
v_reusejp_6218_:
{
return v___x_6219_;
}
}
else
{
lean_del_object(v___x_6210_);
v___y_6159_ = v_fileName_6204_;
v___y_6160_ = v___y_6200_;
v___y_6161_ = v___y_6201_;
v___y_6162_ = v___x_6214_;
v___y_6163_ = v___x_6212_;
v___y_6164_ = v_a_6208_;
v___y_6165_ = v___x_6215_;
v_toCold_6166_ = v___y_6197_;
v___y_6167_ = v___y_6156_;
goto v___jp_6158_;
}
}
}
}
v___jp_6222_:
{
lean_object* v___x_6230_; 
v___x_6230_ = l_Lean_Syntax_getTailPos_x3f(v___y_6228_, v___y_6226_);
lean_dec(v___y_6228_);
if (lean_obj_tag(v___x_6230_) == 0)
{
lean_inc(v___y_6229_);
v___y_6196_ = v___y_6224_;
v___y_6197_ = v___y_6225_;
v___y_6198_ = v___y_6229_;
v___y_6199_ = v___y_6223_;
v___y_6200_ = v___y_6226_;
v___y_6201_ = v___y_6227_;
v___y_6202_ = v___y_6225_;
v___y_6203_ = v___y_6229_;
goto v___jp_6195_;
}
else
{
lean_object* v_val_6231_; 
v_val_6231_ = lean_ctor_get(v___x_6230_, 0);
lean_inc(v_val_6231_);
lean_dec_ref_known(v___x_6230_, 1);
v___y_6196_ = v___y_6224_;
v___y_6197_ = v___y_6225_;
v___y_6198_ = v___y_6229_;
v___y_6199_ = v___y_6223_;
v___y_6200_ = v___y_6226_;
v___y_6201_ = v___y_6227_;
v___y_6202_ = v___y_6225_;
v___y_6203_ = v_val_6231_;
goto v___jp_6195_;
}
}
v___jp_6232_:
{
lean_object* v_toCold_6235_; lean_object* v_ref_6236_; uint8_t v_suppressElabErrors_6237_; lean_object* v___x_6238_; lean_object* v___f_6239_; lean_object* v_ref_6240_; lean_object* v___x_6241_; 
v_toCold_6235_ = lean_ctor_get(v___y_6155_, 0);
v_ref_6236_ = lean_ctor_get(v___y_6155_, 2);
v_suppressElabErrors_6237_ = lean_ctor_get_uint8(v___y_6155_, sizeof(void*)*3 + 2);
v___x_6238_ = lean_box(v_suppressElabErrors_6237_);
v___f_6239_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___boxed), 2, 1);
lean_closure_set(v___f_6239_, 0, v___x_6238_);
v_ref_6240_ = l_Lean_replaceRef(v_ref_6149_, v_ref_6236_);
v___x_6241_ = l_Lean_Syntax_getPos_x3f(v_ref_6240_, v___y_6233_);
if (lean_obj_tag(v___x_6241_) == 0)
{
lean_object* v___x_6242_; 
v___x_6242_ = lean_unsigned_to_nat(0u);
v___y_6223_ = v_suppressElabErrors_6237_;
v___y_6224_ = v___f_6239_;
v___y_6225_ = v_toCold_6235_;
v___y_6226_ = v___y_6233_;
v___y_6227_ = v___y_6234_;
v___y_6228_ = v_ref_6240_;
v___y_6229_ = v___x_6242_;
goto v___jp_6222_;
}
else
{
lean_object* v_val_6243_; 
v_val_6243_ = lean_ctor_get(v___x_6241_, 0);
lean_inc(v_val_6243_);
lean_dec_ref_known(v___x_6241_, 1);
v___y_6223_ = v_suppressElabErrors_6237_;
v___y_6224_ = v___f_6239_;
v___y_6225_ = v_toCold_6235_;
v___y_6226_ = v___y_6233_;
v___y_6227_ = v___y_6234_;
v___y_6228_ = v_ref_6240_;
v___y_6229_ = v_val_6243_;
goto v___jp_6222_;
}
}
v___jp_6245_:
{
uint8_t v___x_6247_; uint8_t v___x_6248_; 
v___x_6247_ = 1;
v___x_6248_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6151_, v___x_6247_);
if (v___x_6248_ == 0)
{
v___y_6233_ = v___y_6246_;
v___y_6234_ = v_severity_6151_;
goto v___jp_6232_;
}
else
{
lean_object* v___x_6249_; lean_object* v___x_6250_; uint8_t v___x_6251_; 
v___x_6249_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_6155_);
v___x_6250_ = l_Lean_warningAsError;
v___x_6251_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7_spec__9(v___x_6249_, v___x_6250_);
lean_dec_ref(v___x_6249_);
if (v___x_6251_ == 0)
{
v___y_6233_ = v___y_6246_;
v___y_6234_ = v_severity_6151_;
goto v___jp_6232_;
}
else
{
v___y_6233_ = v___y_6246_;
v___y_6234_ = v___x_6244_;
goto v___jp_6232_;
}
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
v_ref_6276_ = lean_ctor_get(v___y_6273_, 2);
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
v___x_6392_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2);
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
v_moduleData_6408_ = lean_ctor_get(v___x_6407_, 7);
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
v___x_6498_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
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
lean_object* v_a_6537_; lean_object* v___x_6559_; lean_object* v_ngen_6560_; lean_object* v_namePrefix_6561_; lean_object* v_idx_6562_; lean_object* v___x_6564_; uint8_t v_isShared_6565_; uint8_t v_isSharedCheck_6608_; 
v___x_6559_ = lean_st_ref_get(v_a_6534_);
v_ngen_6560_ = lean_ctor_get(v___x_6559_, 2);
lean_inc_ref(v_ngen_6560_);
lean_dec(v___x_6559_);
v_namePrefix_6561_ = lean_ctor_get(v_ngen_6560_, 0);
v_idx_6562_ = lean_ctor_get(v_ngen_6560_, 1);
v_isSharedCheck_6608_ = !lean_is_exclusive(v_ngen_6560_);
if (v_isSharedCheck_6608_ == 0)
{
v___x_6564_ = v_ngen_6560_;
v_isShared_6565_ = v_isSharedCheck_6608_;
goto v_resetjp_6563_;
}
else
{
lean_inc(v_idx_6562_);
lean_inc(v_namePrefix_6561_);
lean_dec(v_ngen_6560_);
v___x_6564_ = lean_box(0);
v_isShared_6565_ = v_isSharedCheck_6608_;
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
lean_object* v___x_6566_; lean_object* v___x_6567_; lean_object* v___x_6569_; 
lean_inc(v_idx_6562_);
lean_inc(v_namePrefix_6561_);
v___x_6566_ = l_Lean_Name_num___override(v_namePrefix_6561_, v_idx_6562_);
v___x_6567_ = lean_unsigned_to_nat(1u);
if (v_isShared_6565_ == 0)
{
lean_ctor_set(v___x_6564_, 1, v___x_6567_);
lean_ctor_set(v___x_6564_, 0, v___x_6566_);
v___x_6569_ = v___x_6564_;
goto v_reusejp_6568_;
}
else
{
lean_object* v_reuseFailAlloc_6607_; 
v_reuseFailAlloc_6607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6607_, 0, v___x_6566_);
lean_ctor_set(v_reuseFailAlloc_6607_, 1, v___x_6567_);
v___x_6569_ = v_reuseFailAlloc_6607_;
goto v_reusejp_6568_;
}
v_reusejp_6568_:
{
lean_object* v___f_6570_; lean_object* v___x_6571_; lean_object* v___x_6572_; lean_object* v___x_6573_; lean_object* v_env_6574_; lean_object* v_nextMacroScope_6575_; lean_object* v_auxDeclNGen_6576_; lean_object* v_traceState_6577_; lean_object* v_cache_6578_; lean_object* v_recordedDeps_6579_; lean_object* v_messages_6580_; lean_object* v_infoState_6581_; lean_object* v_snapshotTasks_6582_; lean_object* v___x_6584_; uint8_t v_isShared_6585_; uint8_t v_isSharedCheck_6605_; 
lean_inc_ref(v_a_6533_);
v___f_6570_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_6570_, 0, v_a_6533_);
lean_closure_set(v___f_6570_, 1, v___x_6569_);
lean_closure_set(v___f_6570_, 2, v_addEntry_6526_);
lean_closure_set(v___f_6570_, 3, v_constantsPerTask_6528_);
lean_closure_set(v___f_6570_, 4, v_droppedEntriesRef_6529_);
lean_closure_set(v___f_6570_, 5, v_droppedKeys_6527_);
v___x_6571_ = lean_nat_add(v_idx_6562_, v___x_6567_);
lean_dec(v_idx_6562_);
v___x_6572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6572_, 0, v_namePrefix_6561_);
lean_ctor_set(v___x_6572_, 1, v___x_6571_);
v___x_6573_ = lean_st_ref_take(v_a_6534_);
v_env_6574_ = lean_ctor_get(v___x_6573_, 0);
v_nextMacroScope_6575_ = lean_ctor_get(v___x_6573_, 1);
v_auxDeclNGen_6576_ = lean_ctor_get(v___x_6573_, 3);
v_traceState_6577_ = lean_ctor_get(v___x_6573_, 4);
v_cache_6578_ = lean_ctor_get(v___x_6573_, 5);
v_recordedDeps_6579_ = lean_ctor_get(v___x_6573_, 6);
v_messages_6580_ = lean_ctor_get(v___x_6573_, 7);
v_infoState_6581_ = lean_ctor_get(v___x_6573_, 8);
v_snapshotTasks_6582_ = lean_ctor_get(v___x_6573_, 9);
v_isSharedCheck_6605_ = !lean_is_exclusive(v___x_6573_);
if (v_isSharedCheck_6605_ == 0)
{
lean_object* v_unused_6606_; 
v_unused_6606_ = lean_ctor_get(v___x_6573_, 2);
lean_dec(v_unused_6606_);
v___x_6584_ = v___x_6573_;
v_isShared_6585_ = v_isSharedCheck_6605_;
goto v_resetjp_6583_;
}
else
{
lean_inc(v_snapshotTasks_6582_);
lean_inc(v_infoState_6581_);
lean_inc(v_messages_6580_);
lean_inc(v_recordedDeps_6579_);
lean_inc(v_cache_6578_);
lean_inc(v_traceState_6577_);
lean_inc(v_auxDeclNGen_6576_);
lean_inc(v_nextMacroScope_6575_);
lean_inc(v_env_6574_);
lean_dec(v___x_6573_);
v___x_6584_ = lean_box(0);
v_isShared_6585_ = v_isSharedCheck_6605_;
goto v_resetjp_6583_;
}
v_resetjp_6583_:
{
lean_object* v___x_6587_; 
if (v_isShared_6585_ == 0)
{
lean_ctor_set(v___x_6584_, 2, v___x_6572_);
v___x_6587_ = v___x_6584_;
goto v_reusejp_6586_;
}
else
{
lean_object* v_reuseFailAlloc_6604_; 
v_reuseFailAlloc_6604_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6604_, 0, v_env_6574_);
lean_ctor_set(v_reuseFailAlloc_6604_, 1, v_nextMacroScope_6575_);
lean_ctor_set(v_reuseFailAlloc_6604_, 2, v___x_6572_);
lean_ctor_set(v_reuseFailAlloc_6604_, 3, v_auxDeclNGen_6576_);
lean_ctor_set(v_reuseFailAlloc_6604_, 4, v_traceState_6577_);
lean_ctor_set(v_reuseFailAlloc_6604_, 5, v_cache_6578_);
lean_ctor_set(v_reuseFailAlloc_6604_, 6, v_recordedDeps_6579_);
lean_ctor_set(v_reuseFailAlloc_6604_, 7, v_messages_6580_);
lean_ctor_set(v_reuseFailAlloc_6604_, 8, v_infoState_6581_);
lean_ctor_set(v_reuseFailAlloc_6604_, 9, v_snapshotTasks_6582_);
v___x_6587_ = v_reuseFailAlloc_6604_;
goto v_reusejp_6586_;
}
v_reusejp_6586_:
{
lean_object* v___x_6588_; lean_object* v___x_6589_; 
v___x_6588_ = lean_st_ref_put(v_a_6534_, v___x_6587_);
v___x_6589_ = lean_st_ref_get(v_ref_6525_);
if (lean_obj_tag(v___x_6589_) == 0)
{
lean_object* v___x_6590_; lean_object* v___x_6591_; lean_object* v___x_6592_; lean_object* v___x_6593_; 
v___x_6590_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_6533_);
v___x_6591_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___closed__0));
v___x_6592_ = lean_box(0);
v___x_6593_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v___x_6591_, v___x_6590_, v___f_6570_, v___x_6592_, v_a_6531_, v_a_6532_, v_a_6533_, v_a_6534_);
lean_dec_ref(v___x_6590_);
if (lean_obj_tag(v___x_6593_) == 0)
{
lean_object* v_a_6594_; 
v_a_6594_ = lean_ctor_get(v___x_6593_, 0);
lean_inc(v_a_6594_);
lean_dec_ref_known(v___x_6593_, 1);
v_a_6537_ = v_a_6594_;
goto v___jp_6536_;
}
else
{
lean_object* v_a_6595_; lean_object* v___x_6597_; uint8_t v_isShared_6598_; uint8_t v_isSharedCheck_6602_; 
lean_dec_ref(v_ty_6530_);
v_a_6595_ = lean_ctor_get(v___x_6593_, 0);
v_isSharedCheck_6602_ = !lean_is_exclusive(v___x_6593_);
if (v_isSharedCheck_6602_ == 0)
{
v___x_6597_ = v___x_6593_;
v_isShared_6598_ = v_isSharedCheck_6602_;
goto v_resetjp_6596_;
}
else
{
lean_inc(v_a_6595_);
lean_dec(v___x_6593_);
v___x_6597_ = lean_box(0);
v_isShared_6598_ = v_isSharedCheck_6602_;
goto v_resetjp_6596_;
}
v_resetjp_6596_:
{
lean_object* v___x_6600_; 
if (v_isShared_6598_ == 0)
{
v___x_6600_ = v___x_6597_;
goto v_reusejp_6599_;
}
else
{
lean_object* v_reuseFailAlloc_6601_; 
v_reuseFailAlloc_6601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6601_, 0, v_a_6595_);
v___x_6600_ = v_reuseFailAlloc_6601_;
goto v_reusejp_6599_;
}
v_reusejp_6599_:
{
return v___x_6600_;
}
}
}
}
else
{
lean_object* v_val_6603_; 
lean_dec_ref(v___f_6570_);
v_val_6603_ = lean_ctor_get(v___x_6589_, 0);
lean_inc(v_val_6603_);
lean_dec_ref_known(v___x_6589_, 1);
v_a_6537_ = v_val_6603_;
goto v___jp_6536_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___boxed(lean_object* v_ref_6609_, lean_object* v_addEntry_6610_, lean_object* v_droppedKeys_6611_, lean_object* v_constantsPerTask_6612_, lean_object* v_droppedEntriesRef_6613_, lean_object* v_ty_6614_, lean_object* v_a_6615_, lean_object* v_a_6616_, lean_object* v_a_6617_, lean_object* v_a_6618_, lean_object* v_a_6619_){
_start:
{
lean_object* v_res_6620_; 
v_res_6620_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(v_ref_6609_, v_addEntry_6610_, v_droppedKeys_6611_, v_constantsPerTask_6612_, v_droppedEntriesRef_6613_, v_ty_6614_, v_a_6615_, v_a_6616_, v_a_6617_, v_a_6618_);
lean_dec(v_a_6618_);
lean_dec_ref(v_a_6617_);
lean_dec(v_a_6616_);
lean_dec_ref(v_a_6615_);
lean_dec(v_ref_6609_);
return v_res_6620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches(lean_object* v_00_u03b1_6621_, lean_object* v_ref_6622_, lean_object* v_addEntry_6623_, lean_object* v_droppedKeys_6624_, lean_object* v_constantsPerTask_6625_, lean_object* v_droppedEntriesRef_6626_, lean_object* v_ty_6627_, lean_object* v_a_6628_, lean_object* v_a_6629_, lean_object* v_a_6630_, lean_object* v_a_6631_){
_start:
{
lean_object* v___x_6633_; 
v___x_6633_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(v_ref_6622_, v_addEntry_6623_, v_droppedKeys_6624_, v_constantsPerTask_6625_, v_droppedEntriesRef_6626_, v_ty_6627_, v_a_6628_, v_a_6629_, v_a_6630_, v_a_6631_);
return v___x_6633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___boxed(lean_object* v_00_u03b1_6634_, lean_object* v_ref_6635_, lean_object* v_addEntry_6636_, lean_object* v_droppedKeys_6637_, lean_object* v_constantsPerTask_6638_, lean_object* v_droppedEntriesRef_6639_, lean_object* v_ty_6640_, lean_object* v_a_6641_, lean_object* v_a_6642_, lean_object* v_a_6643_, lean_object* v_a_6644_, lean_object* v_a_6645_){
_start:
{
lean_object* v_res_6646_; 
v_res_6646_ = l_Lean_Meta_LazyDiscrTree_findImportMatches(v_00_u03b1_6634_, v_ref_6635_, v_addEntry_6636_, v_droppedKeys_6637_, v_constantsPerTask_6638_, v_droppedEntriesRef_6639_, v_ty_6640_, v_a_6641_, v_a_6642_, v_a_6643_, v_a_6644_);
lean_dec(v_a_6644_);
lean_dec_ref(v_a_6643_);
lean_dec(v_a_6642_);
lean_dec_ref(v_a_6641_);
lean_dec(v_ref_6635_);
return v_res_6646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0(lean_object* v_00_u03b1_6647_, lean_object* v_cctx_6648_, lean_object* v_ngen_6649_, lean_object* v_env_6650_, lean_object* v_act_6651_, lean_object* v_constantsPerTask_6652_, lean_object* v___y_6653_, lean_object* v___y_6654_, lean_object* v___y_6655_, lean_object* v___y_6656_){
_start:
{
lean_object* v___x_6658_; 
v___x_6658_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(v_cctx_6648_, v_ngen_6649_, v_env_6650_, v_act_6651_, v_constantsPerTask_6652_, v___y_6653_, v___y_6654_, v___y_6655_, v___y_6656_);
return v___x_6658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___boxed(lean_object* v_00_u03b1_6659_, lean_object* v_cctx_6660_, lean_object* v_ngen_6661_, lean_object* v_env_6662_, lean_object* v_act_6663_, lean_object* v_constantsPerTask_6664_, lean_object* v___y_6665_, lean_object* v___y_6666_, lean_object* v___y_6667_, lean_object* v___y_6668_, lean_object* v___y_6669_){
_start:
{
lean_object* v_res_6670_; 
v_res_6670_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0(v_00_u03b1_6659_, v_cctx_6660_, v_ngen_6661_, v_env_6662_, v_act_6663_, v_constantsPerTask_6664_, v___y_6665_, v___y_6666_, v___y_6667_, v___y_6668_);
lean_dec(v___y_6668_);
lean_dec_ref(v___y_6667_);
lean_dec(v___y_6666_);
lean_dec_ref(v___y_6665_);
lean_dec(v_constantsPerTask_6664_);
return v_res_6670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1(lean_object* v_00_u03b1_6671_, lean_object* v_cctx_6672_, lean_object* v_env_6673_, lean_object* v_act_6674_, lean_object* v_constantsPerTask_6675_, lean_object* v_n_6676_, lean_object* v_ngen_6677_, lean_object* v_tasks_6678_, lean_object* v_start_6679_, lean_object* v_cnt_6680_, lean_object* v_idx_6681_, lean_object* v___y_6682_, lean_object* v___y_6683_, lean_object* v___y_6684_, lean_object* v___y_6685_){
_start:
{
lean_object* v___x_6687_; 
v___x_6687_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(v_cctx_6672_, v_env_6673_, v_act_6674_, v_constantsPerTask_6675_, v_n_6676_, v_ngen_6677_, v_tasks_6678_, v_start_6679_, v_cnt_6680_, v_idx_6681_);
return v___x_6687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___boxed(lean_object* v_00_u03b1_6688_, lean_object* v_cctx_6689_, lean_object* v_env_6690_, lean_object* v_act_6691_, lean_object* v_constantsPerTask_6692_, lean_object* v_n_6693_, lean_object* v_ngen_6694_, lean_object* v_tasks_6695_, lean_object* v_start_6696_, lean_object* v_cnt_6697_, lean_object* v_idx_6698_, lean_object* v___y_6699_, lean_object* v___y_6700_, lean_object* v___y_6701_, lean_object* v___y_6702_, lean_object* v___y_6703_){
_start:
{
lean_object* v_res_6704_; 
v_res_6704_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1(v_00_u03b1_6688_, v_cctx_6689_, v_env_6690_, v_act_6691_, v_constantsPerTask_6692_, v_n_6693_, v_ngen_6694_, v_tasks_6695_, v_start_6696_, v_cnt_6697_, v_idx_6698_, v___y_6699_, v___y_6700_, v___y_6701_, v___y_6702_);
lean_dec(v___y_6702_);
lean_dec_ref(v___y_6701_);
lean_dec(v___y_6700_);
lean_dec_ref(v___y_6699_);
lean_dec(v_constantsPerTask_6692_);
return v_res_6704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2(lean_object* v_00_u03b1_6705_, lean_object* v_z_6706_, lean_object* v_tasks_6707_){
_start:
{
lean_object* v___x_6708_; 
v___x_6708_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(v_z_6706_, v_tasks_6707_);
return v___x_6708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___boxed(lean_object* v_00_u03b1_6709_, lean_object* v_z_6710_, lean_object* v_tasks_6711_){
_start:
{
lean_object* v_res_6712_; 
v_res_6712_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2(v_00_u03b1_6709_, v_z_6710_, v_tasks_6711_);
lean_dec_ref(v_tasks_6711_);
return v_res_6712_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5(lean_object* v_00_u03b1_6713_, lean_object* v_as_6714_, size_t v_i_6715_, size_t v_stop_6716_, lean_object* v_b_6717_){
_start:
{
lean_object* v___x_6718_; 
v___x_6718_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(v_as_6714_, v_i_6715_, v_stop_6716_, v_b_6717_);
return v___x_6718_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b1_6719_, lean_object* v_as_6720_, lean_object* v_i_6721_, lean_object* v_stop_6722_, lean_object* v_b_6723_){
_start:
{
size_t v_i_boxed_6724_; size_t v_stop_boxed_6725_; lean_object* v_res_6726_; 
v_i_boxed_6724_ = lean_unbox_usize(v_i_6721_);
lean_dec(v_i_6721_);
v_stop_boxed_6725_ = lean_unbox_usize(v_stop_6722_);
lean_dec(v_stop_6722_);
v_res_6726_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5(v_00_u03b1_6719_, v_as_6720_, v_i_boxed_6724_, v_stop_boxed_6725_, v_b_6723_);
lean_dec_ref(v_as_6720_);
return v_res_6726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(lean_object* v___y_6727_){
_start:
{
lean_object* v___x_6729_; lean_object* v_ngen_6730_; lean_object* v_namePrefix_6731_; lean_object* v_idx_6732_; lean_object* v___x_6734_; uint8_t v_isShared_6735_; uint8_t v_isSharedCheck_6763_; 
v___x_6729_ = lean_st_ref_get(v___y_6727_);
v_ngen_6730_ = lean_ctor_get(v___x_6729_, 2);
lean_inc_ref(v_ngen_6730_);
lean_dec(v___x_6729_);
v_namePrefix_6731_ = lean_ctor_get(v_ngen_6730_, 0);
v_idx_6732_ = lean_ctor_get(v_ngen_6730_, 1);
v_isSharedCheck_6763_ = !lean_is_exclusive(v_ngen_6730_);
if (v_isSharedCheck_6763_ == 0)
{
v___x_6734_ = v_ngen_6730_;
v_isShared_6735_ = v_isSharedCheck_6763_;
goto v_resetjp_6733_;
}
else
{
lean_inc(v_idx_6732_);
lean_inc(v_namePrefix_6731_);
lean_dec(v_ngen_6730_);
v___x_6734_ = lean_box(0);
v_isShared_6735_ = v_isSharedCheck_6763_;
goto v_resetjp_6733_;
}
v_resetjp_6733_:
{
lean_object* v___x_6736_; lean_object* v___x_6737_; lean_object* v___x_6739_; 
lean_inc(v_idx_6732_);
lean_inc(v_namePrefix_6731_);
v___x_6736_ = l_Lean_Name_num___override(v_namePrefix_6731_, v_idx_6732_);
v___x_6737_ = lean_unsigned_to_nat(1u);
if (v_isShared_6735_ == 0)
{
lean_ctor_set(v___x_6734_, 1, v___x_6737_);
lean_ctor_set(v___x_6734_, 0, v___x_6736_);
v___x_6739_ = v___x_6734_;
goto v_reusejp_6738_;
}
else
{
lean_object* v_reuseFailAlloc_6762_; 
v_reuseFailAlloc_6762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6762_, 0, v___x_6736_);
lean_ctor_set(v_reuseFailAlloc_6762_, 1, v___x_6737_);
v___x_6739_ = v_reuseFailAlloc_6762_;
goto v_reusejp_6738_;
}
v_reusejp_6738_:
{
lean_object* v___x_6740_; lean_object* v___x_6741_; lean_object* v___x_6742_; lean_object* v_env_6743_; lean_object* v_nextMacroScope_6744_; lean_object* v_auxDeclNGen_6745_; lean_object* v_traceState_6746_; lean_object* v_cache_6747_; lean_object* v_recordedDeps_6748_; lean_object* v_messages_6749_; lean_object* v_infoState_6750_; lean_object* v_snapshotTasks_6751_; lean_object* v___x_6753_; uint8_t v_isShared_6754_; uint8_t v_isSharedCheck_6760_; 
v___x_6740_ = lean_nat_add(v_idx_6732_, v___x_6737_);
lean_dec(v_idx_6732_);
v___x_6741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6741_, 0, v_namePrefix_6731_);
lean_ctor_set(v___x_6741_, 1, v___x_6740_);
v___x_6742_ = lean_st_ref_take(v___y_6727_);
v_env_6743_ = lean_ctor_get(v___x_6742_, 0);
v_nextMacroScope_6744_ = lean_ctor_get(v___x_6742_, 1);
v_auxDeclNGen_6745_ = lean_ctor_get(v___x_6742_, 3);
v_traceState_6746_ = lean_ctor_get(v___x_6742_, 4);
v_cache_6747_ = lean_ctor_get(v___x_6742_, 5);
v_recordedDeps_6748_ = lean_ctor_get(v___x_6742_, 6);
v_messages_6749_ = lean_ctor_get(v___x_6742_, 7);
v_infoState_6750_ = lean_ctor_get(v___x_6742_, 8);
v_snapshotTasks_6751_ = lean_ctor_get(v___x_6742_, 9);
v_isSharedCheck_6760_ = !lean_is_exclusive(v___x_6742_);
if (v_isSharedCheck_6760_ == 0)
{
lean_object* v_unused_6761_; 
v_unused_6761_ = lean_ctor_get(v___x_6742_, 2);
lean_dec(v_unused_6761_);
v___x_6753_ = v___x_6742_;
v_isShared_6754_ = v_isSharedCheck_6760_;
goto v_resetjp_6752_;
}
else
{
lean_inc(v_snapshotTasks_6751_);
lean_inc(v_infoState_6750_);
lean_inc(v_messages_6749_);
lean_inc(v_recordedDeps_6748_);
lean_inc(v_cache_6747_);
lean_inc(v_traceState_6746_);
lean_inc(v_auxDeclNGen_6745_);
lean_inc(v_nextMacroScope_6744_);
lean_inc(v_env_6743_);
lean_dec(v___x_6742_);
v___x_6753_ = lean_box(0);
v_isShared_6754_ = v_isSharedCheck_6760_;
goto v_resetjp_6752_;
}
v_resetjp_6752_:
{
lean_object* v___x_6756_; 
if (v_isShared_6754_ == 0)
{
lean_ctor_set(v___x_6753_, 2, v___x_6741_);
v___x_6756_ = v___x_6753_;
goto v_reusejp_6755_;
}
else
{
lean_object* v_reuseFailAlloc_6759_; 
v_reuseFailAlloc_6759_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6759_, 0, v_env_6743_);
lean_ctor_set(v_reuseFailAlloc_6759_, 1, v_nextMacroScope_6744_);
lean_ctor_set(v_reuseFailAlloc_6759_, 2, v___x_6741_);
lean_ctor_set(v_reuseFailAlloc_6759_, 3, v_auxDeclNGen_6745_);
lean_ctor_set(v_reuseFailAlloc_6759_, 4, v_traceState_6746_);
lean_ctor_set(v_reuseFailAlloc_6759_, 5, v_cache_6747_);
lean_ctor_set(v_reuseFailAlloc_6759_, 6, v_recordedDeps_6748_);
lean_ctor_set(v_reuseFailAlloc_6759_, 7, v_messages_6749_);
lean_ctor_set(v_reuseFailAlloc_6759_, 8, v_infoState_6750_);
lean_ctor_set(v_reuseFailAlloc_6759_, 9, v_snapshotTasks_6751_);
v___x_6756_ = v_reuseFailAlloc_6759_;
goto v_reusejp_6755_;
}
v_reusejp_6755_:
{
lean_object* v___x_6757_; lean_object* v___x_6758_; 
v___x_6757_ = lean_st_ref_put(v___y_6727_, v___x_6756_);
v___x_6758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6758_, 0, v___x_6739_);
return v___x_6758_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg___boxed(lean_object* v___y_6764_, lean_object* v___y_6765_){
_start:
{
lean_object* v_res_6766_; 
v_res_6766_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(v___y_6764_);
lean_dec(v___y_6764_);
return v_res_6766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1(lean_object* v___y_6767_, lean_object* v___y_6768_){
_start:
{
lean_object* v___x_6770_; 
v___x_6770_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(v___y_6768_);
return v___x_6770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___boxed(lean_object* v___y_6771_, lean_object* v___y_6772_, lean_object* v___y_6773_){
_start:
{
lean_object* v_res_6774_; 
v_res_6774_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1(v___y_6771_, v___y_6772_);
lean_dec(v___y_6772_);
lean_dec_ref(v___y_6771_);
return v_res_6774_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0(void){
_start:
{
lean_object* v___x_6775_; lean_object* v___x_6776_; lean_object* v___x_6777_; 
v___x_6775_ = lean_unsigned_to_nat(32u);
v___x_6776_ = lean_mk_empty_array_with_capacity(v___x_6775_);
v___x_6777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6777_, 0, v___x_6776_);
return v___x_6777_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1(void){
_start:
{
size_t v___x_6778_; lean_object* v___x_6779_; lean_object* v___x_6780_; lean_object* v___x_6781_; lean_object* v___x_6782_; lean_object* v___x_6783_; 
v___x_6778_ = ((size_t)5ULL);
v___x_6779_ = lean_unsigned_to_nat(0u);
v___x_6780_ = lean_unsigned_to_nat(32u);
v___x_6781_ = lean_mk_empty_array_with_capacity(v___x_6780_);
v___x_6782_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0);
v___x_6783_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_6783_, 0, v___x_6782_);
lean_ctor_set(v___x_6783_, 1, v___x_6781_);
lean_ctor_set(v___x_6783_, 2, v___x_6779_);
lean_ctor_set(v___x_6783_, 3, v___x_6779_);
lean_ctor_set_usize(v___x_6783_, 4, v___x_6778_);
return v___x_6783_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2(void){
_start:
{
lean_object* v___x_6784_; lean_object* v___x_6785_; lean_object* v___x_6786_; lean_object* v___x_6787_; 
v___x_6784_ = lean_box(1);
v___x_6785_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1);
v___x_6786_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0);
v___x_6787_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6787_, 0, v___x_6786_);
lean_ctor_set(v___x_6787_, 1, v___x_6785_);
lean_ctor_set(v___x_6787_, 2, v___x_6784_);
return v___x_6787_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_msgData_6788_, lean_object* v___y_6789_, lean_object* v___y_6790_){
_start:
{
lean_object* v___x_6792_; lean_object* v_toCold_6793_; lean_object* v_env_6794_; lean_object* v_options_6795_; uint8_t v___x_6796_; lean_object* v_env_6797_; lean_object* v___x_6798_; lean_object* v___x_6799_; lean_object* v___x_6800_; lean_object* v___x_6801_; lean_object* v___x_6802_; 
v___x_6792_ = lean_st_ref_get(v___y_6790_);
v_toCold_6793_ = lean_ctor_get(v___y_6789_, 0);
v_env_6794_ = lean_ctor_get(v___x_6792_, 0);
lean_inc_ref(v_env_6794_);
lean_dec(v___x_6792_);
v_options_6795_ = lean_ctor_get(v_toCold_6793_, 2);
v___x_6796_ = 0;
v_env_6797_ = l_Lean_Environment_setRecordingDeps(v_env_6794_, v___x_6796_);
v___x_6798_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_6799_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2);
lean_inc_ref(v_options_6795_);
v___x_6800_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6800_, 0, v_env_6797_);
lean_ctor_set(v___x_6800_, 1, v___x_6798_);
lean_ctor_set(v___x_6800_, 2, v___x_6799_);
lean_ctor_set(v___x_6800_, 3, v_options_6795_);
v___x_6801_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_6801_, 0, v___x_6800_);
lean_ctor_set(v___x_6801_, 1, v_msgData_6788_);
v___x_6802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6802_, 0, v___x_6801_);
return v___x_6802_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(lean_object* v_msgData_6803_, lean_object* v___y_6804_, lean_object* v___y_6805_, lean_object* v___y_6806_){
_start:
{
lean_object* v_res_6807_; 
v_res_6807_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5(v_msgData_6803_, v___y_6804_, v___y_6805_);
lean_dec(v___y_6805_);
lean_dec_ref(v___y_6804_);
return v_res_6807_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4(lean_object* v_ref_6808_, lean_object* v_msgData_6809_, uint8_t v_severity_6810_, uint8_t v_isSilent_6811_, lean_object* v___y_6812_, lean_object* v___y_6813_){
_start:
{
lean_object* v___y_6816_; uint8_t v___y_6817_; lean_object* v___y_6818_; uint8_t v___y_6819_; lean_object* v___y_6820_; lean_object* v___y_6821_; lean_object* v___y_6822_; lean_object* v_toCold_6823_; lean_object* v___y_6824_; lean_object* v___y_6853_; lean_object* v___y_6854_; uint8_t v___y_6855_; lean_object* v___y_6856_; uint8_t v___y_6857_; lean_object* v___y_6858_; uint8_t v___y_6859_; lean_object* v___y_6860_; lean_object* v___y_6880_; uint8_t v___y_6881_; lean_object* v___y_6882_; uint8_t v___y_6883_; uint8_t v___y_6884_; lean_object* v___y_6885_; lean_object* v___y_6886_; uint8_t v___y_6890_; uint8_t v___y_6891_; uint8_t v___x_6901_; uint8_t v___y_6903_; uint8_t v___x_6909_; 
v___x_6901_ = 2;
v___x_6909_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6810_, v___x_6901_);
if (v___x_6909_ == 0)
{
v___y_6903_ = v___x_6909_;
goto v___jp_6902_;
}
else
{
uint8_t v___x_6910_; 
lean_inc_ref(v_msgData_6809_);
v___x_6910_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_6809_);
if (v___x_6910_ == 0)
{
v___y_6903_ = v___x_6910_;
goto v___jp_6902_;
}
else
{
lean_object* v___x_6911_; lean_object* v___x_6912_; 
lean_dec_ref(v_msgData_6809_);
v___x_6911_ = lean_box(0);
v___x_6912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6912_, 0, v___x_6911_);
return v___x_6912_;
}
}
v___jp_6815_:
{
lean_object* v_currNamespace_6825_; lean_object* v_openDecls_6826_; lean_object* v___x_6827_; lean_object* v___x_6828_; lean_object* v___x_6829_; lean_object* v___x_6830_; lean_object* v_env_6831_; lean_object* v_nextMacroScope_6832_; lean_object* v_ngen_6833_; lean_object* v_auxDeclNGen_6834_; lean_object* v_traceState_6835_; lean_object* v_cache_6836_; lean_object* v_recordedDeps_6837_; lean_object* v_messages_6838_; lean_object* v_infoState_6839_; lean_object* v_snapshotTasks_6840_; lean_object* v___x_6842_; uint8_t v_isShared_6843_; uint8_t v_isSharedCheck_6851_; 
v_currNamespace_6825_ = lean_ctor_get(v_toCold_6823_, 4);
v_openDecls_6826_ = lean_ctor_get(v_toCold_6823_, 5);
lean_inc(v_openDecls_6826_);
lean_inc(v_currNamespace_6825_);
v___x_6827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6827_, 0, v_currNamespace_6825_);
lean_ctor_set(v___x_6827_, 1, v_openDecls_6826_);
v___x_6828_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6828_, 0, v___x_6827_);
lean_ctor_set(v___x_6828_, 1, v___y_6822_);
lean_inc_ref(v___y_6816_);
lean_inc_ref(v___y_6818_);
v___x_6829_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_6829_, 0, v___y_6818_);
lean_ctor_set(v___x_6829_, 1, v___y_6820_);
lean_ctor_set(v___x_6829_, 2, v___y_6821_);
lean_ctor_set(v___x_6829_, 3, v___y_6816_);
lean_ctor_set(v___x_6829_, 4, v___x_6828_);
lean_ctor_set_uint8(v___x_6829_, sizeof(void*)*5, v___y_6819_);
lean_ctor_set_uint8(v___x_6829_, sizeof(void*)*5 + 1, v___y_6817_);
lean_ctor_set_uint8(v___x_6829_, sizeof(void*)*5 + 2, v_isSilent_6811_);
v___x_6830_ = lean_st_ref_take(v___y_6824_);
v_env_6831_ = lean_ctor_get(v___x_6830_, 0);
v_nextMacroScope_6832_ = lean_ctor_get(v___x_6830_, 1);
v_ngen_6833_ = lean_ctor_get(v___x_6830_, 2);
v_auxDeclNGen_6834_ = lean_ctor_get(v___x_6830_, 3);
v_traceState_6835_ = lean_ctor_get(v___x_6830_, 4);
v_cache_6836_ = lean_ctor_get(v___x_6830_, 5);
v_recordedDeps_6837_ = lean_ctor_get(v___x_6830_, 6);
v_messages_6838_ = lean_ctor_get(v___x_6830_, 7);
v_infoState_6839_ = lean_ctor_get(v___x_6830_, 8);
v_snapshotTasks_6840_ = lean_ctor_get(v___x_6830_, 9);
v_isSharedCheck_6851_ = !lean_is_exclusive(v___x_6830_);
if (v_isSharedCheck_6851_ == 0)
{
v___x_6842_ = v___x_6830_;
v_isShared_6843_ = v_isSharedCheck_6851_;
goto v_resetjp_6841_;
}
else
{
lean_inc(v_snapshotTasks_6840_);
lean_inc(v_infoState_6839_);
lean_inc(v_messages_6838_);
lean_inc(v_recordedDeps_6837_);
lean_inc(v_cache_6836_);
lean_inc(v_traceState_6835_);
lean_inc(v_auxDeclNGen_6834_);
lean_inc(v_ngen_6833_);
lean_inc(v_nextMacroScope_6832_);
lean_inc(v_env_6831_);
lean_dec(v___x_6830_);
v___x_6842_ = lean_box(0);
v_isShared_6843_ = v_isSharedCheck_6851_;
goto v_resetjp_6841_;
}
v_resetjp_6841_:
{
lean_object* v___x_6844_; lean_object* v___x_6845_; lean_object* v___x_6847_; 
v___x_6844_ = lean_box(0);
v___x_6845_ = l_Lean_MessageLog_add(v___x_6829_, v_messages_6838_);
if (v_isShared_6843_ == 0)
{
lean_ctor_set(v___x_6842_, 7, v___x_6845_);
v___x_6847_ = v___x_6842_;
goto v_reusejp_6846_;
}
else
{
lean_object* v_reuseFailAlloc_6850_; 
v_reuseFailAlloc_6850_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6850_, 0, v_env_6831_);
lean_ctor_set(v_reuseFailAlloc_6850_, 1, v_nextMacroScope_6832_);
lean_ctor_set(v_reuseFailAlloc_6850_, 2, v_ngen_6833_);
lean_ctor_set(v_reuseFailAlloc_6850_, 3, v_auxDeclNGen_6834_);
lean_ctor_set(v_reuseFailAlloc_6850_, 4, v_traceState_6835_);
lean_ctor_set(v_reuseFailAlloc_6850_, 5, v_cache_6836_);
lean_ctor_set(v_reuseFailAlloc_6850_, 6, v_recordedDeps_6837_);
lean_ctor_set(v_reuseFailAlloc_6850_, 7, v___x_6845_);
lean_ctor_set(v_reuseFailAlloc_6850_, 8, v_infoState_6839_);
lean_ctor_set(v_reuseFailAlloc_6850_, 9, v_snapshotTasks_6840_);
v___x_6847_ = v_reuseFailAlloc_6850_;
goto v_reusejp_6846_;
}
v_reusejp_6846_:
{
lean_object* v___x_6848_; lean_object* v___x_6849_; 
v___x_6848_ = lean_st_ref_put(v___y_6824_, v___x_6847_);
v___x_6849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6849_, 0, v___x_6844_);
return v___x_6849_;
}
}
}
v___jp_6852_:
{
lean_object* v_fileName_6861_; lean_object* v_fileMap_6862_; lean_object* v___x_6863_; lean_object* v___x_6864_; lean_object* v_a_6865_; lean_object* v___x_6867_; uint8_t v_isShared_6868_; uint8_t v_isSharedCheck_6878_; 
v_fileName_6861_ = lean_ctor_get(v___y_6856_, 0);
v_fileMap_6862_ = lean_ctor_get(v___y_6856_, 1);
v___x_6863_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_6809_);
v___x_6864_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5(v___x_6863_, v___y_6812_, v___y_6813_);
v_a_6865_ = lean_ctor_get(v___x_6864_, 0);
v_isSharedCheck_6878_ = !lean_is_exclusive(v___x_6864_);
if (v_isSharedCheck_6878_ == 0)
{
v___x_6867_ = v___x_6864_;
v_isShared_6868_ = v_isSharedCheck_6878_;
goto v_resetjp_6866_;
}
else
{
lean_inc(v_a_6865_);
lean_dec(v___x_6864_);
v___x_6867_ = lean_box(0);
v_isShared_6868_ = v_isSharedCheck_6878_;
goto v_resetjp_6866_;
}
v_resetjp_6866_:
{
lean_object* v___x_6869_; lean_object* v___x_6870_; lean_object* v___x_6871_; lean_object* v___x_6872_; 
lean_inc_ref_n(v_fileMap_6862_, 2);
v___x_6869_ = l_Lean_FileMap_toPosition(v_fileMap_6862_, v___y_6858_);
lean_dec(v___y_6858_);
v___x_6870_ = l_Lean_FileMap_toPosition(v_fileMap_6862_, v___y_6860_);
lean_dec(v___y_6860_);
v___x_6871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6871_, 0, v___x_6870_);
v___x_6872_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___closed__0));
if (v___y_6857_ == 0)
{
lean_del_object(v___x_6867_);
lean_dec_ref(v___y_6854_);
v___y_6816_ = v___x_6872_;
v___y_6817_ = v___y_6855_;
v___y_6818_ = v_fileName_6861_;
v___y_6819_ = v___y_6859_;
v___y_6820_ = v___x_6869_;
v___y_6821_ = v___x_6871_;
v___y_6822_ = v_a_6865_;
v_toCold_6823_ = v___y_6853_;
v___y_6824_ = v___y_6813_;
goto v___jp_6815_;
}
else
{
uint8_t v___x_6873_; 
lean_inc(v_a_6865_);
v___x_6873_ = l_Lean_MessageData_hasTag(v___y_6854_, v_a_6865_);
if (v___x_6873_ == 0)
{
lean_object* v___x_6874_; lean_object* v___x_6876_; 
lean_dec_ref_known(v___x_6871_, 1);
lean_dec_ref(v___x_6869_);
lean_dec(v_a_6865_);
v___x_6874_ = lean_box(0);
if (v_isShared_6868_ == 0)
{
lean_ctor_set(v___x_6867_, 0, v___x_6874_);
v___x_6876_ = v___x_6867_;
goto v_reusejp_6875_;
}
else
{
lean_object* v_reuseFailAlloc_6877_; 
v_reuseFailAlloc_6877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6877_, 0, v___x_6874_);
v___x_6876_ = v_reuseFailAlloc_6877_;
goto v_reusejp_6875_;
}
v_reusejp_6875_:
{
return v___x_6876_;
}
}
else
{
lean_del_object(v___x_6867_);
v___y_6816_ = v___x_6872_;
v___y_6817_ = v___y_6855_;
v___y_6818_ = v_fileName_6861_;
v___y_6819_ = v___y_6859_;
v___y_6820_ = v___x_6869_;
v___y_6821_ = v___x_6871_;
v___y_6822_ = v_a_6865_;
v_toCold_6823_ = v___y_6853_;
v___y_6824_ = v___y_6813_;
goto v___jp_6815_;
}
}
}
}
v___jp_6879_:
{
lean_object* v___x_6887_; 
v___x_6887_ = l_Lean_Syntax_getTailPos_x3f(v___y_6885_, v___y_6884_);
lean_dec(v___y_6885_);
if (lean_obj_tag(v___x_6887_) == 0)
{
lean_inc(v___y_6886_);
v___y_6853_ = v___y_6880_;
v___y_6854_ = v___y_6882_;
v___y_6855_ = v___y_6883_;
v___y_6856_ = v___y_6880_;
v___y_6857_ = v___y_6881_;
v___y_6858_ = v___y_6886_;
v___y_6859_ = v___y_6884_;
v___y_6860_ = v___y_6886_;
goto v___jp_6852_;
}
else
{
lean_object* v_val_6888_; 
v_val_6888_ = lean_ctor_get(v___x_6887_, 0);
lean_inc(v_val_6888_);
lean_dec_ref_known(v___x_6887_, 1);
v___y_6853_ = v___y_6880_;
v___y_6854_ = v___y_6882_;
v___y_6855_ = v___y_6883_;
v___y_6856_ = v___y_6880_;
v___y_6857_ = v___y_6881_;
v___y_6858_ = v___y_6886_;
v___y_6859_ = v___y_6884_;
v___y_6860_ = v_val_6888_;
goto v___jp_6852_;
}
}
v___jp_6889_:
{
lean_object* v_toCold_6892_; lean_object* v_ref_6893_; uint8_t v_suppressElabErrors_6894_; lean_object* v___x_6895_; lean_object* v___f_6896_; lean_object* v_ref_6897_; lean_object* v___x_6898_; 
v_toCold_6892_ = lean_ctor_get(v___y_6812_, 0);
v_ref_6893_ = lean_ctor_get(v___y_6812_, 2);
v_suppressElabErrors_6894_ = lean_ctor_get_uint8(v___y_6812_, sizeof(void*)*3 + 2);
v___x_6895_ = lean_box(v_suppressElabErrors_6894_);
v___f_6896_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___boxed), 2, 1);
lean_closure_set(v___f_6896_, 0, v___x_6895_);
v_ref_6897_ = l_Lean_replaceRef(v_ref_6808_, v_ref_6893_);
v___x_6898_ = l_Lean_Syntax_getPos_x3f(v_ref_6897_, v___y_6890_);
if (lean_obj_tag(v___x_6898_) == 0)
{
lean_object* v___x_6899_; 
v___x_6899_ = lean_unsigned_to_nat(0u);
v___y_6880_ = v_toCold_6892_;
v___y_6881_ = v_suppressElabErrors_6894_;
v___y_6882_ = v___f_6896_;
v___y_6883_ = v___y_6891_;
v___y_6884_ = v___y_6890_;
v___y_6885_ = v_ref_6897_;
v___y_6886_ = v___x_6899_;
goto v___jp_6879_;
}
else
{
lean_object* v_val_6900_; 
v_val_6900_ = lean_ctor_get(v___x_6898_, 0);
lean_inc(v_val_6900_);
lean_dec_ref_known(v___x_6898_, 1);
v___y_6880_ = v_toCold_6892_;
v___y_6881_ = v_suppressElabErrors_6894_;
v___y_6882_ = v___f_6896_;
v___y_6883_ = v___y_6891_;
v___y_6884_ = v___y_6890_;
v___y_6885_ = v_ref_6897_;
v___y_6886_ = v_val_6900_;
goto v___jp_6879_;
}
}
v___jp_6902_:
{
uint8_t v___x_6904_; uint8_t v___x_6905_; 
v___x_6904_ = 1;
v___x_6905_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6810_, v___x_6904_);
if (v___x_6905_ == 0)
{
v___y_6890_ = v___y_6903_;
v___y_6891_ = v_severity_6810_;
goto v___jp_6889_;
}
else
{
lean_object* v___x_6906_; lean_object* v___x_6907_; uint8_t v___x_6908_; 
v___x_6906_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_6812_);
v___x_6907_ = l_Lean_warningAsError;
v___x_6908_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7_spec__9(v___x_6906_, v___x_6907_);
lean_dec_ref(v___x_6906_);
if (v___x_6908_ == 0)
{
v___y_6890_ = v___y_6903_;
v___y_6891_ = v_severity_6810_;
goto v___jp_6889_;
}
else
{
v___y_6890_ = v___y_6903_;
v___y_6891_ = v___x_6901_;
goto v___jp_6889_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_ref_6913_, lean_object* v_msgData_6914_, lean_object* v_severity_6915_, lean_object* v_isSilent_6916_, lean_object* v___y_6917_, lean_object* v___y_6918_, lean_object* v___y_6919_){
_start:
{
uint8_t v_severity_boxed_6920_; uint8_t v_isSilent_boxed_6921_; lean_object* v_res_6922_; 
v_severity_boxed_6920_ = lean_unbox(v_severity_6915_);
v_isSilent_boxed_6921_ = lean_unbox(v_isSilent_6916_);
v_res_6922_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4(v_ref_6913_, v_msgData_6914_, v_severity_boxed_6920_, v_isSilent_boxed_6921_, v___y_6917_, v___y_6918_);
lean_dec(v___y_6918_);
lean_dec_ref(v___y_6917_);
lean_dec(v_ref_6913_);
return v_res_6922_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2(lean_object* v_msgData_6923_, uint8_t v_severity_6924_, uint8_t v_isSilent_6925_, lean_object* v___y_6926_, lean_object* v___y_6927_){
_start:
{
lean_object* v_ref_6929_; lean_object* v___x_6930_; 
v_ref_6929_ = lean_ctor_get(v___y_6926_, 2);
v___x_6930_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4(v_ref_6929_, v_msgData_6923_, v_severity_6924_, v_isSilent_6925_, v___y_6926_, v___y_6927_);
return v___x_6930_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_6931_, lean_object* v_severity_6932_, lean_object* v_isSilent_6933_, lean_object* v___y_6934_, lean_object* v___y_6935_, lean_object* v___y_6936_){
_start:
{
uint8_t v_severity_boxed_6937_; uint8_t v_isSilent_boxed_6938_; lean_object* v_res_6939_; 
v_severity_boxed_6937_ = lean_unbox(v_severity_6932_);
v_isSilent_boxed_6938_ = lean_unbox(v_isSilent_6933_);
v_res_6939_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2(v_msgData_6931_, v_severity_boxed_6937_, v_isSilent_boxed_6938_, v___y_6934_, v___y_6935_);
lean_dec(v___y_6935_);
lean_dec_ref(v___y_6934_);
return v_res_6939_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0(lean_object* v_msgData_6940_, lean_object* v___y_6941_, lean_object* v___y_6942_){
_start:
{
uint8_t v___x_6944_; uint8_t v___x_6945_; lean_object* v___x_6946_; 
v___x_6944_ = 2;
v___x_6945_ = 0;
v___x_6946_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2(v_msgData_6940_, v___x_6944_, v___x_6945_, v___y_6941_, v___y_6942_);
return v___x_6946_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0___boxed(lean_object* v_msgData_6947_, lean_object* v___y_6948_, lean_object* v___y_6949_, lean_object* v___y_6950_){
_start:
{
lean_object* v_res_6951_; 
v_res_6951_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0(v_msgData_6947_, v___y_6948_, v___y_6949_);
lean_dec(v___y_6949_);
lean_dec_ref(v___y_6948_);
return v_res_6951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0(lean_object* v_f_6952_, lean_object* v___y_6953_, lean_object* v___y_6954_){
_start:
{
lean_object* v_module_6956_; lean_object* v_const_6957_; lean_object* v_exception_6958_; lean_object* v___x_6959_; lean_object* v___x_6960_; lean_object* v___x_6961_; lean_object* v___x_6962_; lean_object* v___x_6963_; lean_object* v___x_6964_; lean_object* v___x_6965_; lean_object* v___x_6966_; lean_object* v___x_6967_; lean_object* v___x_6968_; lean_object* v___x_6969_; lean_object* v___x_6970_; 
v_module_6956_ = lean_ctor_get(v_f_6952_, 0);
lean_inc(v_module_6956_);
v_const_6957_ = lean_ctor_get(v_f_6952_, 1);
lean_inc(v_const_6957_);
v_exception_6958_ = lean_ctor_get(v_f_6952_, 2);
lean_inc_ref(v_exception_6958_);
lean_dec_ref(v_f_6952_);
v___x_6959_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1);
v___x_6960_ = l_Lean_MessageData_ofName(v_const_6957_);
v___x_6961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6961_, 0, v___x_6959_);
lean_ctor_set(v___x_6961_, 1, v___x_6960_);
v___x_6962_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3);
v___x_6963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6963_, 0, v___x_6961_);
lean_ctor_set(v___x_6963_, 1, v___x_6962_);
v___x_6964_ = l_Lean_MessageData_ofName(v_module_6956_);
v___x_6965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6965_, 0, v___x_6963_);
lean_ctor_set(v___x_6965_, 1, v___x_6964_);
v___x_6966_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5);
v___x_6967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6967_, 0, v___x_6965_);
lean_ctor_set(v___x_6967_, 1, v___x_6966_);
v___x_6968_ = l_Lean_Exception_toMessageData(v_exception_6958_);
v___x_6969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6969_, 0, v___x_6967_);
lean_ctor_set(v___x_6969_, 1, v___x_6968_);
v___x_6970_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0(v___x_6969_, v___y_6953_, v___y_6954_);
return v___x_6970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0___boxed(lean_object* v_f_6971_, lean_object* v___y_6972_, lean_object* v___y_6973_, lean_object* v___y_6974_){
_start:
{
lean_object* v_res_6975_; 
v_res_6975_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0(v_f_6971_, v___y_6972_, v___y_6973_);
lean_dec(v___y_6973_);
lean_dec_ref(v___y_6972_);
return v_res_6975_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2(lean_object* v_as_6976_, size_t v_i_6977_, size_t v_stop_6978_, lean_object* v_b_6979_, lean_object* v___y_6980_, lean_object* v___y_6981_){
_start:
{
uint8_t v___x_6983_; 
v___x_6983_ = lean_usize_dec_eq(v_i_6977_, v_stop_6978_);
if (v___x_6983_ == 0)
{
lean_object* v___x_6984_; lean_object* v___x_6985_; 
v___x_6984_ = lean_array_uget_borrowed(v_as_6976_, v_i_6977_);
lean_inc(v___x_6984_);
v___x_6985_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0(v___x_6984_, v___y_6980_, v___y_6981_);
if (lean_obj_tag(v___x_6985_) == 0)
{
lean_object* v_a_6986_; size_t v___x_6987_; size_t v___x_6988_; 
v_a_6986_ = lean_ctor_get(v___x_6985_, 0);
lean_inc(v_a_6986_);
lean_dec_ref_known(v___x_6985_, 1);
v___x_6987_ = ((size_t)1ULL);
v___x_6988_ = lean_usize_add(v_i_6977_, v___x_6987_);
v_i_6977_ = v___x_6988_;
v_b_6979_ = v_a_6986_;
goto _start;
}
else
{
return v___x_6985_;
}
}
else
{
lean_object* v___x_6990_; 
v___x_6990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6990_, 0, v_b_6979_);
return v___x_6990_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2___boxed(lean_object* v_as_6991_, lean_object* v_i_6992_, lean_object* v_stop_6993_, lean_object* v_b_6994_, lean_object* v___y_6995_, lean_object* v___y_6996_, lean_object* v___y_6997_){
_start:
{
size_t v_i_boxed_6998_; size_t v_stop_boxed_6999_; lean_object* v_res_7000_; 
v_i_boxed_6998_ = lean_unbox_usize(v_i_6992_);
lean_dec(v_i_6992_);
v_stop_boxed_6999_ = lean_unbox_usize(v_stop_6993_);
lean_dec(v_stop_6993_);
v_res_7000_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2(v_as_6991_, v_i_boxed_6998_, v_stop_boxed_6999_, v_b_6994_, v___y_6995_, v___y_6996_);
lean_dec(v___y_6996_);
lean_dec_ref(v___y_6995_);
lean_dec_ref(v_as_6991_);
return v_res_7000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(lean_object* v_entriesForConst_7001_, lean_object* v_a_7002_, lean_object* v_a_7003_){
_start:
{
lean_object* v___x_7005_; lean_object* v_env_7006_; lean_object* v___x_7007_; lean_object* v_a_7008_; lean_object* v___x_7010_; uint8_t v_isShared_7011_; uint8_t v_isSharedCheck_7035_; 
v___x_7005_ = lean_st_ref_get(v_a_7003_);
v_env_7006_ = lean_ctor_get(v___x_7005_, 0);
lean_inc_ref(v_env_7006_);
lean_dec(v___x_7005_);
v___x_7007_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(v_a_7003_);
v_a_7008_ = lean_ctor_get(v___x_7007_, 0);
v_isSharedCheck_7035_ = !lean_is_exclusive(v___x_7007_);
if (v_isSharedCheck_7035_ == 0)
{
v___x_7010_ = v___x_7007_;
v_isShared_7011_ = v_isSharedCheck_7035_;
goto v_resetjp_7009_;
}
else
{
lean_inc(v_a_7008_);
lean_dec(v___x_7007_);
v___x_7010_ = lean_box(0);
v_isShared_7011_ = v_isSharedCheck_7035_;
goto v_resetjp_7009_;
}
v_resetjp_7009_:
{
lean_object* v___x_7012_; lean_object* v___x_7013_; lean_object* v___x_7019_; lean_object* v___x_7020_; lean_object* v___x_7021_; uint8_t v___x_7022_; 
v___x_7012_ = l_Lean_Meta_LazyDiscrTree_ImportData_new();
lean_inc_ref(v_a_7002_);
v___x_7013_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(v_a_7002_, v_a_7008_, v_env_7006_, v___x_7012_, v_entriesForConst_7001_);
v___x_7019_ = lean_st_ref_get(v___x_7012_);
lean_dec(v___x_7012_);
v___x_7020_ = lean_unsigned_to_nat(0u);
v___x_7021_ = lean_array_get_size(v___x_7019_);
v___x_7022_ = lean_nat_dec_lt(v___x_7020_, v___x_7021_);
if (v___x_7022_ == 0)
{
lean_dec(v___x_7019_);
goto v___jp_7014_;
}
else
{
lean_object* v___x_7023_; size_t v___x_7024_; size_t v___x_7025_; lean_object* v___x_7026_; 
v___x_7023_ = lean_box(0);
v___x_7024_ = ((size_t)0ULL);
v___x_7025_ = lean_usize_of_nat(v___x_7021_);
v___x_7026_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2(v___x_7019_, v___x_7024_, v___x_7025_, v___x_7023_, v_a_7002_, v_a_7003_);
lean_dec(v___x_7019_);
if (lean_obj_tag(v___x_7026_) == 0)
{
lean_dec_ref_known(v___x_7026_, 1);
goto v___jp_7014_;
}
else
{
lean_object* v_a_7027_; lean_object* v___x_7029_; uint8_t v_isShared_7030_; uint8_t v_isSharedCheck_7034_; 
lean_dec_ref(v___x_7013_);
lean_del_object(v___x_7010_);
v_a_7027_ = lean_ctor_get(v___x_7026_, 0);
v_isSharedCheck_7034_ = !lean_is_exclusive(v___x_7026_);
if (v_isSharedCheck_7034_ == 0)
{
v___x_7029_ = v___x_7026_;
v_isShared_7030_ = v_isSharedCheck_7034_;
goto v_resetjp_7028_;
}
else
{
lean_inc(v_a_7027_);
lean_dec(v___x_7026_);
v___x_7029_ = lean_box(0);
v_isShared_7030_ = v_isSharedCheck_7034_;
goto v_resetjp_7028_;
}
v_resetjp_7028_:
{
lean_object* v___x_7032_; 
if (v_isShared_7030_ == 0)
{
v___x_7032_ = v___x_7029_;
goto v_reusejp_7031_;
}
else
{
lean_object* v_reuseFailAlloc_7033_; 
v_reuseFailAlloc_7033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7033_, 0, v_a_7027_);
v___x_7032_ = v_reuseFailAlloc_7033_;
goto v_reusejp_7031_;
}
v_reusejp_7031_:
{
return v___x_7032_;
}
}
}
}
v___jp_7014_:
{
lean_object* v___x_7015_; lean_object* v___x_7017_; 
v___x_7015_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v___x_7013_);
if (v_isShared_7011_ == 0)
{
lean_ctor_set(v___x_7010_, 0, v___x_7015_);
v___x_7017_ = v___x_7010_;
goto v_reusejp_7016_;
}
else
{
lean_object* v_reuseFailAlloc_7018_; 
v_reuseFailAlloc_7018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7018_, 0, v___x_7015_);
v___x_7017_ = v_reuseFailAlloc_7018_;
goto v_reusejp_7016_;
}
v_reusejp_7016_:
{
return v___x_7017_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg___boxed(lean_object* v_entriesForConst_7036_, lean_object* v_a_7037_, lean_object* v_a_7038_, lean_object* v_a_7039_){
_start:
{
lean_object* v_res_7040_; 
v_res_7040_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(v_entriesForConst_7036_, v_a_7037_, v_a_7038_);
lean_dec(v_a_7038_);
lean_dec_ref(v_a_7037_);
return v_res_7040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree(lean_object* v_00_u03b1_7041_, lean_object* v_entriesForConst_7042_, lean_object* v_a_7043_, lean_object* v_a_7044_){
_start:
{
lean_object* v___x_7046_; 
v___x_7046_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(v_entriesForConst_7042_, v_a_7043_, v_a_7044_);
return v___x_7046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___boxed(lean_object* v_00_u03b1_7047_, lean_object* v_entriesForConst_7048_, lean_object* v_a_7049_, lean_object* v_a_7050_, lean_object* v_a_7051_){
_start:
{
lean_object* v_res_7052_; 
v_res_7052_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree(v_00_u03b1_7047_, v_entriesForConst_7048_, v_a_7049_, v_a_7050_);
lean_dec(v_a_7050_);
lean_dec_ref(v_a_7049_);
return v_res_7052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0(lean_object* v_entriesForConst_7053_, lean_object* v_droppedEntriesRef_7054_, lean_object* v_droppedKeys_7055_, lean_object* v___y_7056_, lean_object* v___y_7057_, lean_object* v___y_7058_, lean_object* v___y_7059_){
_start:
{
lean_object* v_t_7062_; lean_object* v___x_7065_; 
v___x_7065_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(v_entriesForConst_7053_, v___y_7058_, v___y_7059_);
if (lean_obj_tag(v___x_7065_) == 0)
{
if (lean_obj_tag(v_droppedEntriesRef_7054_) == 1)
{
lean_object* v_a_7066_; lean_object* v_val_7067_; lean_object* v___x_7069_; uint8_t v_isShared_7070_; uint8_t v_isSharedCheck_7093_; 
v_a_7066_ = lean_ctor_get(v___x_7065_, 0);
lean_inc(v_a_7066_);
lean_dec_ref_known(v___x_7065_, 1);
v_val_7067_ = lean_ctor_get(v_droppedEntriesRef_7054_, 0);
v_isSharedCheck_7093_ = !lean_is_exclusive(v_droppedEntriesRef_7054_);
if (v_isSharedCheck_7093_ == 0)
{
v___x_7069_ = v_droppedEntriesRef_7054_;
v_isShared_7070_ = v_isSharedCheck_7093_;
goto v_resetjp_7068_;
}
else
{
lean_inc(v_val_7067_);
lean_dec(v_droppedEntriesRef_7054_);
v___x_7069_ = lean_box(0);
v_isShared_7070_ = v_isSharedCheck_7093_;
goto v_resetjp_7068_;
}
v_resetjp_7068_:
{
lean_object* v___x_7071_; 
v___x_7071_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_a_7066_, v_droppedKeys_7055_, v___y_7056_, v___y_7057_, v___y_7058_, v___y_7059_);
lean_dec(v_droppedKeys_7055_);
if (lean_obj_tag(v___x_7071_) == 0)
{
lean_object* v_a_7072_; lean_object* v_fst_7073_; lean_object* v_snd_7074_; lean_object* v___x_7075_; lean_object* v___y_7077_; 
v_a_7072_ = lean_ctor_get(v___x_7071_, 0);
lean_inc(v_a_7072_);
lean_dec_ref_known(v___x_7071_, 1);
v_fst_7073_ = lean_ctor_get(v_a_7072_, 0);
lean_inc(v_fst_7073_);
v_snd_7074_ = lean_ctor_get(v_a_7072_, 1);
lean_inc(v_snd_7074_);
lean_dec(v_a_7072_);
v___x_7075_ = lean_st_ref_get(v_val_7067_);
if (lean_obj_tag(v___x_7075_) == 0)
{
lean_object* v___x_7083_; 
v___x_7083_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___y_7077_ = v___x_7083_;
goto v___jp_7076_;
}
else
{
lean_object* v_val_7084_; 
v_val_7084_ = lean_ctor_get(v___x_7075_, 0);
lean_inc(v_val_7084_);
lean_dec_ref_known(v___x_7075_, 1);
v___y_7077_ = v_val_7084_;
goto v___jp_7076_;
}
v___jp_7076_:
{
lean_object* v___x_7078_; lean_object* v___x_7080_; 
v___x_7078_ = l_Array_append___redArg(v___y_7077_, v_fst_7073_);
lean_dec(v_fst_7073_);
if (v_isShared_7070_ == 0)
{
lean_ctor_set(v___x_7069_, 0, v___x_7078_);
v___x_7080_ = v___x_7069_;
goto v_reusejp_7079_;
}
else
{
lean_object* v_reuseFailAlloc_7082_; 
v_reuseFailAlloc_7082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7082_, 0, v___x_7078_);
v___x_7080_ = v_reuseFailAlloc_7082_;
goto v_reusejp_7079_;
}
v_reusejp_7079_:
{
lean_object* v___x_7081_; 
v___x_7081_ = lean_st_ref_swap(v_val_7067_, v___x_7080_);
lean_dec(v_val_7067_);
lean_dec(v___x_7081_);
v_t_7062_ = v_snd_7074_;
goto v___jp_7061_;
}
}
}
else
{
lean_object* v_a_7085_; lean_object* v___x_7087_; uint8_t v_isShared_7088_; uint8_t v_isSharedCheck_7092_; 
lean_del_object(v___x_7069_);
lean_dec(v_val_7067_);
v_a_7085_ = lean_ctor_get(v___x_7071_, 0);
v_isSharedCheck_7092_ = !lean_is_exclusive(v___x_7071_);
if (v_isSharedCheck_7092_ == 0)
{
v___x_7087_ = v___x_7071_;
v_isShared_7088_ = v_isSharedCheck_7092_;
goto v_resetjp_7086_;
}
else
{
lean_inc(v_a_7085_);
lean_dec(v___x_7071_);
v___x_7087_ = lean_box(0);
v_isShared_7088_ = v_isSharedCheck_7092_;
goto v_resetjp_7086_;
}
v_resetjp_7086_:
{
lean_object* v___x_7090_; 
if (v_isShared_7088_ == 0)
{
v___x_7090_ = v___x_7087_;
goto v_reusejp_7089_;
}
else
{
lean_object* v_reuseFailAlloc_7091_; 
v_reuseFailAlloc_7091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7091_, 0, v_a_7085_);
v___x_7090_ = v_reuseFailAlloc_7091_;
goto v_reusejp_7089_;
}
v_reusejp_7089_:
{
return v___x_7090_;
}
}
}
}
}
else
{
lean_object* v_a_7094_; lean_object* v___x_7095_; 
lean_dec(v_droppedEntriesRef_7054_);
v_a_7094_ = lean_ctor_get(v___x_7065_, 0);
lean_inc(v_a_7094_);
lean_dec_ref_known(v___x_7065_, 1);
v___x_7095_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_a_7094_, v_droppedKeys_7055_, v___y_7056_, v___y_7057_, v___y_7058_, v___y_7059_);
if (lean_obj_tag(v___x_7095_) == 0)
{
lean_object* v_a_7096_; 
v_a_7096_ = lean_ctor_get(v___x_7095_, 0);
lean_inc(v_a_7096_);
lean_dec_ref_known(v___x_7095_, 1);
v_t_7062_ = v_a_7096_;
goto v___jp_7061_;
}
else
{
lean_object* v_a_7097_; lean_object* v___x_7099_; uint8_t v_isShared_7100_; uint8_t v_isSharedCheck_7104_; 
v_a_7097_ = lean_ctor_get(v___x_7095_, 0);
v_isSharedCheck_7104_ = !lean_is_exclusive(v___x_7095_);
if (v_isSharedCheck_7104_ == 0)
{
v___x_7099_ = v___x_7095_;
v_isShared_7100_ = v_isSharedCheck_7104_;
goto v_resetjp_7098_;
}
else
{
lean_inc(v_a_7097_);
lean_dec(v___x_7095_);
v___x_7099_ = lean_box(0);
v_isShared_7100_ = v_isSharedCheck_7104_;
goto v_resetjp_7098_;
}
v_resetjp_7098_:
{
lean_object* v___x_7102_; 
if (v_isShared_7100_ == 0)
{
v___x_7102_ = v___x_7099_;
goto v_reusejp_7101_;
}
else
{
lean_object* v_reuseFailAlloc_7103_; 
v_reuseFailAlloc_7103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7103_, 0, v_a_7097_);
v___x_7102_ = v_reuseFailAlloc_7103_;
goto v_reusejp_7101_;
}
v_reusejp_7101_:
{
return v___x_7102_;
}
}
}
}
}
else
{
lean_object* v_a_7105_; lean_object* v___x_7107_; uint8_t v_isShared_7108_; uint8_t v_isSharedCheck_7112_; 
lean_dec(v_droppedKeys_7055_);
lean_dec(v_droppedEntriesRef_7054_);
v_a_7105_ = lean_ctor_get(v___x_7065_, 0);
v_isSharedCheck_7112_ = !lean_is_exclusive(v___x_7065_);
if (v_isSharedCheck_7112_ == 0)
{
v___x_7107_ = v___x_7065_;
v_isShared_7108_ = v_isSharedCheck_7112_;
goto v_resetjp_7106_;
}
else
{
lean_inc(v_a_7105_);
lean_dec(v___x_7065_);
v___x_7107_ = lean_box(0);
v_isShared_7108_ = v_isSharedCheck_7112_;
goto v_resetjp_7106_;
}
v_resetjp_7106_:
{
lean_object* v___x_7110_; 
if (v_isShared_7108_ == 0)
{
v___x_7110_ = v___x_7107_;
goto v_reusejp_7109_;
}
else
{
lean_object* v_reuseFailAlloc_7111_; 
v_reuseFailAlloc_7111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7111_, 0, v_a_7105_);
v___x_7110_ = v_reuseFailAlloc_7111_;
goto v_reusejp_7109_;
}
v_reusejp_7109_:
{
return v___x_7110_;
}
}
}
v___jp_7061_:
{
lean_object* v___x_7063_; lean_object* v___x_7064_; 
v___x_7063_ = lean_st_mk_ref(v_t_7062_);
v___x_7064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7064_, 0, v___x_7063_);
return v___x_7064_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0___boxed(lean_object* v_entriesForConst_7113_, lean_object* v_droppedEntriesRef_7114_, lean_object* v_droppedKeys_7115_, lean_object* v___y_7116_, lean_object* v___y_7117_, lean_object* v___y_7118_, lean_object* v___y_7119_, lean_object* v___y_7120_){
_start:
{
lean_object* v_res_7121_; 
v_res_7121_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0(v_entriesForConst_7113_, v_droppedEntriesRef_7114_, v_droppedKeys_7115_, v___y_7116_, v___y_7117_, v___y_7118_, v___y_7119_);
lean_dec(v___y_7119_);
lean_dec_ref(v___y_7118_);
lean_dec(v___y_7117_);
lean_dec_ref(v___y_7116_);
return v_res_7121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(lean_object* v_entriesForConst_7123_, lean_object* v_droppedKeys_7124_, lean_object* v_droppedEntriesRef_7125_, lean_object* v_a_7126_, lean_object* v_a_7127_, lean_object* v_a_7128_, lean_object* v_a_7129_){
_start:
{
lean_object* v___f_7131_; lean_object* v___x_7132_; lean_object* v___x_7133_; lean_object* v___x_7134_; lean_object* v___x_7135_; 
v___f_7131_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_7131_, 0, v_entriesForConst_7123_);
lean_closure_set(v___f_7131_, 1, v_droppedEntriesRef_7125_);
lean_closure_set(v___f_7131_, 2, v_droppedKeys_7124_);
v___x_7132_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_7128_);
v___x_7133_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___closed__0));
v___x_7134_ = lean_box(0);
v___x_7135_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v___x_7133_, v___x_7132_, v___f_7131_, v___x_7134_, v_a_7126_, v_a_7127_, v_a_7128_, v_a_7129_);
lean_dec_ref(v___x_7132_);
return v___x_7135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___boxed(lean_object* v_entriesForConst_7136_, lean_object* v_droppedKeys_7137_, lean_object* v_droppedEntriesRef_7138_, lean_object* v_a_7139_, lean_object* v_a_7140_, lean_object* v_a_7141_, lean_object* v_a_7142_, lean_object* v_a_7143_){
_start:
{
lean_object* v_res_7144_; 
v_res_7144_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v_entriesForConst_7136_, v_droppedKeys_7137_, v_droppedEntriesRef_7138_, v_a_7139_, v_a_7140_, v_a_7141_, v_a_7142_);
lean_dec(v_a_7142_);
lean_dec_ref(v_a_7141_);
lean_dec(v_a_7140_);
lean_dec_ref(v_a_7139_);
return v_res_7144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef(lean_object* v_00_u03b1_7145_, lean_object* v_entriesForConst_7146_, lean_object* v_droppedKeys_7147_, lean_object* v_droppedEntriesRef_7148_, lean_object* v_a_7149_, lean_object* v_a_7150_, lean_object* v_a_7151_, lean_object* v_a_7152_){
_start:
{
lean_object* v___x_7154_; 
v___x_7154_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v_entriesForConst_7146_, v_droppedKeys_7147_, v_droppedEntriesRef_7148_, v_a_7149_, v_a_7150_, v_a_7151_, v_a_7152_);
return v___x_7154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___boxed(lean_object* v_00_u03b1_7155_, lean_object* v_entriesForConst_7156_, lean_object* v_droppedKeys_7157_, lean_object* v_droppedEntriesRef_7158_, lean_object* v_a_7159_, lean_object* v_a_7160_, lean_object* v_a_7161_, lean_object* v_a_7162_, lean_object* v_a_7163_){
_start:
{
lean_object* v_res_7164_; 
v_res_7164_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef(v_00_u03b1_7155_, v_entriesForConst_7156_, v_droppedKeys_7157_, v_droppedEntriesRef_7158_, v_a_7159_, v_a_7160_, v_a_7161_, v_a_7162_);
lean_dec(v_a_7162_);
lean_dec_ref(v_a_7161_);
lean_dec(v_a_7160_);
lean_dec_ref(v_a_7159_);
return v_res_7164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0(lean_object* v_moduleRef_7165_, lean_object* v_ty_7166_, lean_object* v___y_7167_, lean_object* v___y_7168_, lean_object* v___y_7169_, lean_object* v___y_7170_){
_start:
{
lean_object* v___x_7172_; lean_object* v___x_7173_; 
v___x_7172_ = lean_st_ref_get(v_moduleRef_7165_);
v___x_7173_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v___x_7172_, v_ty_7166_, v___y_7167_, v___y_7168_, v___y_7169_, v___y_7170_);
if (lean_obj_tag(v___x_7173_) == 0)
{
lean_object* v_a_7174_; lean_object* v___x_7176_; uint8_t v_isShared_7177_; uint8_t v_isSharedCheck_7184_; 
v_a_7174_ = lean_ctor_get(v___x_7173_, 0);
v_isSharedCheck_7184_ = !lean_is_exclusive(v___x_7173_);
if (v_isSharedCheck_7184_ == 0)
{
v___x_7176_ = v___x_7173_;
v_isShared_7177_ = v_isSharedCheck_7184_;
goto v_resetjp_7175_;
}
else
{
lean_inc(v_a_7174_);
lean_dec(v___x_7173_);
v___x_7176_ = lean_box(0);
v_isShared_7177_ = v_isSharedCheck_7184_;
goto v_resetjp_7175_;
}
v_resetjp_7175_:
{
lean_object* v_fst_7178_; lean_object* v_snd_7179_; lean_object* v___x_7180_; lean_object* v___x_7182_; 
v_fst_7178_ = lean_ctor_get(v_a_7174_, 0);
lean_inc(v_fst_7178_);
v_snd_7179_ = lean_ctor_get(v_a_7174_, 1);
lean_inc(v_snd_7179_);
lean_dec(v_a_7174_);
v___x_7180_ = lean_st_ref_swap(v_moduleRef_7165_, v_snd_7179_);
lean_dec(v___x_7180_);
if (v_isShared_7177_ == 0)
{
lean_ctor_set(v___x_7176_, 0, v_fst_7178_);
v___x_7182_ = v___x_7176_;
goto v_reusejp_7181_;
}
else
{
lean_object* v_reuseFailAlloc_7183_; 
v_reuseFailAlloc_7183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7183_, 0, v_fst_7178_);
v___x_7182_ = v_reuseFailAlloc_7183_;
goto v_reusejp_7181_;
}
v_reusejp_7181_:
{
return v___x_7182_;
}
}
}
else
{
lean_object* v_a_7185_; lean_object* v___x_7187_; uint8_t v_isShared_7188_; uint8_t v_isSharedCheck_7192_; 
v_a_7185_ = lean_ctor_get(v___x_7173_, 0);
v_isSharedCheck_7192_ = !lean_is_exclusive(v___x_7173_);
if (v_isSharedCheck_7192_ == 0)
{
v___x_7187_ = v___x_7173_;
v_isShared_7188_ = v_isSharedCheck_7192_;
goto v_resetjp_7186_;
}
else
{
lean_inc(v_a_7185_);
lean_dec(v___x_7173_);
v___x_7187_ = lean_box(0);
v_isShared_7188_ = v_isSharedCheck_7192_;
goto v_resetjp_7186_;
}
v_resetjp_7186_:
{
lean_object* v___x_7190_; 
if (v_isShared_7188_ == 0)
{
v___x_7190_ = v___x_7187_;
goto v_reusejp_7189_;
}
else
{
lean_object* v_reuseFailAlloc_7191_; 
v_reuseFailAlloc_7191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7191_, 0, v_a_7185_);
v___x_7190_ = v_reuseFailAlloc_7191_;
goto v_reusejp_7189_;
}
v_reusejp_7189_:
{
return v___x_7190_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0___boxed(lean_object* v_moduleRef_7193_, lean_object* v_ty_7194_, lean_object* v___y_7195_, lean_object* v___y_7196_, lean_object* v___y_7197_, lean_object* v___y_7198_, lean_object* v___y_7199_){
_start:
{
lean_object* v_res_7200_; 
v_res_7200_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0(v_moduleRef_7193_, v_ty_7194_, v___y_7195_, v___y_7196_, v___y_7197_, v___y_7198_);
lean_dec(v___y_7198_);
lean_dec_ref(v___y_7197_);
lean_dec(v___y_7196_);
lean_dec_ref(v___y_7195_);
lean_dec(v_moduleRef_7193_);
return v_res_7200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(lean_object* v_moduleRef_7202_, lean_object* v_ty_7203_, lean_object* v_a_7204_, lean_object* v_a_7205_, lean_object* v_a_7206_, lean_object* v_a_7207_){
_start:
{
lean_object* v___f_7209_; lean_object* v___x_7210_; lean_object* v___x_7211_; lean_object* v___x_7212_; lean_object* v___x_7213_; 
v___f_7209_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_7209_, 0, v_moduleRef_7202_);
lean_closure_set(v___f_7209_, 1, v_ty_7203_);
v___x_7210_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_7206_);
v___x_7211_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___closed__0));
v___x_7212_ = lean_box(0);
v___x_7213_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v___x_7211_, v___x_7210_, v___f_7209_, v___x_7212_, v_a_7204_, v_a_7205_, v_a_7206_, v_a_7207_);
lean_dec_ref(v___x_7210_);
return v___x_7213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___boxed(lean_object* v_moduleRef_7214_, lean_object* v_ty_7215_, lean_object* v_a_7216_, lean_object* v_a_7217_, lean_object* v_a_7218_, lean_object* v_a_7219_, lean_object* v_a_7220_){
_start:
{
lean_object* v_res_7221_; 
v_res_7221_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(v_moduleRef_7214_, v_ty_7215_, v_a_7216_, v_a_7217_, v_a_7218_, v_a_7219_);
lean_dec(v_a_7219_);
lean_dec_ref(v_a_7218_);
lean_dec(v_a_7217_);
lean_dec_ref(v_a_7216_);
return v_res_7221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches(lean_object* v_00_u03b1_7222_, lean_object* v_moduleRef_7223_, lean_object* v_ty_7224_, lean_object* v_a_7225_, lean_object* v_a_7226_, lean_object* v_a_7227_, lean_object* v_a_7228_){
_start:
{
lean_object* v___x_7230_; 
v___x_7230_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(v_moduleRef_7223_, v_ty_7224_, v_a_7225_, v_a_7226_, v_a_7227_, v_a_7228_);
return v___x_7230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___boxed(lean_object* v_00_u03b1_7231_, lean_object* v_moduleRef_7232_, lean_object* v_ty_7233_, lean_object* v_a_7234_, lean_object* v_a_7235_, lean_object* v_a_7236_, lean_object* v_a_7237_, lean_object* v_a_7238_){
_start:
{
lean_object* v_res_7239_; 
v_res_7239_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches(v_00_u03b1_7231_, v_moduleRef_7232_, v_ty_7233_, v_a_7234_, v_a_7235_, v_a_7236_, v_a_7237_);
lean_dec(v_a_7237_);
lean_dec_ref(v_a_7236_);
lean_dec(v_a_7235_);
lean_dec_ref(v_a_7234_);
return v_res_7239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(lean_object* v_adjustResult_7240_, lean_object* v_j_7241_, size_t v_sz_7242_, size_t v_i_7243_, lean_object* v_bs_7244_){
_start:
{
uint8_t v___x_7245_; 
v___x_7245_ = lean_usize_dec_lt(v_i_7243_, v_sz_7242_);
if (v___x_7245_ == 0)
{
lean_dec(v_j_7241_);
lean_dec(v_adjustResult_7240_);
return v_bs_7244_;
}
else
{
lean_object* v_v_7246_; lean_object* v___x_7247_; lean_object* v_bs_x27_7248_; lean_object* v___x_7249_; size_t v___x_7250_; size_t v___x_7251_; lean_object* v___x_7252_; 
v_v_7246_ = lean_array_uget(v_bs_7244_, v_i_7243_);
v___x_7247_ = lean_unsigned_to_nat(0u);
v_bs_x27_7248_ = lean_array_uset(v_bs_7244_, v_i_7243_, v___x_7247_);
lean_inc(v_adjustResult_7240_);
lean_inc(v_j_7241_);
v___x_7249_ = lean_apply_2(v_adjustResult_7240_, v_j_7241_, v_v_7246_);
v___x_7250_ = ((size_t)1ULL);
v___x_7251_ = lean_usize_add(v_i_7243_, v___x_7250_);
v___x_7252_ = lean_array_uset(v_bs_x27_7248_, v_i_7243_, v___x_7249_);
v_i_7243_ = v___x_7251_;
v_bs_7244_ = v___x_7252_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg___boxed(lean_object* v_adjustResult_7254_, lean_object* v_j_7255_, lean_object* v_sz_7256_, lean_object* v_i_7257_, lean_object* v_bs_7258_){
_start:
{
size_t v_sz_boxed_7259_; size_t v_i_boxed_7260_; lean_object* v_res_7261_; 
v_sz_boxed_7259_ = lean_unbox_usize(v_sz_7256_);
lean_dec(v_sz_7256_);
v_i_boxed_7260_ = lean_unbox_usize(v_i_7257_);
lean_dec(v_i_7257_);
v_res_7261_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(v_adjustResult_7254_, v_j_7255_, v_sz_boxed_7259_, v_i_boxed_7260_, v_bs_7258_);
return v_res_7261_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(lean_object* v_adjustResult_7262_, lean_object* v_j_7263_, lean_object* v_as_7264_, size_t v_i_7265_, size_t v_stop_7266_, lean_object* v_b_7267_){
_start:
{
uint8_t v___x_7268_; 
v___x_7268_ = lean_usize_dec_eq(v_i_7265_, v_stop_7266_);
if (v___x_7268_ == 0)
{
lean_object* v___x_7269_; size_t v_sz_7270_; size_t v___x_7271_; lean_object* v___x_7272_; lean_object* v___x_7273_; size_t v___x_7274_; size_t v___x_7275_; 
v___x_7269_ = lean_array_uget_borrowed(v_as_7264_, v_i_7265_);
v_sz_7270_ = lean_array_size(v___x_7269_);
v___x_7271_ = ((size_t)0ULL);
lean_inc(v___x_7269_);
lean_inc(v_j_7263_);
lean_inc(v_adjustResult_7262_);
v___x_7272_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(v_adjustResult_7262_, v_j_7263_, v_sz_7270_, v___x_7271_, v___x_7269_);
v___x_7273_ = l_Array_append___redArg(v_b_7267_, v___x_7272_);
lean_dec_ref(v___x_7272_);
v___x_7274_ = ((size_t)1ULL);
v___x_7275_ = lean_usize_add(v_i_7265_, v___x_7274_);
v_i_7265_ = v___x_7275_;
v_b_7267_ = v___x_7273_;
goto _start;
}
else
{
lean_dec(v_j_7263_);
lean_dec(v_adjustResult_7262_);
return v_b_7267_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg___boxed(lean_object* v_adjustResult_7277_, lean_object* v_j_7278_, lean_object* v_as_7279_, lean_object* v_i_7280_, lean_object* v_stop_7281_, lean_object* v_b_7282_){
_start:
{
size_t v_i_boxed_7283_; size_t v_stop_boxed_7284_; lean_object* v_res_7285_; 
v_i_boxed_7283_ = lean_unbox_usize(v_i_7280_);
lean_dec(v_i_7280_);
v_stop_boxed_7284_ = lean_unbox_usize(v_stop_7281_);
lean_dec(v_stop_7281_);
v_res_7285_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7277_, v_j_7278_, v_as_7279_, v_i_boxed_7283_, v_stop_boxed_7284_, v_b_7282_);
lean_dec_ref(v_as_7279_);
return v_res_7285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(lean_object* v_n_7286_, lean_object* v_aa_7287_, lean_object* v_adjustResult_7288_, lean_object* v_n_7289_, lean_object* v_j_7290_, lean_object* v_a_7291_){
_start:
{
lean_object* v_zero_7292_; uint8_t v_isZero_7293_; 
v_zero_7292_ = lean_unsigned_to_nat(0u);
v_isZero_7293_ = lean_nat_dec_eq(v_j_7290_, v_zero_7292_);
if (v_isZero_7293_ == 1)
{
lean_dec(v_j_7290_);
lean_dec(v_adjustResult_7288_);
return v_a_7291_;
}
else
{
lean_object* v_one_7294_; lean_object* v_n_7295_; lean_object* v___x_7296_; lean_object* v___x_7297_; lean_object* v_j_7298_; lean_object* v_b_7299_; lean_object* v___x_7300_; uint8_t v___x_7301_; 
v_one_7294_ = lean_unsigned_to_nat(1u);
v_n_7295_ = lean_nat_sub(v_j_7290_, v_one_7294_);
v___x_7296_ = lean_nat_sub(v_n_7289_, v_j_7290_);
lean_dec(v_j_7290_);
v___x_7297_ = lean_nat_sub(v_n_7286_, v_one_7294_);
v_j_7298_ = lean_nat_sub(v___x_7297_, v___x_7296_);
lean_dec(v___x_7296_);
lean_dec(v___x_7297_);
v_b_7299_ = lean_array_fget_borrowed(v_aa_7287_, v_j_7298_);
v___x_7300_ = lean_array_get_size(v_b_7299_);
v___x_7301_ = lean_nat_dec_lt(v_zero_7292_, v___x_7300_);
if (v___x_7301_ == 0)
{
lean_dec(v_j_7298_);
v_j_7290_ = v_n_7295_;
goto _start;
}
else
{
size_t v___x_7303_; size_t v___x_7304_; lean_object* v___x_7305_; 
v___x_7303_ = ((size_t)0ULL);
v___x_7304_ = lean_usize_of_nat(v___x_7300_);
lean_inc(v_adjustResult_7288_);
v___x_7305_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7288_, v_j_7298_, v_b_7299_, v___x_7303_, v___x_7304_, v_a_7291_);
v_j_7290_ = v_n_7295_;
v_a_7291_ = v___x_7305_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_n_7307_, lean_object* v_aa_7308_, lean_object* v_adjustResult_7309_, lean_object* v_n_7310_, lean_object* v_j_7311_, lean_object* v_a_7312_){
_start:
{
lean_object* v_res_7313_; 
v_res_7313_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7307_, v_aa_7308_, v_adjustResult_7309_, v_n_7310_, v_j_7311_, v_a_7312_);
lean_dec(v_n_7310_);
lean_dec_ref(v_aa_7308_);
lean_dec(v_n_7307_);
return v_res_7313_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(lean_object* v_n_7314_, lean_object* v_adjustResult_7315_, lean_object* v_aa_7316_, lean_object* v_n_7317_, lean_object* v_j_7318_, lean_object* v_a_7319_){
_start:
{
lean_object* v_zero_7320_; uint8_t v_isZero_7321_; 
v_zero_7320_ = lean_unsigned_to_nat(0u);
v_isZero_7321_ = lean_nat_dec_eq(v_j_7318_, v_zero_7320_);
if (v_isZero_7321_ == 1)
{
lean_dec(v_adjustResult_7315_);
return v_a_7319_;
}
else
{
lean_object* v_one_7322_; lean_object* v_n_7323_; lean_object* v___x_7324_; lean_object* v___x_7325_; lean_object* v_j_7326_; lean_object* v_b_7327_; lean_object* v___x_7328_; uint8_t v___x_7329_; 
v_one_7322_ = lean_unsigned_to_nat(1u);
v_n_7323_ = lean_nat_sub(v_j_7318_, v_one_7322_);
v___x_7324_ = lean_nat_sub(v_n_7317_, v_j_7318_);
v___x_7325_ = lean_nat_sub(v_n_7314_, v_one_7322_);
v_j_7326_ = lean_nat_sub(v___x_7325_, v___x_7324_);
lean_dec(v___x_7324_);
lean_dec(v___x_7325_);
v_b_7327_ = lean_array_fget_borrowed(v_aa_7316_, v_j_7326_);
v___x_7328_ = lean_array_get_size(v_b_7327_);
v___x_7329_ = lean_nat_dec_lt(v_zero_7320_, v___x_7328_);
if (v___x_7329_ == 0)
{
lean_object* v___x_7330_; 
lean_dec(v_j_7326_);
v___x_7330_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7314_, v_aa_7316_, v_adjustResult_7315_, v_n_7317_, v_n_7323_, v_a_7319_);
return v___x_7330_;
}
else
{
size_t v___x_7331_; size_t v___x_7332_; lean_object* v___x_7333_; lean_object* v___x_7334_; 
v___x_7331_ = ((size_t)0ULL);
v___x_7332_ = lean_usize_of_nat(v___x_7328_);
lean_inc(v_adjustResult_7315_);
v___x_7333_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7315_, v_j_7326_, v_b_7327_, v___x_7331_, v___x_7332_, v_a_7319_);
v___x_7334_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7314_, v_aa_7316_, v_adjustResult_7315_, v_n_7317_, v_n_7323_, v___x_7333_);
return v___x_7334_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg___boxed(lean_object* v_n_7335_, lean_object* v_adjustResult_7336_, lean_object* v_aa_7337_, lean_object* v_n_7338_, lean_object* v_j_7339_, lean_object* v_a_7340_){
_start:
{
lean_object* v_res_7341_; 
v_res_7341_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(v_n_7335_, v_adjustResult_7336_, v_aa_7337_, v_n_7338_, v_j_7339_, v_a_7340_);
lean_dec(v_j_7339_);
lean_dec(v_n_7338_);
lean_dec_ref(v_aa_7337_);
lean_dec(v_n_7335_);
return v_res_7341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(lean_object* v_adjustResult_7342_, lean_object* v_mr_7343_, lean_object* v_a_7344_){
_start:
{
lean_object* v_n_7345_; lean_object* v___x_7346_; 
v_n_7345_ = lean_array_get_size(v_mr_7343_);
v___x_7346_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(v_n_7345_, v_adjustResult_7342_, v_mr_7343_, v_n_7345_, v_n_7345_, v_a_7344_);
return v___x_7346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg___boxed(lean_object* v_adjustResult_7347_, lean_object* v_mr_7348_, lean_object* v_a_7349_){
_start:
{
lean_object* v_res_7350_; 
v_res_7350_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7347_, v_mr_7348_, v_a_7349_);
lean_dec_ref(v_mr_7348_);
return v_res_7350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(lean_object* v_moduleTreeRef_7351_, lean_object* v_ref_7352_, lean_object* v_addEntry_7353_, lean_object* v_droppedKeys_7354_, lean_object* v_constantsPerTask_7355_, lean_object* v_droppedEntriesRef_7356_, lean_object* v_adjustResult_7357_, lean_object* v_ty_7358_, lean_object* v_a_7359_, lean_object* v_a_7360_, lean_object* v_a_7361_, lean_object* v_a_7362_){
_start:
{
lean_object* v___x_7364_; 
lean_inc_ref(v_ty_7358_);
v___x_7364_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(v_moduleTreeRef_7351_, v_ty_7358_, v_a_7359_, v_a_7360_, v_a_7361_, v_a_7362_);
if (lean_obj_tag(v___x_7364_) == 0)
{
lean_object* v_a_7365_; lean_object* v___x_7366_; 
v_a_7365_ = lean_ctor_get(v___x_7364_, 0);
lean_inc(v_a_7365_);
lean_dec_ref_known(v___x_7364_, 1);
v___x_7366_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(v_ref_7352_, v_addEntry_7353_, v_droppedKeys_7354_, v_constantsPerTask_7355_, v_droppedEntriesRef_7356_, v_ty_7358_, v_a_7359_, v_a_7360_, v_a_7361_, v_a_7362_);
if (lean_obj_tag(v___x_7366_) == 0)
{
lean_object* v_a_7367_; lean_object* v___x_7369_; uint8_t v_isShared_7370_; uint8_t v_isSharedCheck_7380_; 
v_a_7367_ = lean_ctor_get(v___x_7366_, 0);
v_isSharedCheck_7380_ = !lean_is_exclusive(v___x_7366_);
if (v_isSharedCheck_7380_ == 0)
{
v___x_7369_ = v___x_7366_;
v_isShared_7370_ = v_isSharedCheck_7380_;
goto v_resetjp_7368_;
}
else
{
lean_inc(v_a_7367_);
lean_dec(v___x_7366_);
v___x_7369_ = lean_box(0);
v_isShared_7370_ = v_isSharedCheck_7380_;
goto v_resetjp_7368_;
}
v_resetjp_7368_:
{
lean_object* v___x_7371_; lean_object* v___x_7372_; lean_object* v___x_7373_; lean_object* v___x_7374_; lean_object* v___x_7375_; lean_object* v___x_7376_; lean_object* v___x_7378_; 
v___x_7371_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_a_7365_);
v___x_7372_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_a_7367_);
v___x_7373_ = lean_nat_add(v___x_7371_, v___x_7372_);
lean_dec(v___x_7372_);
lean_dec(v___x_7371_);
v___x_7374_ = lean_mk_empty_array_with_capacity(v___x_7373_);
lean_dec(v___x_7373_);
lean_inc(v_adjustResult_7357_);
v___x_7375_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7357_, v_a_7365_, v___x_7374_);
lean_dec(v_a_7365_);
v___x_7376_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7357_, v_a_7367_, v___x_7375_);
lean_dec(v_a_7367_);
if (v_isShared_7370_ == 0)
{
lean_ctor_set(v___x_7369_, 0, v___x_7376_);
v___x_7378_ = v___x_7369_;
goto v_reusejp_7377_;
}
else
{
lean_object* v_reuseFailAlloc_7379_; 
v_reuseFailAlloc_7379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7379_, 0, v___x_7376_);
v___x_7378_ = v_reuseFailAlloc_7379_;
goto v_reusejp_7377_;
}
v_reusejp_7377_:
{
return v___x_7378_;
}
}
}
else
{
lean_object* v_a_7381_; lean_object* v___x_7383_; uint8_t v_isShared_7384_; uint8_t v_isSharedCheck_7388_; 
lean_dec(v_a_7365_);
lean_dec(v_adjustResult_7357_);
v_a_7381_ = lean_ctor_get(v___x_7366_, 0);
v_isSharedCheck_7388_ = !lean_is_exclusive(v___x_7366_);
if (v_isSharedCheck_7388_ == 0)
{
v___x_7383_ = v___x_7366_;
v_isShared_7384_ = v_isSharedCheck_7388_;
goto v_resetjp_7382_;
}
else
{
lean_inc(v_a_7381_);
lean_dec(v___x_7366_);
v___x_7383_ = lean_box(0);
v_isShared_7384_ = v_isSharedCheck_7388_;
goto v_resetjp_7382_;
}
v_resetjp_7382_:
{
lean_object* v___x_7386_; 
if (v_isShared_7384_ == 0)
{
v___x_7386_ = v___x_7383_;
goto v_reusejp_7385_;
}
else
{
lean_object* v_reuseFailAlloc_7387_; 
v_reuseFailAlloc_7387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7387_, 0, v_a_7381_);
v___x_7386_ = v_reuseFailAlloc_7387_;
goto v_reusejp_7385_;
}
v_reusejp_7385_:
{
return v___x_7386_;
}
}
}
}
else
{
lean_object* v_a_7389_; lean_object* v___x_7391_; uint8_t v_isShared_7392_; uint8_t v_isSharedCheck_7396_; 
lean_dec_ref(v_ty_7358_);
lean_dec(v_adjustResult_7357_);
lean_dec(v_droppedEntriesRef_7356_);
lean_dec(v_constantsPerTask_7355_);
lean_dec(v_droppedKeys_7354_);
lean_dec_ref(v_addEntry_7353_);
v_a_7389_ = lean_ctor_get(v___x_7364_, 0);
v_isSharedCheck_7396_ = !lean_is_exclusive(v___x_7364_);
if (v_isSharedCheck_7396_ == 0)
{
v___x_7391_ = v___x_7364_;
v_isShared_7392_ = v_isSharedCheck_7396_;
goto v_resetjp_7390_;
}
else
{
lean_inc(v_a_7389_);
lean_dec(v___x_7364_);
v___x_7391_ = lean_box(0);
v_isShared_7392_ = v_isSharedCheck_7396_;
goto v_resetjp_7390_;
}
v_resetjp_7390_:
{
lean_object* v___x_7394_; 
if (v_isShared_7392_ == 0)
{
v___x_7394_ = v___x_7391_;
goto v_reusejp_7393_;
}
else
{
lean_object* v_reuseFailAlloc_7395_; 
v_reuseFailAlloc_7395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7395_, 0, v_a_7389_);
v___x_7394_ = v_reuseFailAlloc_7395_;
goto v_reusejp_7393_;
}
v_reusejp_7393_:
{
return v___x_7394_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg___boxed(lean_object* v_moduleTreeRef_7397_, lean_object* v_ref_7398_, lean_object* v_addEntry_7399_, lean_object* v_droppedKeys_7400_, lean_object* v_constantsPerTask_7401_, lean_object* v_droppedEntriesRef_7402_, lean_object* v_adjustResult_7403_, lean_object* v_ty_7404_, lean_object* v_a_7405_, lean_object* v_a_7406_, lean_object* v_a_7407_, lean_object* v_a_7408_, lean_object* v_a_7409_){
_start:
{
lean_object* v_res_7410_; 
v_res_7410_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_moduleTreeRef_7397_, v_ref_7398_, v_addEntry_7399_, v_droppedKeys_7400_, v_constantsPerTask_7401_, v_droppedEntriesRef_7402_, v_adjustResult_7403_, v_ty_7404_, v_a_7405_, v_a_7406_, v_a_7407_, v_a_7408_);
lean_dec(v_a_7408_);
lean_dec_ref(v_a_7407_);
lean_dec(v_a_7406_);
lean_dec_ref(v_a_7405_);
lean_dec(v_ref_7398_);
return v_res_7410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt(lean_object* v_00_u03b1_7411_, lean_object* v_00_u03b2_7412_, lean_object* v_moduleTreeRef_7413_, lean_object* v_ref_7414_, lean_object* v_addEntry_7415_, lean_object* v_droppedKeys_7416_, lean_object* v_constantsPerTask_7417_, lean_object* v_droppedEntriesRef_7418_, lean_object* v_adjustResult_7419_, lean_object* v_ty_7420_, lean_object* v_a_7421_, lean_object* v_a_7422_, lean_object* v_a_7423_, lean_object* v_a_7424_){
_start:
{
lean_object* v___x_7426_; 
v___x_7426_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_moduleTreeRef_7413_, v_ref_7414_, v_addEntry_7415_, v_droppedKeys_7416_, v_constantsPerTask_7417_, v_droppedEntriesRef_7418_, v_adjustResult_7419_, v_ty_7420_, v_a_7421_, v_a_7422_, v_a_7423_, v_a_7424_);
return v___x_7426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___boxed(lean_object* v_00_u03b1_7427_, lean_object* v_00_u03b2_7428_, lean_object* v_moduleTreeRef_7429_, lean_object* v_ref_7430_, lean_object* v_addEntry_7431_, lean_object* v_droppedKeys_7432_, lean_object* v_constantsPerTask_7433_, lean_object* v_droppedEntriesRef_7434_, lean_object* v_adjustResult_7435_, lean_object* v_ty_7436_, lean_object* v_a_7437_, lean_object* v_a_7438_, lean_object* v_a_7439_, lean_object* v_a_7440_, lean_object* v_a_7441_){
_start:
{
lean_object* v_res_7442_; 
v_res_7442_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt(v_00_u03b1_7427_, v_00_u03b2_7428_, v_moduleTreeRef_7429_, v_ref_7430_, v_addEntry_7431_, v_droppedKeys_7432_, v_constantsPerTask_7433_, v_droppedEntriesRef_7434_, v_adjustResult_7435_, v_ty_7436_, v_a_7437_, v_a_7438_, v_a_7439_, v_a_7440_);
lean_dec(v_a_7440_);
lean_dec_ref(v_a_7439_);
lean_dec(v_a_7438_);
lean_dec_ref(v_a_7437_);
lean_dec(v_ref_7430_);
return v_res_7442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0(lean_object* v_00_u03b1_7443_, lean_object* v_00_u03b2_7444_, lean_object* v_adjustResult_7445_, lean_object* v_mr_7446_, lean_object* v_a_7447_){
_start:
{
lean_object* v___x_7448_; 
v___x_7448_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7445_, v_mr_7446_, v_a_7447_);
return v___x_7448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___boxed(lean_object* v_00_u03b1_7449_, lean_object* v_00_u03b2_7450_, lean_object* v_adjustResult_7451_, lean_object* v_mr_7452_, lean_object* v_a_7453_){
_start:
{
lean_object* v_res_7454_; 
v_res_7454_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0(v_00_u03b1_7449_, v_00_u03b2_7450_, v_adjustResult_7451_, v_mr_7452_, v_a_7453_);
lean_dec_ref(v_mr_7452_);
return v_res_7454_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0(lean_object* v_00_u03b1_7455_, lean_object* v_00_u03b2_7456_, lean_object* v_adjustResult_7457_, lean_object* v_j_7458_, size_t v_sz_7459_, size_t v_i_7460_, lean_object* v_bs_7461_){
_start:
{
lean_object* v___x_7462_; 
v___x_7462_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(v_adjustResult_7457_, v_j_7458_, v_sz_7459_, v_i_7460_, v_bs_7461_);
return v___x_7462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___boxed(lean_object* v_00_u03b1_7463_, lean_object* v_00_u03b2_7464_, lean_object* v_adjustResult_7465_, lean_object* v_j_7466_, lean_object* v_sz_7467_, lean_object* v_i_7468_, lean_object* v_bs_7469_){
_start:
{
size_t v_sz_boxed_7470_; size_t v_i_boxed_7471_; lean_object* v_res_7472_; 
v_sz_boxed_7470_ = lean_unbox_usize(v_sz_7467_);
lean_dec(v_sz_7467_);
v_i_boxed_7471_ = lean_unbox_usize(v_i_7468_);
lean_dec(v_i_7468_);
v_res_7472_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0(v_00_u03b1_7463_, v_00_u03b2_7464_, v_adjustResult_7465_, v_j_7466_, v_sz_boxed_7470_, v_i_boxed_7471_, v_bs_7469_);
return v_res_7472_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1(lean_object* v_00_u03b1_7473_, lean_object* v_00_u03b2_7474_, lean_object* v_adjustResult_7475_, lean_object* v_j_7476_, lean_object* v_as_7477_, size_t v_i_7478_, size_t v_stop_7479_, lean_object* v_b_7480_){
_start:
{
lean_object* v___x_7481_; 
v___x_7481_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7475_, v_j_7476_, v_as_7477_, v_i_7478_, v_stop_7479_, v_b_7480_);
return v___x_7481_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___boxed(lean_object* v_00_u03b1_7482_, lean_object* v_00_u03b2_7483_, lean_object* v_adjustResult_7484_, lean_object* v_j_7485_, lean_object* v_as_7486_, lean_object* v_i_7487_, lean_object* v_stop_7488_, lean_object* v_b_7489_){
_start:
{
size_t v_i_boxed_7490_; size_t v_stop_boxed_7491_; lean_object* v_res_7492_; 
v_i_boxed_7490_ = lean_unbox_usize(v_i_7487_);
lean_dec(v_i_7487_);
v_stop_boxed_7491_ = lean_unbox_usize(v_stop_7488_);
lean_dec(v_stop_7488_);
v_res_7492_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1(v_00_u03b1_7482_, v_00_u03b2_7483_, v_adjustResult_7484_, v_j_7485_, v_as_7486_, v_i_boxed_7490_, v_stop_boxed_7491_, v_b_7489_);
lean_dec_ref(v_as_7486_);
return v_res_7492_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2(lean_object* v_00_u03b2_7493_, lean_object* v_n_7494_, lean_object* v_00_u03b1_7495_, lean_object* v_adjustResult_7496_, lean_object* v_aa_7497_, lean_object* v_n_7498_, lean_object* v_j_7499_, lean_object* v_a_7500_, lean_object* v_a_7501_){
_start:
{
lean_object* v___x_7502_; 
v___x_7502_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(v_n_7494_, v_adjustResult_7496_, v_aa_7497_, v_n_7498_, v_j_7499_, v_a_7501_);
return v___x_7502_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___boxed(lean_object* v_00_u03b2_7503_, lean_object* v_n_7504_, lean_object* v_00_u03b1_7505_, lean_object* v_adjustResult_7506_, lean_object* v_aa_7507_, lean_object* v_n_7508_, lean_object* v_j_7509_, lean_object* v_a_7510_, lean_object* v_a_7511_){
_start:
{
lean_object* v_res_7512_; 
v_res_7512_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2(v_00_u03b2_7503_, v_n_7504_, v_00_u03b1_7505_, v_adjustResult_7506_, v_aa_7507_, v_n_7508_, v_j_7509_, v_a_7510_, v_a_7511_);
lean_dec(v_j_7509_);
lean_dec(v_n_7508_);
lean_dec_ref(v_aa_7507_);
lean_dec(v_n_7504_);
return v_res_7512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_7513_, lean_object* v_n_7514_, lean_object* v_00_u03b1_7515_, lean_object* v_aa_7516_, lean_object* v_adjustResult_7517_, lean_object* v_n_7518_, lean_object* v_j_7519_, lean_object* v_a_7520_, lean_object* v_a_7521_){
_start:
{
lean_object* v___x_7522_; 
v___x_7522_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7514_, v_aa_7516_, v_adjustResult_7517_, v_n_7518_, v_j_7519_, v_a_7521_);
return v___x_7522_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b2_7523_, lean_object* v_n_7524_, lean_object* v_00_u03b1_7525_, lean_object* v_aa_7526_, lean_object* v_adjustResult_7527_, lean_object* v_n_7528_, lean_object* v_j_7529_, lean_object* v_a_7530_, lean_object* v_a_7531_){
_start:
{
lean_object* v_res_7532_; 
v_res_7532_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3(v_00_u03b2_7523_, v_n_7524_, v_00_u03b1_7525_, v_aa_7526_, v_adjustResult_7527_, v_n_7528_, v_j_7529_, v_a_7530_, v_a_7531_);
lean_dec(v_n_7528_);
lean_dec_ref(v_aa_7526_);
lean_dec(v_n_7524_);
return v_res_7532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg___lam__0(lean_object* v_x_7533_, lean_object* v_v_7534_){
_start:
{
lean_inc(v_v_7534_);
return v_v_7534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg___lam__0___boxed(lean_object* v_x_7535_, lean_object* v_v_7536_){
_start:
{
lean_object* v_res_7537_; 
v_res_7537_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg___lam__0(v_x_7535_, v_v_7536_);
lean_dec(v_v_7536_);
lean_dec(v_x_7535_);
return v_res_7537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg(lean_object* v_ref_7539_, lean_object* v_addEntry_7540_, lean_object* v_droppedKeys_7541_, lean_object* v_constantsPerTask_7542_, lean_object* v_droppedEntriesRef_7543_, lean_object* v_ty_7544_, lean_object* v_a_7545_, lean_object* v_a_7546_, lean_object* v_a_7547_, lean_object* v_a_7548_){
_start:
{
lean_object* v___f_7550_; lean_object* v___x_7551_; 
v___f_7550_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_findMatches___redArg___closed__0));
lean_inc(v_droppedEntriesRef_7543_);
lean_inc(v_droppedKeys_7541_);
lean_inc_ref(v_addEntry_7540_);
v___x_7551_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v_addEntry_7540_, v_droppedKeys_7541_, v_droppedEntriesRef_7543_, v_a_7545_, v_a_7546_, v_a_7547_, v_a_7548_);
if (lean_obj_tag(v___x_7551_) == 0)
{
lean_object* v_a_7552_; lean_object* v___x_7553_; 
v_a_7552_ = lean_ctor_get(v___x_7551_, 0);
lean_inc(v_a_7552_);
lean_dec_ref_known(v___x_7551_, 1);
v___x_7553_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_a_7552_, v_ref_7539_, v_addEntry_7540_, v_droppedKeys_7541_, v_constantsPerTask_7542_, v_droppedEntriesRef_7543_, v___f_7550_, v_ty_7544_, v_a_7545_, v_a_7546_, v_a_7547_, v_a_7548_);
return v___x_7553_;
}
else
{
lean_object* v_a_7554_; lean_object* v___x_7556_; uint8_t v_isShared_7557_; uint8_t v_isSharedCheck_7561_; 
lean_dec_ref(v_ty_7544_);
lean_dec(v_droppedEntriesRef_7543_);
lean_dec(v_constantsPerTask_7542_);
lean_dec(v_droppedKeys_7541_);
lean_dec_ref(v_addEntry_7540_);
v_a_7554_ = lean_ctor_get(v___x_7551_, 0);
v_isSharedCheck_7561_ = !lean_is_exclusive(v___x_7551_);
if (v_isSharedCheck_7561_ == 0)
{
v___x_7556_ = v___x_7551_;
v_isShared_7557_ = v_isSharedCheck_7561_;
goto v_resetjp_7555_;
}
else
{
lean_inc(v_a_7554_);
lean_dec(v___x_7551_);
v___x_7556_ = lean_box(0);
v_isShared_7557_ = v_isSharedCheck_7561_;
goto v_resetjp_7555_;
}
v_resetjp_7555_:
{
lean_object* v___x_7559_; 
if (v_isShared_7557_ == 0)
{
v___x_7559_ = v___x_7556_;
goto v_reusejp_7558_;
}
else
{
lean_object* v_reuseFailAlloc_7560_; 
v_reuseFailAlloc_7560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7560_, 0, v_a_7554_);
v___x_7559_ = v_reuseFailAlloc_7560_;
goto v_reusejp_7558_;
}
v_reusejp_7558_:
{
return v___x_7559_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg___boxed(lean_object* v_ref_7562_, lean_object* v_addEntry_7563_, lean_object* v_droppedKeys_7564_, lean_object* v_constantsPerTask_7565_, lean_object* v_droppedEntriesRef_7566_, lean_object* v_ty_7567_, lean_object* v_a_7568_, lean_object* v_a_7569_, lean_object* v_a_7570_, lean_object* v_a_7571_, lean_object* v_a_7572_){
_start:
{
lean_object* v_res_7573_; 
v_res_7573_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg(v_ref_7562_, v_addEntry_7563_, v_droppedKeys_7564_, v_constantsPerTask_7565_, v_droppedEntriesRef_7566_, v_ty_7567_, v_a_7568_, v_a_7569_, v_a_7570_, v_a_7571_);
lean_dec(v_a_7571_);
lean_dec_ref(v_a_7570_);
lean_dec(v_a_7569_);
lean_dec_ref(v_a_7568_);
lean_dec(v_ref_7562_);
return v_res_7573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches(lean_object* v_00_u03b1_7574_, lean_object* v_ref_7575_, lean_object* v_addEntry_7576_, lean_object* v_droppedKeys_7577_, lean_object* v_constantsPerTask_7578_, lean_object* v_droppedEntriesRef_7579_, lean_object* v_ty_7580_, lean_object* v_a_7581_, lean_object* v_a_7582_, lean_object* v_a_7583_, lean_object* v_a_7584_){
_start:
{
lean_object* v___x_7586_; 
v___x_7586_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg(v_ref_7575_, v_addEntry_7576_, v_droppedKeys_7577_, v_constantsPerTask_7578_, v_droppedEntriesRef_7579_, v_ty_7580_, v_a_7581_, v_a_7582_, v_a_7583_, v_a_7584_);
return v___x_7586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___boxed(lean_object* v_00_u03b1_7587_, lean_object* v_ref_7588_, lean_object* v_addEntry_7589_, lean_object* v_droppedKeys_7590_, lean_object* v_constantsPerTask_7591_, lean_object* v_droppedEntriesRef_7592_, lean_object* v_ty_7593_, lean_object* v_a_7594_, lean_object* v_a_7595_, lean_object* v_a_7596_, lean_object* v_a_7597_, lean_object* v_a_7598_){
_start:
{
lean_object* v_res_7599_; 
v_res_7599_ = l_Lean_Meta_LazyDiscrTree_findMatches(v_00_u03b1_7587_, v_ref_7588_, v_addEntry_7589_, v_droppedKeys_7590_, v_constantsPerTask_7591_, v_droppedEntriesRef_7592_, v_ty_7593_, v_a_7594_, v_a_7595_, v_a_7596_, v_a_7597_);
lean_dec(v_a_7597_);
lean_dec_ref(v_a_7596_);
lean_dec(v_a_7595_);
lean_dec_ref(v_a_7594_);
lean_dec(v_ref_7588_);
return v_res_7599_;
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
