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
lean_object* v___y_764_; uint8_t v___y_774_; uint16_t v___y_775_; lean_object* v___y_776_; lean_object* v___y_777_; lean_object* v___y_778_; uint8_t v___y_779_; lean_object* v_toCold_784_; lean_object* v_currRecDepth_785_; lean_object* v_ref_786_; uint16_t v_optionFlags_787_; uint8_t v_suppressElabErrors_788_; uint8_t v_isRecordingDeps_789_; lean_object* v_maxRecDepth_790_; lean_object* v_cancelTk_x3f_791_; 
v_toCold_784_ = lean_ctor_get(v___y_760_, 0);
v_currRecDepth_785_ = lean_ctor_get(v___y_760_, 1);
v_ref_786_ = lean_ctor_get(v___y_760_, 2);
v_optionFlags_787_ = lean_ctor_get_uint16(v___y_760_, sizeof(void*)*3);
v_suppressElabErrors_788_ = lean_ctor_get_uint8(v___y_760_, sizeof(void*)*3 + 2);
v_isRecordingDeps_789_ = lean_ctor_get_uint8(v___y_760_, sizeof(void*)*3 + 3);
v_maxRecDepth_790_ = lean_ctor_get(v_toCold_784_, 3);
v_cancelTk_x3f_791_ = lean_ctor_get(v_toCold_784_, 10);
if (lean_obj_tag(v_cancelTk_x3f_791_) == 1)
{
lean_object* v_val_797_; uint8_t v___x_798_; 
v_val_797_ = lean_ctor_get(v_cancelTk_x3f_791_, 0);
v___x_798_ = l_IO_CancelToken_isSet(v_val_797_);
if (v___x_798_ == 0)
{
goto v___jp_792_;
}
else
{
lean_object* v___x_799_; lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_807_; 
lean_dec_ref(v_x_758_);
v___x_799_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg();
v_a_800_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_807_ == 0)
{
v___x_802_ = v___x_799_;
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v___x_799_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_805_; 
if (v_isShared_803_ == 0)
{
v___x_805_ = v___x_802_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_a_800_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
}
else
{
goto v___jp_792_;
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
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_780_ = lean_unsigned_to_nat(1u);
v___x_781_ = lean_nat_add(v___y_777_, v___x_780_);
lean_inc_ref(v___y_776_);
v___x_782_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_782_, 0, v___y_776_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
lean_ctor_set(v___x_782_, 2, v___y_778_);
lean_ctor_set_uint16(v___x_782_, sizeof(void*)*3, v___y_775_);
lean_ctor_set_uint8(v___x_782_, sizeof(void*)*3 + 2, v___y_774_);
lean_ctor_set_uint8(v___x_782_, sizeof(void*)*3 + 3, v___y_779_);
lean_inc(v___y_761_);
lean_inc(v___y_759_);
v___x_783_ = lean_apply_4(v_x_758_, v___y_759_, v___x_782_, v___y_761_, lean_box(0));
v___y_764_ = v___x_783_;
goto v___jp_763_;
}
v___jp_792_:
{
lean_object* v___x_793_; uint8_t v___x_794_; 
v___x_793_ = lean_unsigned_to_nat(0u);
v___x_794_ = lean_nat_dec_eq(v_maxRecDepth_790_, v___x_793_);
if (v___x_794_ == 0)
{
uint8_t v___x_795_; 
v___x_795_ = lean_nat_dec_eq(v_currRecDepth_785_, v_maxRecDepth_790_);
if (v___x_795_ == 0)
{
lean_inc(v_ref_786_);
v___y_774_ = v_suppressElabErrors_788_;
v___y_775_ = v_optionFlags_787_;
v___y_776_ = v_toCold_784_;
v___y_777_ = v_currRecDepth_785_;
v___y_778_ = v_ref_786_;
v___y_779_ = v_isRecordingDeps_789_;
goto v___jp_773_;
}
else
{
lean_object* v___x_796_; 
lean_dec_ref(v_x_758_);
lean_inc(v_ref_786_);
v___x_796_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_786_);
v___y_764_ = v___x_796_;
goto v___jp_763_;
}
}
else
{
lean_inc(v_ref_786_);
v___y_774_ = v_suppressElabErrors_788_;
v___y_775_ = v_optionFlags_787_;
v___y_776_ = v_toCold_784_;
v___y_777_ = v_currRecDepth_785_;
v___y_778_ = v_ref_786_;
v___y_779_ = v_isRecordingDeps_789_;
goto v___jp_773_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg(v_x_808_, v___y_809_, v___y_810_, v___y_811_);
lean_dec(v___y_811_);
lean_dec_ref(v___y_810_);
lean_dec(v___y_809_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_a_814_, lean_object* v_x_815_){
_start:
{
if (lean_obj_tag(v_x_815_) == 0)
{
lean_object* v___x_816_; 
v___x_816_ = lean_box(0);
return v___x_816_;
}
else
{
lean_object* v_key_817_; lean_object* v_value_818_; lean_object* v_tail_819_; uint8_t v___x_820_; 
v_key_817_ = lean_ctor_get(v_x_815_, 0);
v_value_818_ = lean_ctor_get(v_x_815_, 1);
v_tail_819_ = lean_ctor_get(v_x_815_, 2);
v___x_820_ = l_Lean_ExprStructEq_beq(v_key_817_, v_a_814_);
if (v___x_820_ == 0)
{
v_x_815_ = v_tail_819_;
goto _start;
}
else
{
lean_object* v___x_822_; 
lean_inc(v_value_818_);
v___x_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_822_, 0, v_value_818_);
return v___x_822_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_a_823_, lean_object* v_x_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg(v_a_823_, v_x_824_);
lean_dec(v_x_824_);
lean_dec_ref(v_a_823_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg(lean_object* v_m_826_, lean_object* v_a_827_){
_start:
{
lean_object* v_buckets_828_; lean_object* v___x_829_; uint64_t v___x_830_; uint64_t v___x_831_; uint64_t v___x_832_; uint64_t v_fold_833_; uint64_t v___x_834_; uint64_t v___x_835_; uint64_t v___x_836_; size_t v___x_837_; size_t v___x_838_; size_t v___x_839_; size_t v___x_840_; size_t v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
v_buckets_828_ = lean_ctor_get(v_m_826_, 1);
v___x_829_ = lean_array_get_size(v_buckets_828_);
v___x_830_ = l_Lean_ExprStructEq_hash(v_a_827_);
v___x_831_ = 32ULL;
v___x_832_ = lean_uint64_shift_right(v___x_830_, v___x_831_);
v_fold_833_ = lean_uint64_xor(v___x_830_, v___x_832_);
v___x_834_ = 16ULL;
v___x_835_ = lean_uint64_shift_right(v_fold_833_, v___x_834_);
v___x_836_ = lean_uint64_xor(v_fold_833_, v___x_835_);
v___x_837_ = lean_uint64_to_usize(v___x_836_);
v___x_838_ = lean_usize_of_nat(v___x_829_);
v___x_839_ = ((size_t)1ULL);
v___x_840_ = lean_usize_sub(v___x_838_, v___x_839_);
v___x_841_ = lean_usize_land(v___x_837_, v___x_840_);
v___x_842_ = lean_array_uget_borrowed(v_buckets_828_, v___x_841_);
v___x_843_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg(v_a_827_, v___x_842_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_m_844_, lean_object* v_a_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg(v_m_844_, v_a_845_);
lean_dec_ref(v_a_845_);
lean_dec_ref(v_m_844_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12___redArg(lean_object* v_a_847_, lean_object* v_b_848_, lean_object* v_x_849_){
_start:
{
if (lean_obj_tag(v_x_849_) == 0)
{
lean_dec(v_b_848_);
lean_dec_ref(v_a_847_);
return v_x_849_;
}
else
{
lean_object* v_key_850_; lean_object* v_value_851_; lean_object* v_tail_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_864_; 
v_key_850_ = lean_ctor_get(v_x_849_, 0);
v_value_851_ = lean_ctor_get(v_x_849_, 1);
v_tail_852_ = lean_ctor_get(v_x_849_, 2);
v_isSharedCheck_864_ = !lean_is_exclusive(v_x_849_);
if (v_isSharedCheck_864_ == 0)
{
v___x_854_ = v_x_849_;
v_isShared_855_ = v_isSharedCheck_864_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_tail_852_);
lean_inc(v_value_851_);
lean_inc(v_key_850_);
lean_dec(v_x_849_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_864_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
uint8_t v___x_856_; 
v___x_856_ = l_Lean_ExprStructEq_beq(v_key_850_, v_a_847_);
if (v___x_856_ == 0)
{
lean_object* v___x_857_; lean_object* v___x_859_; 
v___x_857_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12___redArg(v_a_847_, v_b_848_, v_tail_852_);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 2, v___x_857_);
v___x_859_ = v___x_854_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_key_850_);
lean_ctor_set(v_reuseFailAlloc_860_, 1, v_value_851_);
lean_ctor_set(v_reuseFailAlloc_860_, 2, v___x_857_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
else
{
lean_object* v___x_862_; 
lean_dec(v_value_851_);
lean_dec(v_key_850_);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 1, v_b_848_);
lean_ctor_set(v___x_854_, 0, v_a_847_);
v___x_862_ = v___x_854_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_a_847_);
lean_ctor_set(v_reuseFailAlloc_863_, 1, v_b_848_);
lean_ctor_set(v_reuseFailAlloc_863_, 2, v_tail_852_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(lean_object* v_x_865_, lean_object* v_x_866_){
_start:
{
if (lean_obj_tag(v_x_866_) == 0)
{
return v_x_865_;
}
else
{
lean_object* v_key_867_; lean_object* v_value_868_; lean_object* v_tail_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_892_; 
v_key_867_ = lean_ctor_get(v_x_866_, 0);
v_value_868_ = lean_ctor_get(v_x_866_, 1);
v_tail_869_ = lean_ctor_get(v_x_866_, 2);
v_isSharedCheck_892_ = !lean_is_exclusive(v_x_866_);
if (v_isSharedCheck_892_ == 0)
{
v___x_871_ = v_x_866_;
v_isShared_872_ = v_isSharedCheck_892_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_tail_869_);
lean_inc(v_value_868_);
lean_inc(v_key_867_);
lean_dec(v_x_866_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_892_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_873_; uint64_t v___x_874_; uint64_t v___x_875_; uint64_t v___x_876_; uint64_t v_fold_877_; uint64_t v___x_878_; uint64_t v___x_879_; uint64_t v___x_880_; size_t v___x_881_; size_t v___x_882_; size_t v___x_883_; size_t v___x_884_; size_t v___x_885_; lean_object* v___x_886_; lean_object* v___x_888_; 
v___x_873_ = lean_array_get_size(v_x_865_);
v___x_874_ = l_Lean_ExprStructEq_hash(v_key_867_);
v___x_875_ = 32ULL;
v___x_876_ = lean_uint64_shift_right(v___x_874_, v___x_875_);
v_fold_877_ = lean_uint64_xor(v___x_874_, v___x_876_);
v___x_878_ = 16ULL;
v___x_879_ = lean_uint64_shift_right(v_fold_877_, v___x_878_);
v___x_880_ = lean_uint64_xor(v_fold_877_, v___x_879_);
v___x_881_ = lean_uint64_to_usize(v___x_880_);
v___x_882_ = lean_usize_of_nat(v___x_873_);
v___x_883_ = ((size_t)1ULL);
v___x_884_ = lean_usize_sub(v___x_882_, v___x_883_);
v___x_885_ = lean_usize_land(v___x_881_, v___x_884_);
v___x_886_ = lean_array_uget_borrowed(v_x_865_, v___x_885_);
lean_inc(v___x_886_);
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 2, v___x_886_);
v___x_888_ = v___x_871_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_key_867_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v_value_868_);
lean_ctor_set(v_reuseFailAlloc_891_, 2, v___x_886_);
v___x_888_ = v_reuseFailAlloc_891_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
lean_object* v___x_889_; 
v___x_889_ = lean_array_uset(v_x_865_, v___x_885_, v___x_888_);
v_x_865_ = v___x_889_;
v_x_866_ = v_tail_869_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(lean_object* v_i_893_, lean_object* v_source_894_, lean_object* v_target_895_){
_start:
{
lean_object* v___x_896_; uint8_t v___x_897_; 
v___x_896_ = lean_array_get_size(v_source_894_);
v___x_897_ = lean_nat_dec_lt(v_i_893_, v___x_896_);
if (v___x_897_ == 0)
{
lean_dec_ref(v_source_894_);
lean_dec(v_i_893_);
return v_target_895_;
}
else
{
lean_object* v_es_898_; lean_object* v___x_899_; lean_object* v_source_900_; lean_object* v_target_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v_es_898_ = lean_array_fget(v_source_894_, v_i_893_);
v___x_899_ = lean_box(0);
v_source_900_ = lean_array_fset(v_source_894_, v_i_893_, v___x_899_);
v_target_901_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_target_895_, v_es_898_);
v___x_902_ = lean_unsigned_to_nat(1u);
v___x_903_ = lean_nat_add(v_i_893_, v___x_902_);
lean_dec(v_i_893_);
v_i_893_ = v___x_903_;
v_source_894_ = v_source_900_;
v_target_895_ = v_target_901_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11___redArg(lean_object* v_data_905_){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v_nbuckets_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_906_ = lean_array_get_size(v_data_905_);
v___x_907_ = lean_unsigned_to_nat(2u);
v_nbuckets_908_ = lean_nat_mul(v___x_906_, v___x_907_);
v___x_909_ = lean_unsigned_to_nat(0u);
v___x_910_ = lean_box(0);
v___x_911_ = lean_mk_array(v_nbuckets_908_, v___x_910_);
v___x_912_ = lean_array_propagate_mark(v_data_905_, v___x_911_);
v___x_913_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v___x_909_, v_data_905_, v___x_912_);
return v___x_913_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(lean_object* v_a_914_, lean_object* v_x_915_){
_start:
{
if (lean_obj_tag(v_x_915_) == 0)
{
uint8_t v___x_916_; 
v___x_916_ = 0;
return v___x_916_;
}
else
{
lean_object* v_key_917_; lean_object* v_tail_918_; uint8_t v___x_919_; 
v_key_917_ = lean_ctor_get(v_x_915_, 0);
v_tail_918_ = lean_ctor_get(v_x_915_, 2);
v___x_919_ = l_Lean_ExprStructEq_beq(v_key_917_, v_a_914_);
if (v___x_919_ == 0)
{
v_x_915_ = v_tail_918_;
goto _start;
}
else
{
return v___x_919_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg___boxed(lean_object* v_a_921_, lean_object* v_x_922_){
_start:
{
uint8_t v_res_923_; lean_object* v_r_924_; 
v_res_923_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(v_a_921_, v_x_922_);
lean_dec(v_x_922_);
lean_dec_ref(v_a_921_);
v_r_924_ = lean_box(v_res_923_);
return v_r_924_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6___redArg(lean_object* v_m_925_, lean_object* v_a_926_, lean_object* v_b_927_){
_start:
{
lean_object* v_size_928_; lean_object* v_buckets_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_972_; 
v_size_928_ = lean_ctor_get(v_m_925_, 0);
v_buckets_929_ = lean_ctor_get(v_m_925_, 1);
v_isSharedCheck_972_ = !lean_is_exclusive(v_m_925_);
if (v_isSharedCheck_972_ == 0)
{
v___x_931_ = v_m_925_;
v_isShared_932_ = v_isSharedCheck_972_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_buckets_929_);
lean_inc(v_size_928_);
lean_dec(v_m_925_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_972_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_933_; uint64_t v___x_934_; uint64_t v___x_935_; uint64_t v___x_936_; uint64_t v_fold_937_; uint64_t v___x_938_; uint64_t v___x_939_; uint64_t v___x_940_; size_t v___x_941_; size_t v___x_942_; size_t v___x_943_; size_t v___x_944_; size_t v___x_945_; lean_object* v_bkt_946_; uint8_t v___x_947_; 
v___x_933_ = lean_array_get_size(v_buckets_929_);
v___x_934_ = l_Lean_ExprStructEq_hash(v_a_926_);
v___x_935_ = 32ULL;
v___x_936_ = lean_uint64_shift_right(v___x_934_, v___x_935_);
v_fold_937_ = lean_uint64_xor(v___x_934_, v___x_936_);
v___x_938_ = 16ULL;
v___x_939_ = lean_uint64_shift_right(v_fold_937_, v___x_938_);
v___x_940_ = lean_uint64_xor(v_fold_937_, v___x_939_);
v___x_941_ = lean_uint64_to_usize(v___x_940_);
v___x_942_ = lean_usize_of_nat(v___x_933_);
v___x_943_ = ((size_t)1ULL);
v___x_944_ = lean_usize_sub(v___x_942_, v___x_943_);
v___x_945_ = lean_usize_land(v___x_941_, v___x_944_);
v_bkt_946_ = lean_array_uget_borrowed(v_buckets_929_, v___x_945_);
v___x_947_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(v_a_926_, v_bkt_946_);
if (v___x_947_ == 0)
{
lean_object* v___x_948_; lean_object* v_size_x27_949_; lean_object* v___x_950_; lean_object* v_buckets_x27_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; uint8_t v___x_957_; 
v___x_948_ = lean_unsigned_to_nat(1u);
v_size_x27_949_ = lean_nat_add(v_size_928_, v___x_948_);
lean_dec(v_size_928_);
lean_inc(v_bkt_946_);
v___x_950_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_950_, 0, v_a_926_);
lean_ctor_set(v___x_950_, 1, v_b_927_);
lean_ctor_set(v___x_950_, 2, v_bkt_946_);
v_buckets_x27_951_ = lean_array_uset(v_buckets_929_, v___x_945_, v___x_950_);
v___x_952_ = lean_unsigned_to_nat(4u);
v___x_953_ = lean_nat_mul(v_size_x27_949_, v___x_952_);
v___x_954_ = lean_unsigned_to_nat(3u);
v___x_955_ = lean_nat_div(v___x_953_, v___x_954_);
lean_dec(v___x_953_);
v___x_956_ = lean_array_get_size(v_buckets_x27_951_);
v___x_957_ = lean_nat_dec_le(v___x_955_, v___x_956_);
lean_dec(v___x_955_);
if (v___x_957_ == 0)
{
lean_object* v_val_958_; lean_object* v___x_960_; 
v_val_958_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11___redArg(v_buckets_x27_951_);
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 1, v_val_958_);
lean_ctor_set(v___x_931_, 0, v_size_x27_949_);
v___x_960_ = v___x_931_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_size_x27_949_);
lean_ctor_set(v_reuseFailAlloc_961_, 1, v_val_958_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
else
{
lean_object* v___x_963_; 
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 1, v_buckets_x27_951_);
lean_ctor_set(v___x_931_, 0, v_size_x27_949_);
v___x_963_ = v___x_931_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_size_x27_949_);
lean_ctor_set(v_reuseFailAlloc_964_, 1, v_buckets_x27_951_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
else
{
lean_object* v___x_965_; lean_object* v_buckets_x27_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_970_; 
lean_inc(v_bkt_946_);
v___x_965_ = lean_box(0);
v_buckets_x27_966_ = lean_array_uset(v_buckets_929_, v___x_945_, v___x_965_);
v___x_967_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12___redArg(v_a_926_, v_b_927_, v_bkt_946_);
v___x_968_ = lean_array_uset(v_buckets_x27_966_, v___x_945_, v___x_967_);
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 1, v___x_968_);
v___x_970_ = v___x_931_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_size_928_);
lean_ctor_set(v_reuseFailAlloc_971_, 1, v___x_968_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2(lean_object* v_a_973_, lean_object* v_e_974_, lean_object* v_a_975_){
_start:
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_977_ = lean_st_ref_take(v_a_973_);
v___x_978_ = lean_box(0);
v___x_979_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6___redArg(v___x_977_, v_e_974_, v_a_975_);
v___x_980_ = lean_st_ref_put(v_a_973_, v___x_979_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2___boxed(lean_object* v_a_981_, lean_object* v_e_982_, lean_object* v_a_983_, lean_object* v___y_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2(v_a_981_, v_e_982_, v_a_983_);
lean_dec(v_a_981_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_986_, lean_object* v_x_987_, lean_object* v___y_988_, lean_object* v___y_989_){
_start:
{
lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_991_ = lean_apply_1(v_x_987_, lean_box(0));
v___x_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_992_, 0, v___x_991_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_993_, lean_object* v_x_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(v_00_u03b1_993_, v_x_994_, v___y_995_, v___y_996_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
return v_res_998_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0(void){
_start:
{
lean_object* v___x_1000_; lean_object* v_dummy_1001_; 
v___x_1000_ = lean_box(0);
v_dummy_1001_ = l_Lean_Expr_sort___override(v___x_1000_);
return v_dummy_1001_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1(lean_object* v_pre_1002_, lean_object* v_post_1003_, size_t v_sz_1004_, size_t v_i_1005_, lean_object* v_bs_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
uint8_t v___x_1011_; 
v___x_1011_ = lean_usize_dec_lt(v_i_1005_, v_sz_1004_);
if (v___x_1011_ == 0)
{
lean_object* v___x_1012_; 
lean_dec_ref(v_post_1003_);
lean_dec_ref(v_pre_1002_);
v___x_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1012_, 0, v_bs_1006_);
return v___x_1012_;
}
else
{
lean_object* v_v_1013_; lean_object* v___x_1014_; lean_object* v_bs_x27_1015_; lean_object* v___x_1016_; 
v_v_1013_ = lean_array_uget(v_bs_1006_, v_i_1005_);
v___x_1014_ = lean_unsigned_to_nat(0u);
v_bs_x27_1015_ = lean_array_uset(v_bs_1006_, v_i_1005_, v___x_1014_);
lean_inc_ref(v_post_1003_);
lean_inc_ref(v_pre_1002_);
v___x_1016_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1002_, v_post_1003_, v_v_1013_, v___y_1007_, v___y_1008_, v___y_1009_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_object* v_a_1017_; size_t v___x_1018_; size_t v___x_1019_; lean_object* v___x_1020_; 
v_a_1017_ = lean_ctor_get(v___x_1016_, 0);
lean_inc(v_a_1017_);
lean_dec_ref_known(v___x_1016_, 1);
v___x_1018_ = ((size_t)1ULL);
v___x_1019_ = lean_usize_add(v_i_1005_, v___x_1018_);
v___x_1020_ = lean_array_uset(v_bs_x27_1015_, v_i_1005_, v_a_1017_);
v_i_1005_ = v___x_1019_;
v_bs_1006_ = v___x_1020_;
goto _start;
}
else
{
lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1029_; 
lean_dec_ref(v_bs_x27_1015_);
lean_dec_ref(v_post_1003_);
lean_dec_ref(v_pre_1002_);
v_a_1022_ = lean_ctor_get(v___x_1016_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1024_ = v___x_1016_;
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_1016_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1027_; 
if (v_isShared_1025_ == 0)
{
v___x_1027_ = v___x_1024_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_a_1022_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4(lean_object* v_pre_1030_, lean_object* v_post_1031_, lean_object* v_x_1032_, lean_object* v_x_1033_, lean_object* v_x_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
if (lean_obj_tag(v_x_1032_) == 5)
{
lean_object* v_fn_1039_; lean_object* v_arg_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; 
v_fn_1039_ = lean_ctor_get(v_x_1032_, 0);
lean_inc_ref(v_fn_1039_);
v_arg_1040_ = lean_ctor_get(v_x_1032_, 1);
lean_inc_ref(v_arg_1040_);
lean_dec_ref_known(v_x_1032_, 2);
v___x_1041_ = lean_array_set(v_x_1033_, v_x_1034_, v_arg_1040_);
v___x_1042_ = lean_unsigned_to_nat(1u);
v___x_1043_ = lean_nat_sub(v_x_1034_, v___x_1042_);
lean_dec(v_x_1034_);
v_x_1032_ = v_fn_1039_;
v_x_1033_ = v___x_1041_;
v_x_1034_ = v___x_1043_;
goto _start;
}
else
{
lean_object* v___x_1045_; 
lean_dec(v_x_1034_);
lean_inc_ref(v_post_1031_);
lean_inc_ref(v_pre_1030_);
v___x_1045_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1030_, v_post_1031_, v_x_1032_, v___y_1035_, v___y_1036_, v___y_1037_);
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_object* v_a_1046_; size_t v_sz_1047_; size_t v___x_1048_; lean_object* v___x_1049_; 
v_a_1046_ = lean_ctor_get(v___x_1045_, 0);
lean_inc(v_a_1046_);
lean_dec_ref_known(v___x_1045_, 1);
v_sz_1047_ = lean_array_size(v_x_1033_);
v___x_1048_ = ((size_t)0ULL);
lean_inc_ref(v_post_1031_);
lean_inc_ref(v_pre_1030_);
v___x_1049_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1(v_pre_1030_, v_post_1031_, v_sz_1047_, v___x_1048_, v_x_1033_, v___y_1035_, v___y_1036_, v___y_1037_);
if (lean_obj_tag(v___x_1049_) == 0)
{
lean_object* v_a_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v_a_1050_ = lean_ctor_get(v___x_1049_, 0);
lean_inc(v_a_1050_);
lean_dec_ref_known(v___x_1049_, 1);
v___x_1051_ = l_Lean_mkAppN(v_a_1046_, v_a_1050_);
lean_dec(v_a_1050_);
v___x_1052_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1030_, v_post_1031_, v___x_1051_, v___y_1035_, v___y_1036_, v___y_1037_);
return v___x_1052_;
}
else
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1060_; 
lean_dec(v_a_1046_);
lean_dec_ref(v_post_1031_);
lean_dec_ref(v_pre_1030_);
v_a_1053_ = lean_ctor_get(v___x_1049_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1055_ = v___x_1049_;
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1049_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1058_; 
if (v_isShared_1056_ == 0)
{
v___x_1058_ = v___x_1055_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_a_1053_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
}
else
{
lean_dec_ref(v_x_1033_);
lean_dec_ref(v_post_1031_);
lean_dec_ref(v_pre_1030_);
return v___x_1045_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1(lean_object* v___x_1061_, lean_object* v_pre_1062_, lean_object* v_e_1063_, lean_object* v_post_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_){
_start:
{
lean_object* v___x_1069_; 
v___x_1069_ = l_Lean_Core_checkSystem(v___x_1061_, v___y_1066_, v___y_1067_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v___x_1070_; 
lean_dec_ref_known(v___x_1069_, 1);
lean_inc_ref(v_pre_1062_);
lean_inc(v___y_1067_);
lean_inc_ref(v___y_1066_);
lean_inc_ref(v_e_1063_);
v___x_1070_ = lean_apply_4(v_pre_1062_, v_e_1063_, v___y_1066_, v___y_1067_, lean_box(0));
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_object* v_a_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1186_; 
v_a_1071_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1073_ = v___x_1070_;
v_isShared_1074_ = v_isSharedCheck_1186_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_a_1071_);
lean_dec(v___x_1070_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1186_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___y_1076_; 
switch(lean_obj_tag(v_a_1071_))
{
case 0:
{
lean_object* v_e_1176_; lean_object* v___x_1178_; 
lean_dec_ref(v_post_1064_);
lean_dec_ref(v_e_1063_);
lean_dec_ref(v_pre_1062_);
v_e_1176_ = lean_ctor_get(v_a_1071_, 0);
lean_inc_ref(v_e_1176_);
lean_dec_ref_known(v_a_1071_, 1);
if (v_isShared_1074_ == 0)
{
lean_ctor_set(v___x_1073_, 0, v_e_1176_);
v___x_1178_ = v___x_1073_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_e_1176_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
case 1:
{
lean_object* v_e_1180_; lean_object* v___x_1181_; 
lean_del_object(v___x_1073_);
lean_dec_ref(v_e_1063_);
v_e_1180_ = lean_ctor_get(v_a_1071_, 0);
lean_inc_ref(v_e_1180_);
lean_dec_ref_known(v_a_1071_, 1);
lean_inc_ref(v_post_1064_);
lean_inc_ref(v_pre_1062_);
v___x_1181_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1062_, v_post_1064_, v_e_1180_, v___y_1065_, v___y_1066_, v___y_1067_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v_a_1182_; lean_object* v___x_1183_; 
v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
lean_inc(v_a_1182_);
lean_dec_ref_known(v___x_1181_, 1);
v___x_1183_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1062_, v_post_1064_, v_a_1182_, v___y_1065_, v___y_1066_, v___y_1067_);
return v___x_1183_;
}
else
{
lean_dec_ref(v_post_1064_);
lean_dec_ref(v_pre_1062_);
return v___x_1181_;
}
}
default: 
{
lean_object* v_e_x3f_1184_; 
lean_del_object(v___x_1073_);
v_e_x3f_1184_ = lean_ctor_get(v_a_1071_, 0);
lean_inc(v_e_x3f_1184_);
lean_dec_ref_known(v_a_1071_, 1);
if (lean_obj_tag(v_e_x3f_1184_) == 0)
{
v___y_1076_ = v_e_1063_;
goto v___jp_1075_;
}
else
{
lean_object* v_val_1185_; 
lean_dec_ref(v_e_1063_);
v_val_1185_ = lean_ctor_get(v_e_x3f_1184_, 0);
lean_inc(v_val_1185_);
lean_dec_ref_known(v_e_x3f_1184_, 1);
v___y_1076_ = v_val_1185_;
goto v___jp_1075_;
}
}
}
v___jp_1075_:
{
switch(lean_obj_tag(v___y_1076_))
{
case 7:
{
lean_object* v_binderName_1077_; lean_object* v_binderType_1078_; lean_object* v_body_1079_; uint8_t v_binderInfo_1080_; lean_object* v___x_1081_; 
v_binderName_1077_ = lean_ctor_get(v___y_1076_, 0);
v_binderType_1078_ = lean_ctor_get(v___y_1076_, 1);
v_body_1079_ = lean_ctor_get(v___y_1076_, 2);
v_binderInfo_1080_ = lean_ctor_get_uint8(v___y_1076_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1078_);
lean_inc_ref(v_post_1064_);
lean_inc_ref(v_pre_1062_);
v___x_1081_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1062_, v_post_1064_, v_binderType_1078_, v___y_1065_, v___y_1066_, v___y_1067_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v_a_1082_; lean_object* v___x_1083_; 
v_a_1082_ = lean_ctor_get(v___x_1081_, 0);
lean_inc(v_a_1082_);
lean_dec_ref_known(v___x_1081_, 1);
lean_inc_ref(v_body_1079_);
lean_inc_ref(v_post_1064_);
lean_inc_ref(v_pre_1062_);
v___x_1083_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1062_, v_post_1064_, v_body_1079_, v___y_1065_, v___y_1066_, v___y_1067_);
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_object* v_a_1084_; size_t v___x_1085_; size_t v___x_1086_; uint8_t v___x_1087_; 
v_a_1084_ = lean_ctor_get(v___x_1083_, 0);
lean_inc(v_a_1084_);
lean_dec_ref_known(v___x_1083_, 1);
v___x_1085_ = lean_ptr_addr(v_binderType_1078_);
v___x_1086_ = lean_ptr_addr(v_a_1082_);
v___x_1087_ = lean_usize_dec_eq(v___x_1085_, v___x_1086_);
if (v___x_1087_ == 0)
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
lean_inc(v_binderName_1077_);
lean_dec_ref_known(v___y_1076_, 3);
v___x_1088_ = l_Lean_Expr_forallE___override(v_binderName_1077_, v_a_1082_, v_a_1084_, v_binderInfo_1080_);
v___x_1089_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1062_, v_post_1064_, v___x_1088_, v___y_1065_, v___y_1066_, v___y_1067_);
return v___x_1089_;
}
else
{
size_t v___x_1090_; size_t v___x_1091_; uint8_t v___x_1092_; 
v___x_1090_ = lean_ptr_addr(v_body_1079_);
v___x_1091_ = lean_ptr_addr(v_a_1084_);
v___x_1092_ = lean_usize_dec_eq(v___x_1090_, v___x_1091_);
if (v___x_1092_ == 0)
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
lean_inc(v_binderName_1077_);
lean_dec_ref_known(v___y_1076_, 3);
v___x_1093_ = l_Lean_Expr_forallE___override(v_binderName_1077_, v_a_1082_, v_a_1084_, v_binderInfo_1080_);
v___x_1094_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1062_, v_post_1064_, v___x_1093_, v___y_1065_, v___y_1066_, v___y_1067_);
return v___x_1094_;
}
else
{
uint8_t v___x_1095_; 
v___x_1095_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1080_, v_binderInfo_1080_);
if (v___x_1095_ == 0)
{
lean_object* v___x_1096_; lean_object* v___x_1097_; 
lean_inc(v_binderName_1077_);
lean_dec_ref_known(v___y_1076_, 3);
v___x_1096_ = l_Lean_Expr_forallE___override(v_binderName_1077_, v_a_1082_, v_a_1084_, v_binderInfo_1080_);
v___x_1097_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1062_, v_post_1064_, v___x_1096_, v___y_1065_, v___y_1066_, v___y_1067_);
return v___x_1097_;
}
else
{
lean_object* v___x_1098_; 
lean_dec(v_a_1084_);
lean_dec(v_a_1082_);
v___x_1098_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1062_, v_post_1064_, v___y_1076_, v___y_1065_, v___y_1066_, v___y_1067_);
return v___x_1098_;
}
}
}
}
else
{
lean_dec(v_a_1082_);
lean_dec_ref_known(v___y_1076_, 3);
lean_dec_ref(v_post_1064_);
lean_dec_ref(v_pre_1062_);
return v___x_1083_;
}
}
else
{
lean_dec_ref_known(v___y_1076_, 3);
lean_dec_ref(v_post_1064_);
lean_dec_ref(v_pre_1062_);
return v___x_1081_;
}
}
case 6:
{
lean_object* v_binderName_1099_; lean_object* v_binderType_1100_; lean_object* v_body_1101_; uint8_t v_binderInfo_1102_; lean_object* v___x_1103_; 
v_binderName_1099_ = lean_ctor_get(v___y_1076_, 0);
v_binderType_1100_ = lean_ctor_get(v___y_1076_, 1);
v_body_1101_ = lean_ctor_get(v___y_1076_, 2);
v_binderInfo_1102_ = lean_ctor_get_uint8(v___y_1076_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1100_);
lean_inc_ref(v_post_1064_);
lean_inc_ref(v_pre_1062_);
v___x_1103_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1062_, v_post_1064_, v_binderType_1100_, v___y_1065_, v___y_1066_, v___y_1067_);
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_object* v_a_1104_; lean_object* v___x_1105_; 
v_a_1104_ = lean_ctor_get(v___x_1103_, 0);
lean_inc(v_a_1104_);
lean_dec_ref_known(v___x_1103_, 1);
lean_inc_ref(v_body_1101_);
lean_inc_ref(v_post_1064_);
lean_inc_ref(v_pre_1062_);
v___x_1105_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1062_, v_post_1064_, v_body_1101_, v___y_1065_, v___y_1066_, v___y_1067_);
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_object* v_a_1106_; size_t v___x_1107_; size_t v___x_1108_; uint8_t v___x_1109_; 
v_a_1106_ = lean_ctor_get(v___x_1105_, 0);
lean_inc(v_a_1106_);
lean_dec_ref_known(v___x_1105_, 1);
v___x_1107_ = lean_ptr_addr(v_binderType_1100_);
v___x_1108_ = lean_ptr_addr(v_a_1104_);
v___x_1109_ = lean_usize_dec_eq(v___x_1107_, v___x_1108_);
if (v___x_1109_ == 0)
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
lean_inc(v_binderName_1099_);
lean_dec_ref_known(v___y_1076_, 3);
v___x_1110_ = l_Lean_Expr_lam___override(v_binderName_1099_, v_a_1104_, v_a_1106_, v_binderInfo_1102_);
v___x_1111_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1062_, v_post_1064_, v___x_1110_, v___y_1065_, v___y_1066_, v___y_1067_);
return v___x_1111_;
}
else
{
size_t v___x_1112_; size_t v___x_1113_; uint8_t v___x_1114_; 
v___x_1112_ = lean_ptr_addr(v_body_1101_);
v___x_1113_ = lean_ptr_addr(v_a_1106_);
v___x_1114_ = lean_usize_dec_eq(v___x_1112_, v___x_1113_);
if (v___x_1114_ == 0)
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
lean_inc(v_binderName_1099_);
lean_dec_ref_known(v___y_1076_, 3);
v___x_1115_ = l_Lean_Expr_lam___override(v_binderName_1099_, v_a_1104_, v_a_1106_, v_binderInfo_1102_);
v___x_1116_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1062_, v_post_1064_, v___x_1115_, v___y_1065_, v___y_1066_, v___y_1067_);
return v___x_1116_;
}
else
{
uint8_t v___x_1117_; 
v___x_1117_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1102_, v_binderInfo_1102_);
if (v___x_1117_ == 0)
{
lean_object* v___x_1118_; lean_object* v___x_1119_; 
lean_inc(v_binderName_1099_);
lean_dec_ref_known(v___y_1076_, 3);
v___x_1118_ = l_Lean_Expr_lam___override(v_binderName_1099_, v_a_1104_, v_a_1106_, v_binderInfo_1102_);
v___x_1119_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1062_, v_post_1064_, v___x_1118_, v___y_1065_, v___y_1066_, v___y_1067_);
return v___x_1119_;
}
else
{
lean_object* v___x_1120_; 
lean_dec(v_a_1106_);
lean_dec(v_a_1104_);
v___x_1120_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1062_, v_post_1064_, v___y_1076_, v___y_1065_, v___y_1066_, v___y_1067_);
return v___x_1120_;
}
}
}
}
else
{
lean_dec(v_a_1104_);
lean_dec_ref_known(v___y_1076_, 3);
lean_dec_ref(v_post_1064_);
lean_dec_ref(v_pre_1062_);
return v___x_1105_;
}
}
else
{
lean_dec_ref_known(v___y_1076_, 3);
lean_dec_ref(v_post_1064_);
lean_dec_ref(v_pre_1062_);
return v___x_1103_;
}
}
case 8:
{
lean_object* v_declName_1121_; lean_object* v_type_1122_; lean_object* v_value_1123_; lean_object* v_body_1124_; uint8_t v_nondep_1125_; lean_object* v___x_1126_; 
v_declName_1121_ = lean_ctor_get(v___y_1076_, 0);
v_type_1122_ = lean_ctor_get(v___y_1076_, 1);
v_value_1123_ = lean_ctor_get(v___y_1076_, 2);
v_body_1124_ = lean_ctor_get(v___y_1076_, 3);
v_nondep_1125_ = lean_ctor_get_uint8(v___y_1076_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_1122_);
lean_inc_ref(v_post_1064_);
lean_inc_ref(v_pre_1062_);
v___x_1126_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1062_, v_post_1064_, v_type_1122_, v___y_1065_, v___y_1066_, v___y_1067_);
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_object* v_a_1127_; lean_object* v___x_1128_; 
v_a_1127_ = lean_ctor_get(v___x_1126_, 0);
lean_inc(v_a_1127_);
lean_dec_ref_known(v___x_1126_, 1);
lean_inc_ref(v_value_1123_);
lean_inc_ref(v_post_1064_);
lean_inc_ref(v_pre_1062_);
v___x_1128_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1062_, v_post_1064_, v_value_1123_, v___y_1065_, v___y_1066_, v___y_1067_);
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_object* v_a_1129_; lean_object* v___x_1130_; 
v_a_1129_ = lean_ctor_get(v___x_1128_, 0);
lean_inc(v_a_1129_);
lean_dec_ref_known(v___x_1128_, 1);
lean_inc_ref(v_body_1124_);
lean_inc_ref(v_post_1064_);
lean_inc_ref(v_pre_1062_);
v___x_1130_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1062_, v_post_1064_, v_body_1124_, v___y_1065_, v___y_1066_, v___y_1067_);
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v_a_1131_; size_t v___x_1132_; size_t v___x_1133_; uint8_t v___x_1134_; 
v_a_1131_ = lean_ctor_get(v___x_1130_, 0);
lean_inc(v_a_1131_);
lean_dec_ref_known(v___x_1130_, 1);
v___x_1132_ = lean_ptr_addr(v_type_1122_);
v___x_1133_ = lean_ptr_addr(v_a_1127_);
v___x_1134_ = lean_usize_dec_eq(v___x_1132_, v___x_1133_);
if (v___x_1134_ == 0)
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
lean_inc(v_declName_1121_);
lean_dec_ref_known(v___y_1076_, 4);
v___x_1135_ = l_Lean_Expr_letE___override(v_declName_1121_, v_a_1127_, v_a_1129_, v_a_1131_, v_nondep_1125_);
v___x_1136_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1062_, v_post_1064_, v___x_1135_, v___y_1065_, v___y_1066_, v___y_1067_);
return v___x_1136_;
}
else
{
size_t v___x_1137_; size_t v___x_1138_; uint8_t v___x_1139_; 
v___x_1137_ = lean_ptr_addr(v_value_1123_);
v___x_1138_ = lean_ptr_addr(v_a_1129_);
v___x_1139_ = lean_usize_dec_eq(v___x_1137_, v___x_1138_);
if (v___x_1139_ == 0)
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
lean_inc(v_declName_1121_);
lean_dec_ref_known(v___y_1076_, 4);
v___x_1140_ = l_Lean_Expr_letE___override(v_declName_1121_, v_a_1127_, v_a_1129_, v_a_1131_, v_nondep_1125_);
v___x_1141_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1062_, v_post_1064_, v___x_1140_, v___y_1065_, v___y_1066_, v___y_1067_);
return v___x_1141_;
}
else
{
size_t v___x_1142_; size_t v___x_1143_; uint8_t v___x_1144_; 
v___x_1142_ = lean_ptr_addr(v_body_1124_);
v___x_1143_ = lean_ptr_addr(v_a_1131_);
v___x_1144_ = lean_usize_dec_eq(v___x_1142_, v___x_1143_);
if (v___x_1144_ == 0)
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
lean_inc(v_declName_1121_);
lean_dec_ref_known(v___y_1076_, 4);
v___x_1145_ = l_Lean_Expr_letE___override(v_declName_1121_, v_a_1127_, v_a_1129_, v_a_1131_, v_nondep_1125_);
v___x_1146_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1062_, v_post_1064_, v___x_1145_, v___y_1065_, v___y_1066_, v___y_1067_);
return v___x_1146_;
}
else
{
lean_object* v___x_1147_; 
lean_dec(v_a_1131_);
lean_dec(v_a_1129_);
lean_dec(v_a_1127_);
v___x_1147_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1062_, v_post_1064_, v___y_1076_, v___y_1065_, v___y_1066_, v___y_1067_);
return v___x_1147_;
}
}
}
}
else
{
lean_dec(v_a_1129_);
lean_dec(v_a_1127_);
lean_dec_ref_known(v___y_1076_, 4);
lean_dec_ref(v_post_1064_);
lean_dec_ref(v_pre_1062_);
return v___x_1130_;
}
}
else
{
lean_dec(v_a_1127_);
lean_dec_ref_known(v___y_1076_, 4);
lean_dec_ref(v_post_1064_);
lean_dec_ref(v_pre_1062_);
return v___x_1128_;
}
}
else
{
lean_dec_ref_known(v___y_1076_, 4);
lean_dec_ref(v_post_1064_);
lean_dec_ref(v_pre_1062_);
return v___x_1126_;
}
}
case 5:
{
lean_object* v_dummy_1148_; lean_object* v_nargs_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
v_dummy_1148_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0);
v_nargs_1149_ = l_Lean_Expr_getAppNumArgs(v___y_1076_);
lean_inc(v_nargs_1149_);
v___x_1150_ = lean_mk_array(v_nargs_1149_, v_dummy_1148_);
v___x_1151_ = lean_unsigned_to_nat(1u);
v___x_1152_ = lean_nat_sub(v_nargs_1149_, v___x_1151_);
lean_dec(v_nargs_1149_);
v___x_1153_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4(v_pre_1062_, v_post_1064_, v___y_1076_, v___x_1150_, v___x_1152_, v___y_1065_, v___y_1066_, v___y_1067_);
return v___x_1153_;
}
case 10:
{
lean_object* v_data_1154_; lean_object* v_expr_1155_; lean_object* v___x_1156_; 
v_data_1154_ = lean_ctor_get(v___y_1076_, 0);
v_expr_1155_ = lean_ctor_get(v___y_1076_, 1);
lean_inc_ref(v_expr_1155_);
lean_inc_ref(v_post_1064_);
lean_inc_ref(v_pre_1062_);
v___x_1156_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1062_, v_post_1064_, v_expr_1155_, v___y_1065_, v___y_1066_, v___y_1067_);
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v_a_1157_; size_t v___x_1158_; size_t v___x_1159_; uint8_t v___x_1160_; 
v_a_1157_ = lean_ctor_get(v___x_1156_, 0);
lean_inc(v_a_1157_);
lean_dec_ref_known(v___x_1156_, 1);
v___x_1158_ = lean_ptr_addr(v_expr_1155_);
v___x_1159_ = lean_ptr_addr(v_a_1157_);
v___x_1160_ = lean_usize_dec_eq(v___x_1158_, v___x_1159_);
if (v___x_1160_ == 0)
{
lean_object* v___x_1161_; lean_object* v___x_1162_; 
lean_inc(v_data_1154_);
lean_dec_ref_known(v___y_1076_, 2);
v___x_1161_ = l_Lean_Expr_mdata___override(v_data_1154_, v_a_1157_);
v___x_1162_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1062_, v_post_1064_, v___x_1161_, v___y_1065_, v___y_1066_, v___y_1067_);
return v___x_1162_;
}
else
{
lean_object* v___x_1163_; 
lean_dec(v_a_1157_);
v___x_1163_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1062_, v_post_1064_, v___y_1076_, v___y_1065_, v___y_1066_, v___y_1067_);
return v___x_1163_;
}
}
else
{
lean_dec_ref_known(v___y_1076_, 2);
lean_dec_ref(v_post_1064_);
lean_dec_ref(v_pre_1062_);
return v___x_1156_;
}
}
case 11:
{
lean_object* v_typeName_1164_; lean_object* v_idx_1165_; lean_object* v_struct_1166_; lean_object* v___x_1167_; 
v_typeName_1164_ = lean_ctor_get(v___y_1076_, 0);
v_idx_1165_ = lean_ctor_get(v___y_1076_, 1);
v_struct_1166_ = lean_ctor_get(v___y_1076_, 2);
lean_inc_ref(v_struct_1166_);
lean_inc_ref(v_post_1064_);
lean_inc_ref(v_pre_1062_);
v___x_1167_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1062_, v_post_1064_, v_struct_1166_, v___y_1065_, v___y_1066_, v___y_1067_);
if (lean_obj_tag(v___x_1167_) == 0)
{
lean_object* v_a_1168_; size_t v___x_1169_; size_t v___x_1170_; uint8_t v___x_1171_; 
v_a_1168_ = lean_ctor_get(v___x_1167_, 0);
lean_inc(v_a_1168_);
lean_dec_ref_known(v___x_1167_, 1);
v___x_1169_ = lean_ptr_addr(v_struct_1166_);
v___x_1170_ = lean_ptr_addr(v_a_1168_);
v___x_1171_ = lean_usize_dec_eq(v___x_1169_, v___x_1170_);
if (v___x_1171_ == 0)
{
lean_object* v___x_1172_; lean_object* v___x_1173_; 
lean_inc(v_idx_1165_);
lean_inc(v_typeName_1164_);
lean_dec_ref_known(v___y_1076_, 3);
v___x_1172_ = l_Lean_Expr_proj___override(v_typeName_1164_, v_idx_1165_, v_a_1168_);
v___x_1173_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1062_, v_post_1064_, v___x_1172_, v___y_1065_, v___y_1066_, v___y_1067_);
return v___x_1173_;
}
else
{
lean_object* v___x_1174_; 
lean_dec(v_a_1168_);
v___x_1174_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1062_, v_post_1064_, v___y_1076_, v___y_1065_, v___y_1066_, v___y_1067_);
return v___x_1174_;
}
}
else
{
lean_dec_ref_known(v___y_1076_, 3);
lean_dec_ref(v_post_1064_);
lean_dec_ref(v_pre_1062_);
return v___x_1167_;
}
}
default: 
{
lean_object* v___x_1175_; 
v___x_1175_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1062_, v_post_1064_, v___y_1076_, v___y_1065_, v___y_1066_, v___y_1067_);
return v___x_1175_;
}
}
}
}
}
else
{
lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1194_; 
lean_dec_ref(v_post_1064_);
lean_dec_ref(v_e_1063_);
lean_dec_ref(v_pre_1062_);
v_a_1187_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1189_ = v___x_1070_;
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_dec(v___x_1070_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1192_; 
if (v_isShared_1190_ == 0)
{
v___x_1192_ = v___x_1189_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_a_1187_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
}
else
{
lean_object* v_a_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1202_; 
lean_dec_ref(v_post_1064_);
lean_dec_ref(v_e_1063_);
lean_dec_ref(v_pre_1062_);
v_a_1195_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1197_ = v___x_1069_;
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_a_1195_);
lean_dec(v___x_1069_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1200_; 
if (v_isShared_1198_ == 0)
{
v___x_1200_ = v___x_1197_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_a_1195_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___boxed(lean_object* v___x_1203_, lean_object* v_pre_1204_, lean_object* v_e_1205_, lean_object* v_post_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1(v___x_1203_, v_pre_1204_, v_e_1205_, v_post_1206_, v___y_1207_, v___y_1208_, v___y_1209_);
lean_dec(v___y_1209_);
lean_dec_ref(v___y_1208_);
lean_dec(v___y_1207_);
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(lean_object* v_pre_1212_, lean_object* v_post_1213_, lean_object* v_e_1214_, lean_object* v_a_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; 
lean_inc(v_a_1215_);
v___x_1219_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1219_, 0, lean_box(0));
lean_closure_set(v___x_1219_, 1, lean_box(0));
lean_closure_set(v___x_1219_, 2, v_a_1215_);
v___x_1220_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(lean_box(0), v___x_1219_, v___y_1216_, v___y_1217_);
if (lean_obj_tag(v___x_1220_) == 0)
{
lean_object* v_a_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1252_; 
v_a_1221_ = lean_ctor_get(v___x_1220_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1223_ = v___x_1220_;
v_isShared_1224_ = v_isSharedCheck_1252_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_a_1221_);
lean_dec(v___x_1220_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1252_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1225_; 
v___x_1225_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg(v_a_1221_, v_e_1214_);
lean_dec(v_a_1221_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_object* v___x_1226_; lean_object* v___f_1227_; lean_object* v___x_1228_; 
lean_del_object(v___x_1223_);
v___x_1226_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___closed__0));
lean_inc_ref(v_e_1214_);
v___f_1227_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___boxed), 8, 4);
lean_closure_set(v___f_1227_, 0, v___x_1226_);
lean_closure_set(v___f_1227_, 1, v_pre_1212_);
lean_closure_set(v___f_1227_, 2, v_e_1214_);
lean_closure_set(v___f_1227_, 3, v_post_1213_);
v___x_1228_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg(v___f_1227_, v_a_1215_, v___y_1216_, v___y_1217_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_object* v_a_1229_; lean_object* v___f_1230_; lean_object* v___x_1231_; 
v_a_1229_ = lean_ctor_get(v___x_1228_, 0);
lean_inc_n(v_a_1229_, 2);
lean_dec_ref_known(v___x_1228_, 1);
lean_inc(v_a_1215_);
v___f_1230_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1230_, 0, v_a_1215_);
lean_closure_set(v___f_1230_, 1, v_e_1214_);
lean_closure_set(v___f_1230_, 2, v_a_1229_);
v___x_1231_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(lean_box(0), v___f_1230_, v___y_1216_, v___y_1217_);
if (lean_obj_tag(v___x_1231_) == 0)
{
lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1238_; 
v_isSharedCheck_1238_ = !lean_is_exclusive(v___x_1231_);
if (v_isSharedCheck_1238_ == 0)
{
lean_object* v_unused_1239_; 
v_unused_1239_ = lean_ctor_get(v___x_1231_, 0);
lean_dec(v_unused_1239_);
v___x_1233_ = v___x_1231_;
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
else
{
lean_dec(v___x_1231_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1236_; 
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 0, v_a_1229_);
v___x_1236_ = v___x_1233_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_a_1229_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
else
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1247_; 
lean_dec(v_a_1229_);
v_a_1240_ = lean_ctor_get(v___x_1231_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1231_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1242_ = v___x_1231_;
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1231_);
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
lean_dec_ref(v_e_1214_);
return v___x_1228_;
}
}
else
{
lean_object* v_val_1248_; lean_object* v___x_1250_; 
lean_dec_ref(v_e_1214_);
lean_dec_ref(v_post_1213_);
lean_dec_ref(v_pre_1212_);
v_val_1248_ = lean_ctor_get(v___x_1225_, 0);
lean_inc(v_val_1248_);
lean_dec_ref_known(v___x_1225_, 1);
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 0, v_val_1248_);
v___x_1250_ = v___x_1223_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_val_1248_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
}
else
{
lean_object* v_a_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1260_; 
lean_dec_ref(v_e_1214_);
lean_dec_ref(v_post_1213_);
lean_dec_ref(v_pre_1212_);
v_a_1253_ = lean_ctor_get(v___x_1220_, 0);
v_isSharedCheck_1260_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1255_ = v___x_1220_;
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_a_1253_);
lean_dec(v___x_1220_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(lean_object* v_pre_1261_, lean_object* v_post_1262_, lean_object* v_e_1263_, lean_object* v_a_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_){
_start:
{
lean_object* v___x_1268_; 
lean_inc_ref(v_post_1262_);
lean_inc(v___y_1266_);
lean_inc_ref(v___y_1265_);
lean_inc_ref(v_e_1263_);
v___x_1268_ = lean_apply_4(v_post_1262_, v_e_1263_, v___y_1265_, v___y_1266_, lean_box(0));
if (lean_obj_tag(v___x_1268_) == 0)
{
lean_object* v_a_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1287_; 
v_a_1269_ = lean_ctor_get(v___x_1268_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1271_ = v___x_1268_;
v_isShared_1272_ = v_isSharedCheck_1287_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_a_1269_);
lean_dec(v___x_1268_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1287_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
switch(lean_obj_tag(v_a_1269_))
{
case 0:
{
lean_object* v_e_1273_; lean_object* v___x_1275_; 
lean_dec_ref(v_e_1263_);
lean_dec_ref(v_post_1262_);
lean_dec_ref(v_pre_1261_);
v_e_1273_ = lean_ctor_get(v_a_1269_, 0);
lean_inc_ref(v_e_1273_);
lean_dec_ref_known(v_a_1269_, 1);
if (v_isShared_1272_ == 0)
{
lean_ctor_set(v___x_1271_, 0, v_e_1273_);
v___x_1275_ = v___x_1271_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_e_1273_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
case 1:
{
lean_object* v_e_1277_; lean_object* v___x_1278_; 
lean_del_object(v___x_1271_);
lean_dec_ref(v_e_1263_);
v_e_1277_ = lean_ctor_get(v_a_1269_, 0);
lean_inc_ref(v_e_1277_);
lean_dec_ref_known(v_a_1269_, 1);
v___x_1278_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1261_, v_post_1262_, v_e_1277_, v_a_1264_, v___y_1265_, v___y_1266_);
return v___x_1278_;
}
default: 
{
lean_object* v_e_x3f_1279_; 
lean_dec_ref(v_post_1262_);
lean_dec_ref(v_pre_1261_);
v_e_x3f_1279_ = lean_ctor_get(v_a_1269_, 0);
lean_inc(v_e_x3f_1279_);
lean_dec_ref_known(v_a_1269_, 1);
if (lean_obj_tag(v_e_x3f_1279_) == 0)
{
lean_object* v___x_1281_; 
if (v_isShared_1272_ == 0)
{
lean_ctor_set(v___x_1271_, 0, v_e_1263_);
v___x_1281_ = v___x_1271_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_e_1263_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
else
{
lean_object* v_val_1283_; lean_object* v___x_1285_; 
lean_dec_ref(v_e_1263_);
v_val_1283_ = lean_ctor_get(v_e_x3f_1279_, 0);
lean_inc(v_val_1283_);
lean_dec_ref_known(v_e_x3f_1279_, 1);
if (v_isShared_1272_ == 0)
{
lean_ctor_set(v___x_1271_, 0, v_val_1283_);
v___x_1285_ = v___x_1271_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_val_1283_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
}
}
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
lean_dec_ref(v_e_1263_);
lean_dec_ref(v_post_1262_);
lean_dec_ref(v_pre_1261_);
v_a_1288_ = lean_ctor_get(v___x_1268_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1268_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1268_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1293_; 
if (v_isShared_1291_ == 0)
{
v___x_1293_ = v___x_1290_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_a_1288_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_1296_, lean_object* v_post_1297_, lean_object* v_e_1298_, lean_object* v_a_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_){
_start:
{
lean_object* v_res_1303_; 
v_res_1303_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1296_, v_post_1297_, v_e_1298_, v_a_1299_, v___y_1300_, v___y_1301_);
lean_dec(v___y_1301_);
lean_dec_ref(v___y_1300_);
lean_dec(v_a_1299_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_1304_, lean_object* v_post_1305_, lean_object* v_sz_1306_, lean_object* v_i_1307_, lean_object* v_bs_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
size_t v_sz_boxed_1313_; size_t v_i_boxed_1314_; lean_object* v_res_1315_; 
v_sz_boxed_1313_ = lean_unbox_usize(v_sz_1306_);
lean_dec(v_sz_1306_);
v_i_boxed_1314_ = lean_unbox_usize(v_i_1307_);
lean_dec(v_i_1307_);
v_res_1315_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1(v_pre_1304_, v_post_1305_, v_sz_boxed_1313_, v_i_boxed_1314_, v_bs_1308_, v___y_1309_, v___y_1310_, v___y_1311_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec(v___y_1309_);
return v_res_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_1316_, lean_object* v_post_1317_, lean_object* v_x_1318_, lean_object* v_x_1319_, lean_object* v_x_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_){
_start:
{
lean_object* v_res_1325_; 
v_res_1325_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4(v_pre_1316_, v_post_1317_, v_x_1318_, v_x_1319_, v_x_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
lean_dec(v___y_1321_);
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___boxed(lean_object* v_pre_1326_, lean_object* v_post_1327_, lean_object* v_e_1328_, lean_object* v_a_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1326_, v_post_1327_, v_e_1328_, v_a_1329_, v___y_1330_, v___y_1331_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
lean_dec(v_a_1329_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(lean_object* v_00_u03b1_1334_, lean_object* v_x_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_){
_start:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1339_ = lean_apply_1(v_x_1335_, lean_box(0));
v___x_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1340_, 0, v___x_1339_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1341_, lean_object* v_x_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(v_00_u03b1_1341_, v_x_1342_, v___y_1343_, v___y_1344_);
lean_dec(v___y_1344_);
lean_dec_ref(v___y_1343_);
return v_res_1346_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1347_ = lean_box(0);
v___x_1348_ = lean_unsigned_to_nat(16u);
v___x_1349_ = lean_mk_array(v___x_1348_, v___x_1347_);
return v___x_1349_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1350_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0, &l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0);
v___x_1351_ = lean_unsigned_to_nat(0u);
v___x_1352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1351_);
lean_ctor_set(v___x_1352_, 1, v___x_1350_);
return v___x_1352_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; 
v___x_1353_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1, &l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1_once, _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1);
v___x_1354_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1354_, 0, lean_box(0));
lean_closure_set(v___x_1354_, 1, lean_box(0));
lean_closure_set(v___x_1354_, 2, v___x_1353_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0(lean_object* v_input_1355_, lean_object* v_pre_1356_, lean_object* v_post_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v_a_1363_; lean_object* v___x_1364_; 
v___x_1361_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2);
v___x_1362_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(lean_box(0), v___x_1361_, v___y_1358_, v___y_1359_);
v_a_1363_ = lean_ctor_get(v___x_1362_, 0);
lean_inc(v_a_1363_);
lean_dec_ref(v___x_1362_);
v___x_1364_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1356_, v_post_1357_, v_input_1355_, v_a_1363_, v___y_1358_, v___y_1359_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v_a_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1374_; 
v_a_1365_ = lean_ctor_get(v___x_1364_, 0);
lean_inc(v_a_1365_);
lean_dec_ref_known(v___x_1364_, 1);
v___x_1366_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1366_, 0, lean_box(0));
lean_closure_set(v___x_1366_, 1, lean_box(0));
lean_closure_set(v___x_1366_, 2, v_a_1363_);
v___x_1367_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(lean_box(0), v___x_1366_, v___y_1358_, v___y_1359_);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1374_ == 0)
{
lean_object* v_unused_1375_; 
v_unused_1375_ = lean_ctor_get(v___x_1367_, 0);
lean_dec(v_unused_1375_);
v___x_1369_ = v___x_1367_;
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
else
{
lean_dec(v___x_1367_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1372_; 
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 0, v_a_1365_);
v___x_1372_ = v___x_1369_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_a_1365_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
}
else
{
lean_dec(v_a_1363_);
return v___x_1364_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___boxed(lean_object* v_input_1376_, lean_object* v_pre_1377_, lean_object* v_post_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_){
_start:
{
lean_object* v_res_1382_; 
v_res_1382_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0(v_input_1376_, v_pre_1377_, v_post_1378_, v___y_1379_, v___y_1380_);
lean_dec(v___y_1380_);
lean_dec_ref(v___y_1379_);
return v_res_1382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(lean_object* v_e_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_){
_start:
{
lean_object* v___f_1389_; lean_object* v___f_1390_; lean_object* v___x_1391_; 
v___f_1389_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___closed__0));
v___f_1390_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___closed__1));
v___x_1391_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0(v_e_1385_, v___f_1389_, v___f_1390_, v_a_1386_, v_a_1387_);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___boxed(lean_object* v_e_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(v_e_1392_, v_a_1393_, v_a_1394_);
lean_dec(v_a_1394_);
lean_dec_ref(v_a_1393_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1397_, lean_object* v_m_1398_, lean_object* v_a_1399_){
_start:
{
lean_object* v___x_1400_; 
v___x_1400_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg(v_m_1398_, v_a_1399_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1401_, lean_object* v_m_1402_, lean_object* v_a_1403_){
_start:
{
lean_object* v_res_1404_; 
v_res_1404_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3(v_00_u03b2_1401_, v_m_1402_, v_a_1403_);
lean_dec_ref(v_a_1403_);
lean_dec_ref(v_m_1402_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_1405_, lean_object* v_ref_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_){
_start:
{
lean_object* v___x_1410_; 
v___x_1410_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1406_);
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1411_, lean_object* v_ref_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_1411_, v_ref_1412_, v___y_1413_, v___y_1414_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8(lean_object* v_00_u03b1_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_){
_start:
{
lean_object* v___x_1421_; 
v___x_1421_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg();
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8(v_00_u03b1_1422_, v___y_1423_, v___y_1424_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_1427_, lean_object* v_x_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
lean_object* v___x_1433_; 
v___x_1433_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg(v_x_1428_, v___y_1429_, v___y_1430_, v___y_1431_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_1434_, lean_object* v_x_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_){
_start:
{
lean_object* v_res_1440_; 
v_res_1440_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5(v_00_u03b1_1434_, v_x_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
lean_dec(v___y_1438_);
lean_dec_ref(v___y_1437_);
lean_dec(v___y_1436_);
return v_res_1440_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_1441_, lean_object* v_m_1442_, lean_object* v_a_1443_, lean_object* v_b_1444_){
_start:
{
lean_object* v___x_1445_; 
v___x_1445_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6___redArg(v_m_1442_, v_a_1443_, v_b_1444_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_1446_, lean_object* v_a_1447_, lean_object* v_x_1448_){
_start:
{
lean_object* v___x_1449_; 
v___x_1449_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1447_, v_x_1448_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1450_, lean_object* v_a_1451_, lean_object* v_x_1452_){
_start:
{
lean_object* v_res_1453_; 
v_res_1453_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_1450_, v_a_1451_, v_x_1452_);
lean_dec(v_x_1452_);
lean_dec_ref(v_a_1451_);
return v_res_1453_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_1454_, lean_object* v_a_1455_, lean_object* v_x_1456_){
_start:
{
uint8_t v___x_1457_; 
v___x_1457_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1455_, v_x_1456_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___boxed(lean_object* v_00_u03b2_1458_, lean_object* v_a_1459_, lean_object* v_x_1460_){
_start:
{
uint8_t v_res_1461_; lean_object* v_r_1462_; 
v_res_1461_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10(v_00_u03b2_1458_, v_a_1459_, v_x_1460_);
lean_dec(v_x_1460_);
lean_dec_ref(v_a_1459_);
v_r_1462_ = lean_box(v_res_1461_);
return v_r_1462_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_1463_, lean_object* v_data_1464_){
_start:
{
lean_object* v___x_1465_; 
v___x_1465_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11___redArg(v_data_1464_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12(lean_object* v_00_u03b2_1466_, lean_object* v_a_1467_, lean_object* v_b_1468_, lean_object* v_x_1469_){
_start:
{
lean_object* v___x_1470_; 
v___x_1470_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1467_, v_b_1468_, v_x_1469_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12(lean_object* v_00_u03b2_1471_, lean_object* v_i_1472_, lean_object* v_source_1473_, lean_object* v_target_1474_){
_start:
{
lean_object* v___x_1475_; 
v___x_1475_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v_i_1472_, v_source_1473_, v_target_1474_);
return v___x_1475_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_1476_, lean_object* v_x_1477_, lean_object* v_x_1478_){
_start:
{
lean_object* v___x_1479_; 
v___x_1479_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_x_1477_, v_x_1478_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(lean_object* v_declName_1480_, lean_object* v___y_1481_){
_start:
{
lean_object* v___x_1483_; lean_object* v_env_1484_; uint8_t v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1483_ = lean_st_ref_get(v___y_1481_);
v_env_1484_ = lean_ctor_get(v___x_1483_, 0);
lean_inc_ref(v_env_1484_);
lean_dec(v___x_1483_);
v___x_1485_ = l_Lean_isRecCore(v_env_1484_, v_declName_1480_);
v___x_1486_ = lean_box(v___x_1485_);
v___x_1487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1486_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg___boxed(lean_object* v_declName_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
lean_object* v_res_1491_; 
v_res_1491_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(v_declName_1488_, v___y_1489_);
lean_dec(v___y_1489_);
return v_res_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2(lean_object* v_declName_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_){
_start:
{
lean_object* v___x_1498_; 
v___x_1498_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(v_declName_1492_, v___y_1496_);
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___boxed(lean_object* v_declName_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2(v_declName_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(lean_object* v_declName_1506_, lean_object* v___y_1507_){
_start:
{
lean_object* v___x_1509_; lean_object* v_env_1510_; uint8_t v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1509_ = lean_st_ref_get(v___y_1507_);
v_env_1510_ = lean_ctor_get(v___x_1509_, 0);
lean_inc_ref(v_env_1510_);
lean_dec(v___x_1509_);
v___x_1511_ = l_Lean_getReducibilityStatusCore(v_env_1510_, v_declName_1506_);
v___x_1512_ = lean_box(v___x_1511_);
v___x_1513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1512_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg___boxed(lean_object* v_declName_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_){
_start:
{
lean_object* v_res_1517_; 
v_res_1517_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(v_declName_1514_, v___y_1515_);
lean_dec(v___y_1515_);
return v_res_1517_;
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0(lean_object* v_declName_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
lean_object* v___x_1524_; lean_object* v_a_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1540_; 
v___x_1524_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(v_declName_1518_, v___y_1522_);
v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1540_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1527_ = v___x_1524_;
v_isShared_1528_ = v_isSharedCheck_1540_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_a_1525_);
lean_dec(v___x_1524_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1540_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
uint8_t v___x_1529_; 
v___x_1529_ = lean_unbox(v_a_1525_);
lean_dec(v_a_1525_);
if (v___x_1529_ == 0)
{
uint8_t v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1533_; 
v___x_1530_ = 1;
v___x_1531_ = lean_box(v___x_1530_);
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 0, v___x_1531_);
v___x_1533_ = v___x_1527_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v___x_1531_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
else
{
uint8_t v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1538_; 
v___x_1535_ = 0;
v___x_1536_ = lean_box(v___x_1535_);
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 0, v___x_1536_);
v___x_1538_ = v___x_1527_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v___x_1536_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
return v___x_1538_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0___boxed(lean_object* v_declName_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0(v_declName_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
lean_dec(v___y_1545_);
lean_dec_ref(v___y_1544_);
lean_dec(v___y_1543_);
lean_dec_ref(v___y_1542_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(lean_object* v_a_1548_, lean_object* v_b_1549_){
_start:
{
lean_object* v_array_1551_; lean_object* v_start_1552_; lean_object* v_stop_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1570_; 
v_array_1551_ = lean_ctor_get(v_a_1548_, 0);
v_start_1552_ = lean_ctor_get(v_a_1548_, 1);
v_stop_1553_ = lean_ctor_get(v_a_1548_, 2);
v_isSharedCheck_1570_ = !lean_is_exclusive(v_a_1548_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1555_ = v_a_1548_;
v_isShared_1556_ = v_isSharedCheck_1570_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_stop_1553_);
lean_inc(v_start_1552_);
lean_inc(v_array_1551_);
lean_dec(v_a_1548_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1570_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
uint8_t v___x_1557_; 
v___x_1557_ = lean_nat_dec_lt(v_start_1552_, v_stop_1553_);
if (v___x_1557_ == 0)
{
lean_object* v___x_1558_; 
lean_del_object(v___x_1555_);
lean_dec(v_stop_1553_);
lean_dec(v_start_1552_);
lean_dec_ref(v_array_1551_);
v___x_1558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1558_, 0, v_b_1549_);
return v___x_1558_;
}
else
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1563_; 
v___x_1559_ = lean_box(0);
v___x_1560_ = lean_unsigned_to_nat(1u);
v___x_1561_ = lean_nat_add(v_start_1552_, v___x_1560_);
lean_inc_ref(v_array_1551_);
if (v_isShared_1556_ == 0)
{
lean_ctor_set(v___x_1555_, 1, v___x_1561_);
v___x_1563_ = v___x_1555_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_array_1551_);
lean_ctor_set(v_reuseFailAlloc_1569_, 1, v___x_1561_);
lean_ctor_set(v_reuseFailAlloc_1569_, 2, v_stop_1553_);
v___x_1563_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
lean_object* v___x_1564_; uint8_t v___x_1565_; 
v___x_1564_ = lean_array_fget(v_array_1551_, v_start_1552_);
lean_dec(v_start_1552_);
lean_dec_ref(v_array_1551_);
v___x_1565_ = l_Lean_Expr_hasExprMVar(v___x_1564_);
lean_dec(v___x_1564_);
if (v___x_1565_ == 0)
{
v_a_1548_ = v___x_1563_;
v_b_1549_ = v___x_1559_;
goto _start;
}
else
{
lean_object* v___x_1567_; 
v___x_1567_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_dec_ref_known(v___x_1567_, 1);
v_a_1548_ = v___x_1563_;
v_b_1549_ = v___x_1559_;
goto _start;
}
else
{
lean_dec_ref(v___x_1563_);
return v___x_1567_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg___boxed(lean_object* v_a_1571_, lean_object* v_b_1572_, lean_object* v___y_1573_){
_start:
{
lean_object* v_res_1574_; 
v_res_1574_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(v_a_1571_, v_b_1572_);
return v_res_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(lean_object* v_e_1583_, uint8_t v_isMatch_1584_, uint8_t v_root_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_){
_start:
{
lean_object* v___y_1592_; lean_object* v_b_1593_; lean_object* v___x_1604_; 
v___x_1604_ = l_Lean_Meta_DiscrTree_reduceDT(v_e_1583_, v_root_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_);
if (lean_obj_tag(v___x_1604_) == 0)
{
lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1767_; 
v_a_1605_ = lean_ctor_get(v___x_1604_, 0);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1607_ = v___x_1604_;
v_isShared_1608_ = v_isSharedCheck_1767_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_a_1605_);
lean_dec(v___x_1604_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1767_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___y_1610_; lean_object* v___y_1620_; lean_object* v___y_1621_; lean_object* v___y_1622_; lean_object* v___y_1623_; 
if (v_root_1585_ == 0)
{
lean_object* v___x_1755_; 
lean_inc(v_a_1605_);
v___x_1755_ = l_Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f(v_a_1605_);
if (lean_obj_tag(v___x_1755_) == 1)
{
lean_object* v_val_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1766_; 
lean_del_object(v___x_1607_);
lean_dec(v_a_1605_);
v_val_1756_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1758_ = v___x_1755_;
v_isShared_1759_ = v_isSharedCheck_1766_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_val_1756_);
lean_dec(v___x_1755_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1766_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1761_; 
if (v_isShared_1759_ == 0)
{
lean_ctor_set_tag(v___x_1758_, 2);
v___x_1761_ = v___x_1758_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_val_1756_);
v___x_1761_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___x_1762_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
v___x_1763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1761_);
lean_ctor_set(v___x_1763_, 1, v___x_1762_);
v___x_1764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1764_, 0, v___x_1763_);
return v___x_1764_;
}
}
}
else
{
lean_dec(v___x_1755_);
v___y_1620_ = v_a_1586_;
v___y_1621_ = v_a_1587_;
v___y_1622_ = v_a_1588_;
v___y_1623_ = v_a_1589_;
goto v___jp_1619_;
}
}
else
{
v___y_1620_ = v_a_1586_;
v___y_1621_ = v_a_1587_;
v___y_1622_ = v_a_1588_;
v___y_1623_ = v_a_1589_;
goto v___jp_1619_;
}
v___jp_1609_:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1617_; 
v___x_1611_ = l_Lean_Expr_getAppNumArgs(v_a_1605_);
lean_inc(v___x_1611_);
v___x_1612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1612_, 0, v___y_1610_);
lean_ctor_set(v___x_1612_, 1, v___x_1611_);
v___x_1613_ = lean_mk_empty_array_with_capacity(v___x_1611_);
lean_dec(v___x_1611_);
v___x_1614_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1605_, v___x_1613_);
v___x_1615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1612_);
lean_ctor_set(v___x_1615_, 1, v___x_1614_);
if (v_isShared_1608_ == 0)
{
lean_ctor_set(v___x_1607_, 0, v___x_1615_);
v___x_1617_ = v___x_1607_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v___x_1615_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
v___jp_1619_:
{
lean_object* v___x_1624_; 
v___x_1624_ = l_Lean_Expr_getAppFn(v_a_1605_);
switch(lean_obj_tag(v___x_1624_))
{
case 1:
{
lean_object* v_fvarId_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; 
lean_del_object(v___x_1607_);
v_fvarId_1625_ = lean_ctor_get(v___x_1624_, 0);
lean_inc(v_fvarId_1625_);
lean_dec_ref_known(v___x_1624_, 1);
v___x_1626_ = l_Lean_Expr_getAppNumArgs(v_a_1605_);
lean_inc(v___x_1626_);
v___x_1627_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1627_, 0, v_fvarId_1625_);
lean_ctor_set(v___x_1627_, 1, v___x_1626_);
v___x_1628_ = lean_mk_empty_array_with_capacity(v___x_1626_);
lean_dec(v___x_1626_);
v___x_1629_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1605_, v___x_1628_);
v___x_1630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1627_);
lean_ctor_set(v___x_1630_, 1, v___x_1629_);
v___x_1631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1630_);
return v___x_1631_;
}
case 2:
{
lean_del_object(v___x_1607_);
lean_dec(v_a_1605_);
if (v_isMatch_1584_ == 0)
{
lean_object* v_mvarId_1632_; lean_object* v___x_1633_; uint8_t v_isDefEqStuckEx_1634_; 
v_mvarId_1632_ = lean_ctor_get(v___x_1624_, 0);
lean_inc(v_mvarId_1632_);
lean_dec_ref_known(v___x_1624_, 1);
v___x_1633_ = l_Lean_Meta_Context_config(v___y_1620_);
v_isDefEqStuckEx_1634_ = lean_ctor_get_uint8(v___x_1633_, 4);
lean_dec_ref(v___x_1633_);
if (v_isDefEqStuckEx_1634_ == 0)
{
lean_object* v___x_1635_; 
v___x_1635_ = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(v_mvarId_1632_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1649_; 
v_a_1636_ = lean_ctor_get(v___x_1635_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1638_ = v___x_1635_;
v_isShared_1639_ = v_isSharedCheck_1649_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1635_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1649_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
uint8_t v___x_1640_; 
v___x_1640_ = lean_unbox(v_a_1636_);
lean_dec(v_a_1636_);
if (v___x_1640_ == 0)
{
lean_object* v___x_1641_; lean_object* v___x_1643_; 
v___x_1641_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__2));
if (v_isShared_1639_ == 0)
{
lean_ctor_set(v___x_1638_, 0, v___x_1641_);
v___x_1643_ = v___x_1638_;
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
else
{
lean_object* v___x_1645_; lean_object* v___x_1647_; 
v___x_1645_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
if (v_isShared_1639_ == 0)
{
lean_ctor_set(v___x_1638_, 0, v___x_1645_);
v___x_1647_ = v___x_1638_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v___x_1645_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
}
}
else
{
lean_object* v_a_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1657_; 
v_a_1650_ = lean_ctor_get(v___x_1635_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1652_ = v___x_1635_;
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_a_1650_);
lean_dec(v___x_1635_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1655_; 
if (v_isShared_1653_ == 0)
{
v___x_1655_ = v___x_1652_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_a_1650_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
}
}
else
{
lean_object* v___x_1658_; lean_object* v___x_1659_; 
lean_dec(v_mvarId_1632_);
v___x_1658_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__2));
v___x_1659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1658_);
return v___x_1659_;
}
}
else
{
lean_object* v___x_1660_; lean_object* v___x_1661_; 
lean_dec_ref_known(v___x_1624_, 1);
v___x_1660_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
v___x_1661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1661_, 0, v___x_1660_);
return v___x_1661_;
}
}
case 4:
{
lean_object* v_declName_1662_; lean_object* v___x_1663_; uint8_t v_isDefEqStuckEx_1664_; 
v_declName_1662_ = lean_ctor_get(v___x_1624_, 0);
lean_inc(v_declName_1662_);
lean_dec_ref_known(v___x_1624_, 2);
v___x_1663_ = l_Lean_Meta_Context_config(v___y_1620_);
v_isDefEqStuckEx_1664_ = lean_ctor_get_uint8(v___x_1663_, 4);
lean_dec_ref(v___x_1663_);
if (v_isDefEqStuckEx_1664_ == 0)
{
v___y_1610_ = v_declName_1662_;
goto v___jp_1609_;
}
else
{
uint8_t v___x_1665_; 
v___x_1665_ = l_Lean_Expr_hasExprMVar(v_a_1605_);
if (v___x_1665_ == 0)
{
v___y_1610_ = v_declName_1662_;
goto v___jp_1609_;
}
else
{
lean_object* v___x_1666_; 
lean_inc(v_declName_1662_);
v___x_1666_ = l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0(v_declName_1662_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_);
if (lean_obj_tag(v___x_1666_) == 0)
{
lean_object* v_a_1667_; uint8_t v___x_1668_; 
v_a_1667_ = lean_ctor_get(v___x_1666_, 0);
lean_inc(v_a_1667_);
lean_dec_ref_known(v___x_1666_, 1);
v___x_1668_ = lean_unbox(v_a_1667_);
lean_dec(v_a_1667_);
if (v___x_1668_ == 0)
{
lean_object* v___x_1669_; lean_object* v_env_1670_; lean_object* v___x_1671_; 
v___x_1669_ = lean_st_ref_get(v___y_1623_);
v_env_1670_ = lean_ctor_get(v___x_1669_, 0);
lean_inc_ref(v_env_1670_);
lean_dec(v___x_1669_);
v___x_1671_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_1670_, v_a_1605_);
if (lean_obj_tag(v___x_1671_) == 1)
{
lean_object* v_val_1672_; lean_object* v_numDiscrs_1673_; lean_object* v_nargs_1674_; lean_object* v_dummy_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
v_val_1672_ = lean_ctor_get(v___x_1671_, 0);
lean_inc(v_val_1672_);
lean_dec_ref_known(v___x_1671_, 1);
v_numDiscrs_1673_ = lean_ctor_get(v_val_1672_, 1);
lean_inc(v_numDiscrs_1673_);
v_nargs_1674_ = l_Lean_Expr_getAppNumArgs(v_a_1605_);
v_dummy_1675_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0);
lean_inc(v_nargs_1674_);
v___x_1676_ = lean_mk_array(v_nargs_1674_, v_dummy_1675_);
v___x_1677_ = lean_unsigned_to_nat(1u);
v___x_1678_ = lean_nat_sub(v_nargs_1674_, v___x_1677_);
lean_dec(v_nargs_1674_);
lean_inc(v_a_1605_);
v___x_1679_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1605_, v___x_1676_, v___x_1678_);
v___x_1680_ = l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(v_val_1672_);
lean_dec(v_val_1672_);
v___x_1681_ = lean_nat_add(v___x_1680_, v_numDiscrs_1673_);
lean_dec(v_numDiscrs_1673_);
v___x_1682_ = l_Array_toSubarray___redArg(v___x_1679_, v___x_1680_, v___x_1681_);
v___x_1683_ = lean_box(0);
v___x_1684_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(v___x_1682_, v___x_1683_);
if (lean_obj_tag(v___x_1684_) == 0)
{
lean_dec_ref_known(v___x_1684_, 1);
v___y_1610_ = v_declName_1662_;
goto v___jp_1609_;
}
else
{
lean_object* v_a_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1692_; 
lean_dec(v_declName_1662_);
lean_del_object(v___x_1607_);
lean_dec(v_a_1605_);
v_a_1685_ = lean_ctor_get(v___x_1684_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1687_ = v___x_1684_;
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_a_1685_);
lean_dec(v___x_1684_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1690_; 
if (v_isShared_1688_ == 0)
{
v___x_1690_ = v___x_1687_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_a_1685_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
}
else
{
lean_object* v___x_1693_; lean_object* v_a_1694_; uint8_t v___x_1695_; 
lean_dec(v___x_1671_);
lean_inc(v_declName_1662_);
v___x_1693_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(v_declName_1662_, v___y_1623_);
v_a_1694_ = lean_ctor_get(v___x_1693_, 0);
lean_inc(v_a_1694_);
lean_dec_ref(v___x_1693_);
v___x_1695_ = lean_unbox(v_a_1694_);
lean_dec(v_a_1694_);
if (v___x_1695_ == 0)
{
v___y_1610_ = v_declName_1662_;
goto v___jp_1609_;
}
else
{
lean_object* v___x_1696_; 
v___x_1696_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1696_) == 0)
{
lean_dec_ref_known(v___x_1696_, 1);
v___y_1610_ = v_declName_1662_;
goto v___jp_1609_;
}
else
{
lean_object* v_a_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1704_; 
lean_dec(v_declName_1662_);
lean_del_object(v___x_1607_);
lean_dec(v_a_1605_);
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
}
}
else
{
lean_object* v___x_1705_; 
v___x_1705_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_dec_ref_known(v___x_1705_, 1);
v___y_1610_ = v_declName_1662_;
goto v___jp_1609_;
}
else
{
lean_object* v_a_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1713_; 
lean_dec(v_declName_1662_);
lean_del_object(v___x_1607_);
lean_dec(v_a_1605_);
v_a_1706_ = lean_ctor_get(v___x_1705_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1708_ = v___x_1705_;
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_a_1706_);
lean_dec(v___x_1705_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1711_; 
if (v_isShared_1709_ == 0)
{
v___x_1711_ = v___x_1708_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_a_1706_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
return v___x_1711_;
}
}
}
}
}
else
{
lean_object* v_a_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1721_; 
lean_dec(v_declName_1662_);
lean_del_object(v___x_1607_);
lean_dec(v_a_1605_);
v_a_1714_ = lean_ctor_get(v___x_1666_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1716_ = v___x_1666_;
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_a_1714_);
lean_dec(v___x_1666_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1719_; 
if (v_isShared_1717_ == 0)
{
v___x_1719_ = v___x_1716_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_a_1714_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
}
}
}
case 7:
{
lean_object* v_binderType_1722_; lean_object* v_body_1723_; uint8_t v___x_1724_; 
lean_del_object(v___x_1607_);
lean_dec(v_a_1605_);
v_binderType_1722_ = lean_ctor_get(v___x_1624_, 1);
lean_inc_ref(v_binderType_1722_);
v_body_1723_ = lean_ctor_get(v___x_1624_, 2);
lean_inc_ref(v_body_1723_);
lean_dec_ref_known(v___x_1624_, 3);
v___x_1724_ = l_Lean_Expr_hasLooseBVars(v_body_1723_);
if (v___x_1724_ == 0)
{
v___y_1592_ = v_binderType_1722_;
v_b_1593_ = v_body_1723_;
goto v___jp_1591_;
}
else
{
lean_object* v___x_1725_; 
v___x_1725_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(v_body_1723_, v___y_1622_, v___y_1623_);
if (lean_obj_tag(v___x_1725_) == 0)
{
lean_object* v_a_1726_; 
v_a_1726_ = lean_ctor_get(v___x_1725_, 0);
lean_inc(v_a_1726_);
lean_dec_ref_known(v___x_1725_, 1);
v___y_1592_ = v_binderType_1722_;
v_b_1593_ = v_a_1726_;
goto v___jp_1591_;
}
else
{
lean_object* v_a_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1734_; 
lean_dec_ref(v_binderType_1722_);
v_a_1727_ = lean_ctor_get(v___x_1725_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1729_ = v___x_1725_;
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_a_1727_);
lean_dec(v___x_1725_);
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
case 9:
{
lean_object* v_a_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
lean_del_object(v___x_1607_);
lean_dec(v_a_1605_);
v_a_1735_ = lean_ctor_get(v___x_1624_, 0);
lean_inc_ref(v_a_1735_);
lean_dec_ref_known(v___x_1624_, 1);
v___x_1736_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1736_, 0, v_a_1735_);
v___x_1737_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
v___x_1738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1736_);
lean_ctor_set(v___x_1738_, 1, v___x_1737_);
v___x_1739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1738_);
return v___x_1739_;
}
case 11:
{
lean_object* v_typeName_1740_; lean_object* v_idx_1741_; lean_object* v_struct_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; 
lean_del_object(v___x_1607_);
v_typeName_1740_ = lean_ctor_get(v___x_1624_, 0);
lean_inc(v_typeName_1740_);
v_idx_1741_ = lean_ctor_get(v___x_1624_, 1);
lean_inc(v_idx_1741_);
v_struct_1742_ = lean_ctor_get(v___x_1624_, 2);
lean_inc_ref(v_struct_1742_);
lean_dec_ref_known(v___x_1624_, 3);
v___x_1743_ = l_Lean_Expr_getAppNumArgs(v_a_1605_);
lean_inc(v___x_1743_);
v___x_1744_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_1744_, 0, v_typeName_1740_);
lean_ctor_set(v___x_1744_, 1, v_idx_1741_);
lean_ctor_set(v___x_1744_, 2, v___x_1743_);
v___x_1745_ = lean_unsigned_to_nat(1u);
v___x_1746_ = lean_mk_empty_array_with_capacity(v___x_1745_);
v___x_1747_ = lean_array_push(v___x_1746_, v_struct_1742_);
v___x_1748_ = lean_mk_empty_array_with_capacity(v___x_1743_);
lean_dec(v___x_1743_);
v___x_1749_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1605_, v___x_1748_);
v___x_1750_ = l_Array_append___redArg(v___x_1747_, v___x_1749_);
lean_dec_ref(v___x_1749_);
v___x_1751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1744_);
lean_ctor_set(v___x_1751_, 1, v___x_1750_);
v___x_1752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1752_, 0, v___x_1751_);
return v___x_1752_;
}
default: 
{
lean_object* v___x_1753_; lean_object* v___x_1754_; 
lean_dec_ref(v___x_1624_);
lean_del_object(v___x_1607_);
lean_dec(v_a_1605_);
v___x_1753_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
v___x_1754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1753_);
return v___x_1754_;
}
}
}
}
}
else
{
lean_object* v_a_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1775_; 
v_a_1768_ = lean_ctor_get(v___x_1604_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1770_ = v___x_1604_;
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_a_1768_);
lean_dec(v___x_1604_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1773_; 
if (v_isShared_1771_ == 0)
{
v___x_1773_ = v___x_1770_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_a_1768_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
v___jp_1591_:
{
uint8_t v___x_1594_; 
v___x_1594_ = l_Lean_Expr_hasLooseBVars(v_b_1593_);
if (v___x_1594_ == 0)
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1595_ = lean_box(5);
v___x_1596_ = lean_unsigned_to_nat(2u);
v___x_1597_ = lean_mk_empty_array_with_capacity(v___x_1596_);
v___x_1598_ = lean_array_push(v___x_1597_, v___y_1592_);
v___x_1599_ = lean_array_push(v___x_1598_, v_b_1593_);
v___x_1600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1600_, 0, v___x_1595_);
lean_ctor_set(v___x_1600_, 1, v___x_1599_);
v___x_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1600_);
return v___x_1601_;
}
else
{
lean_object* v___x_1602_; lean_object* v___x_1603_; 
lean_dec_ref(v_b_1593_);
lean_dec_ref(v___y_1592_);
v___x_1602_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
v___x_1603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1602_);
return v___x_1603_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___boxed(lean_object* v_e_1776_, lean_object* v_isMatch_1777_, lean_object* v_root_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_){
_start:
{
uint8_t v_isMatch_boxed_1784_; uint8_t v_root_boxed_1785_; lean_object* v_res_1786_; 
v_isMatch_boxed_1784_ = lean_unbox(v_isMatch_1777_);
v_root_boxed_1785_ = lean_unbox(v_root_1778_);
v_res_1786_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_1776_, v_isMatch_boxed_1784_, v_root_boxed_1785_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_);
lean_dec(v_a_1782_);
lean_dec_ref(v_a_1781_);
lean_dec(v_a_1780_);
lean_dec_ref(v_a_1779_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0(lean_object* v_declName_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
lean_object* v___x_1793_; 
v___x_1793_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(v_declName_1787_, v___y_1791_);
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___boxed(lean_object* v_declName_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_){
_start:
{
lean_object* v_res_1800_; 
v_res_1800_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0(v_declName_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_);
lean_dec(v___y_1798_);
lean_dec_ref(v___y_1797_);
lean_dec(v___y_1796_);
lean_dec_ref(v___y_1795_);
return v_res_1800_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1(lean_object* v_inst_1801_, lean_object* v_R_1802_, lean_object* v_a_1803_, lean_object* v_b_1804_, lean_object* v_c_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_){
_start:
{
lean_object* v___x_1811_; 
v___x_1811_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(v_a_1803_, v_b_1804_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___boxed(lean_object* v_inst_1812_, lean_object* v_R_1813_, lean_object* v_a_1814_, lean_object* v_b_1815_, lean_object* v_c_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
lean_object* v_res_1822_; 
v_res_1822_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1(v_inst_1812_, v_R_1813_, v_a_1814_, v_b_1815_, v_c_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
lean_dec(v___y_1820_);
lean_dec_ref(v___y_1819_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
return v_res_1822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getMatchKeyArgs(lean_object* v_e_1823_, uint8_t v_root_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_){
_start:
{
uint8_t v___x_1830_; lean_object* v___x_1831_; 
v___x_1830_ = 1;
v___x_1831_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_1823_, v___x_1830_, v_root_1824_, v_a_1825_, v_a_1826_, v_a_1827_, v_a_1828_);
return v___x_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getMatchKeyArgs___boxed(lean_object* v_e_1832_, lean_object* v_root_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_){
_start:
{
uint8_t v_root_boxed_1839_; lean_object* v_res_1840_; 
v_root_boxed_1839_ = lean_unbox(v_root_1833_);
v_res_1840_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getMatchKeyArgs(v_e_1832_, v_root_boxed_1839_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_);
lean_dec(v_a_1837_);
lean_dec_ref(v_a_1836_);
lean_dec(v_a_1835_);
lean_dec_ref(v_a_1834_);
return v_res_1840_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__1(void){
_start:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1843_ = lean_box(0);
v___x_1844_ = lean_unsigned_to_nat(16u);
v___x_1845_ = lean_mk_array(v___x_1844_, v___x_1843_);
return v___x_1845_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2(void){
_start:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1846_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__1);
v___x_1847_ = lean_unsigned_to_nat(0u);
v___x_1848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1847_);
lean_ctor_set(v___x_1848_, 1, v___x_1846_);
return v___x_1848_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__4(void){
_start:
{
lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___x_1851_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__3));
v___x_1852_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2);
v___x_1853_ = lean_unsigned_to_nat(0u);
v___x_1854_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__0));
v___x_1855_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1854_);
lean_ctor_set(v___x_1855_, 1, v___x_1853_);
lean_ctor_set(v___x_1855_, 2, v___x_1852_);
lean_ctor_set(v___x_1855_, 3, v___x_1851_);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg(){
_start:
{
lean_object* v___x_1857_; 
v___x_1857_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__4);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___boxed(lean_object* v___dummy_1858_){
_start:
{
lean_object* v_res_1859_; 
v_res_1859_ = l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg();
return v_res_1859_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0(void){
_start:
{
lean_object* v___x_1860_; 
v___x_1860_ = l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg();
return v___x_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default(lean_object* v_00_u03b1_1861_){
_start:
{
lean_object* v___x_1862_; 
v___x_1862_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___redArg(){
_start:
{
lean_object* v___x_1864_; 
v___x_1864_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___redArg___boxed(lean_object* v___dummy_1865_){
_start:
{
lean_object* v_res_1866_; 
v_res_1866_ = l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___redArg();
return v_res_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie(lean_object* v_a_1867_){
_start:
{
lean_object* v___x_1868_; 
v___x_1868_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0);
return v___x_1868_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__1(void){
_start:
{
lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1871_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2);
v___x_1872_ = lean_unsigned_to_nat(0u);
v___x_1873_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___x_1874_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1873_);
lean_ctor_set(v___x_1874_, 1, v___x_1872_);
lean_ctor_set(v___x_1874_, 2, v___x_1871_);
lean_ctor_set(v___x_1874_, 3, v___x_1873_);
return v___x_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg(){
_start:
{
lean_object* v___x_1876_; 
v___x_1876_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__1);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___boxed(lean_object* v___dummy_1877_){
_start:
{
lean_object* v_res_1878_; 
v_res_1878_ = l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg();
return v_res_1878_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0(void){
_start:
{
lean_object* v___x_1879_; 
v___x_1879_ = l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg();
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie(lean_object* v_00_u03b1_1880_){
_start:
{
lean_object* v___x_1881_; 
v___x_1881_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0, &l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0);
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
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__0(void){
_start:
{
lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1900_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0);
v___x_1901_ = lean_unsigned_to_nat(1u);
v___x_1902_ = lean_mk_empty_array_with_capacity(v___x_1901_);
v___x_1903_ = lean_array_push(v___x_1902_, v___x_1900_);
return v___x_1903_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__1(void){
_start:
{
lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1904_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2);
v___x_1905_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__0);
v___x_1906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1906_, 0, v___x_1905_);
lean_ctor_set(v___x_1906_, 1, v___x_1904_);
return v___x_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabited___redArg(){
_start:
{
lean_object* v___x_1908_; 
v___x_1908_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__1);
return v___x_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___boxed(lean_object* v___dummy_1909_){
_start:
{
lean_object* v_res_1910_; 
v_res_1910_ = l_Lean_Meta_LazyDiscrTree_instInhabited___redArg();
return v_res_1910_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_1911_; 
v___x_1911_ = l_Lean_Meta_LazyDiscrTree_instInhabited___redArg();
return v___x_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabited(lean_object* v_00_u03b1_1912_){
_start:
{
lean_object* v___x_1913_; 
v___x_1913_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0);
return v___x_1913_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(lean_object* v_msgData_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_){
_start:
{
lean_object* v___x_1920_; lean_object* v_env_1921_; uint8_t v___x_1922_; lean_object* v_env_1923_; lean_object* v___x_1924_; lean_object* v_toCold_1925_; lean_object* v_mctx_1926_; lean_object* v_lctx_1927_; lean_object* v_options_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1920_ = lean_st_ref_get(v___y_1918_);
v_env_1921_ = lean_ctor_get(v___x_1920_, 0);
lean_inc_ref(v_env_1921_);
lean_dec(v___x_1920_);
v___x_1922_ = 0;
v_env_1923_ = l_Lean_Environment_setRecordingDeps(v_env_1921_, v___x_1922_);
v___x_1924_ = lean_st_ref_get(v___y_1916_);
v_toCold_1925_ = lean_ctor_get(v___y_1917_, 0);
v_mctx_1926_ = lean_ctor_get(v___x_1924_, 0);
lean_inc_ref(v_mctx_1926_);
lean_dec(v___x_1924_);
v_lctx_1927_ = lean_ctor_get(v___y_1915_, 2);
v_options_1928_ = lean_ctor_get(v_toCold_1925_, 2);
lean_inc_ref(v_options_1928_);
lean_inc_ref(v_lctx_1927_);
v___x_1929_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1929_, 0, v_env_1923_);
lean_ctor_set(v___x_1929_, 1, v_mctx_1926_);
lean_ctor_set(v___x_1929_, 2, v_lctx_1927_);
lean_ctor_set(v___x_1929_, 3, v_options_1928_);
v___x_1930_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1930_, 0, v___x_1929_);
lean_ctor_set(v___x_1930_, 1, v_msgData_1914_);
v___x_1931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1930_);
return v___x_1931_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0___boxed(lean_object* v_msgData_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_){
_start:
{
lean_object* v_res_1938_; 
v_res_1938_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(v_msgData_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
lean_dec(v___y_1936_);
lean_dec_ref(v___y_1935_);
lean_dec(v___y_1934_);
lean_dec_ref(v___y_1933_);
return v_res_1938_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(lean_object* v_msg_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_){
_start:
{
lean_object* v_ref_1945_; lean_object* v___x_1946_; lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1955_; 
v_ref_1945_ = lean_ctor_get(v___y_1942_, 2);
v___x_1946_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(v_msg_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1949_ = v___x_1946_;
v_isShared_1950_ = v_isSharedCheck_1955_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1946_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1955_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1951_; lean_object* v___x_1953_; 
lean_inc(v_ref_1945_);
v___x_1951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1951_, 0, v_ref_1945_);
lean_ctor_set(v___x_1951_, 1, v_a_1947_);
if (v_isShared_1950_ == 0)
{
lean_ctor_set_tag(v___x_1949_, 1);
lean_ctor_set(v___x_1949_, 0, v___x_1951_);
v___x_1953_ = v___x_1949_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v___x_1951_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg___boxed(lean_object* v_msg_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_){
_start:
{
lean_object* v_res_1962_; 
v_res_1962_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(v_msg_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
return v_res_1962_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1(void){
_start:
{
lean_object* v___x_1964_; lean_object* v___x_1965_; 
v___x_1964_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_pushArgs___closed__0));
v___x_1965_ = l_Lean_stringToMessageData(v___x_1964_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushArgs(uint8_t v_root_1966_, lean_object* v_todo_1967_, lean_object* v_e_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_){
_start:
{
lean_object* v_v_1975_; uint8_t v___x_1979_; 
v___x_1979_ = l_Lean_Meta_DiscrTree_hasNoindexAnnotation(v_e_1968_);
if (v___x_1979_ == 0)
{
lean_object* v___x_1980_; 
v___x_1980_ = l_Lean_Meta_DiscrTree_reduceDT(v_e_1968_, v_root_1966_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_);
if (lean_obj_tag(v___x_1980_) == 0)
{
lean_object* v_a_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_2123_; 
v_a_1981_ = lean_ctor_get(v___x_1980_, 0);
v_isSharedCheck_2123_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_1983_ = v___x_1980_;
v_isShared_1984_ = v_isSharedCheck_2123_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_a_1981_);
lean_dec(v___x_1980_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_2123_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1985_; lean_object* v_k_1987_; lean_object* v_nargs_1988_; lean_object* v_todo_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; 
v___x_1985_ = l_Lean_Expr_getAppFn(v_a_1981_);
switch(lean_obj_tag(v___x_1985_))
{
case 9:
{
lean_object* v_a_2032_; 
lean_del_object(v___x_1983_);
lean_dec(v_a_1981_);
v_a_2032_ = lean_ctor_get(v___x_1985_, 0);
lean_inc_ref(v_a_2032_);
lean_dec_ref_known(v___x_1985_, 1);
v_v_1975_ = v_a_2032_;
goto v___jp_1974_;
}
case 4:
{
lean_object* v_declName_2033_; lean_object* v___y_2035_; lean_object* v___y_2036_; lean_object* v___y_2037_; lean_object* v___y_2038_; 
lean_del_object(v___x_1983_);
v_declName_2033_ = lean_ctor_get(v___x_1985_, 0);
if (v_root_1966_ == 0)
{
lean_object* v___x_2041_; 
lean_inc(v_a_1981_);
v___x_2041_ = l_Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f(v_a_1981_);
if (lean_obj_tag(v___x_2041_) == 1)
{
lean_object* v_val_2042_; 
lean_dec_ref_known(v___x_1985_, 2);
lean_dec(v_a_1981_);
v_val_2042_ = lean_ctor_get(v___x_2041_, 0);
lean_inc(v_val_2042_);
lean_dec_ref_known(v___x_2041_, 1);
v_v_1975_ = v_val_2042_;
goto v___jp_1974_;
}
else
{
lean_object* v___x_2043_; 
lean_dec(v___x_2041_);
v___x_2043_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset(v_declName_2033_, v_a_1981_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_);
if (lean_obj_tag(v___x_2043_) == 0)
{
lean_object* v_a_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2054_; 
v_a_2044_ = lean_ctor_get(v___x_2043_, 0);
v_isSharedCheck_2054_ = !lean_is_exclusive(v___x_2043_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2046_ = v___x_2043_;
v_isShared_2047_ = v_isSharedCheck_2054_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_a_2044_);
lean_dec(v___x_2043_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2054_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
uint8_t v___x_2048_; 
v___x_2048_ = lean_unbox(v_a_2044_);
lean_dec(v_a_2044_);
if (v___x_2048_ == 0)
{
lean_del_object(v___x_2046_);
v___y_2035_ = v_a_1969_;
v___y_2036_ = v_a_1970_;
v___y_2037_ = v_a_1971_;
v___y_2038_ = v_a_1972_;
goto v___jp_2034_;
}
else
{
lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2052_; 
lean_dec_ref_known(v___x_1985_, 2);
lean_dec(v_a_1981_);
v___x_2049_ = lean_box(3);
v___x_2050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2050_, 0, v___x_2049_);
lean_ctor_set(v___x_2050_, 1, v_todo_1967_);
if (v_isShared_2047_ == 0)
{
lean_ctor_set(v___x_2046_, 0, v___x_2050_);
v___x_2052_ = v___x_2046_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v___x_2050_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
}
}
else
{
lean_object* v_a_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2062_; 
lean_dec_ref_known(v___x_1985_, 2);
lean_dec(v_a_1981_);
lean_dec_ref(v_todo_1967_);
v_a_2055_ = lean_ctor_get(v___x_2043_, 0);
v_isSharedCheck_2062_ = !lean_is_exclusive(v___x_2043_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2057_ = v___x_2043_;
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_a_2055_);
lean_dec(v___x_2043_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2060_; 
if (v_isShared_2058_ == 0)
{
v___x_2060_ = v___x_2057_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v_a_2055_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
return v___x_2060_;
}
}
}
}
}
else
{
v___y_2035_ = v_a_1969_;
v___y_2036_ = v_a_1970_;
v___y_2037_ = v_a_1971_;
v___y_2038_ = v_a_1972_;
goto v___jp_2034_;
}
v___jp_2034_:
{
lean_object* v___x_2039_; lean_object* v___x_2040_; 
v___x_2039_ = l_Lean_Expr_getAppNumArgs(v_a_1981_);
lean_inc(v___x_2039_);
lean_inc(v_declName_2033_);
v___x_2040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2040_, 0, v_declName_2033_);
lean_ctor_set(v___x_2040_, 1, v___x_2039_);
v_k_1987_ = v___x_2040_;
v_nargs_1988_ = v___x_2039_;
v_todo_1989_ = v_todo_1967_;
v___y_1990_ = v___y_2035_;
v___y_1991_ = v___y_2036_;
v___y_1992_ = v___y_2037_;
v___y_1993_ = v___y_2038_;
goto v___jp_1986_;
}
}
case 11:
{
lean_object* v_typeName_2063_; lean_object* v_idx_2064_; lean_object* v_struct_2065_; lean_object* v___x_2066_; lean_object* v___y_2068_; lean_object* v_env_2072_; uint8_t v___x_2073_; 
lean_del_object(v___x_1983_);
v_typeName_2063_ = lean_ctor_get(v___x_1985_, 0);
v_idx_2064_ = lean_ctor_get(v___x_1985_, 1);
v_struct_2065_ = lean_ctor_get(v___x_1985_, 2);
v___x_2066_ = lean_st_ref_get(v_a_1972_);
v_env_2072_ = lean_ctor_get(v___x_2066_, 0);
lean_inc_ref(v_env_2072_);
lean_dec(v___x_2066_);
v___x_2073_ = l_Lean_isClass(v_env_2072_, v_typeName_2063_);
if (v___x_2073_ == 0)
{
lean_inc_ref(v_struct_2065_);
v___y_2068_ = v_struct_2065_;
goto v___jp_2067_;
}
else
{
lean_object* v___x_2074_; 
lean_inc_ref(v_struct_2065_);
v___x_2074_ = l_Lean_Meta_DiscrTree_mkNoindexAnnotation(v_struct_2065_);
v___y_2068_ = v___x_2074_;
goto v___jp_2067_;
}
v___jp_2067_:
{
lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; 
v___x_2069_ = l_Lean_Expr_getAppNumArgs(v_a_1981_);
lean_inc(v___x_2069_);
lean_inc(v_idx_2064_);
lean_inc(v_typeName_2063_);
v___x_2070_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_2070_, 0, v_typeName_2063_);
lean_ctor_set(v___x_2070_, 1, v_idx_2064_);
lean_ctor_set(v___x_2070_, 2, v___x_2069_);
v___x_2071_ = lean_array_push(v_todo_1967_, v___y_2068_);
v_k_1987_ = v___x_2070_;
v_nargs_1988_ = v___x_2069_;
v_todo_1989_ = v___x_2071_;
v___y_1990_ = v_a_1969_;
v___y_1991_ = v_a_1970_;
v___y_1992_ = v_a_1971_;
v___y_1993_ = v_a_1972_;
goto v___jp_1986_;
}
}
case 1:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2078_; 
lean_dec_ref_known(v___x_1985_, 1);
lean_dec(v_a_1981_);
v___x_2075_ = lean_box(3);
v___x_2076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2075_);
lean_ctor_set(v___x_2076_, 1, v_todo_1967_);
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 0, v___x_2076_);
v___x_2078_ = v___x_1983_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v___x_2076_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
case 2:
{
lean_object* v_mvarId_2080_; lean_object* v___x_2081_; uint8_t v___x_2082_; 
lean_dec(v_a_1981_);
v_mvarId_2080_ = lean_ctor_get(v___x_1985_, 0);
lean_inc(v_mvarId_2080_);
lean_dec_ref_known(v___x_1985_, 1);
v___x_2081_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_tmpMVarId));
v___x_2082_ = l_Lean_instBEqMVarId_beq(v_mvarId_2080_, v___x_2081_);
lean_dec(v_mvarId_2080_);
if (v___x_2082_ == 0)
{
lean_object* v___x_2083_; lean_object* v___x_2084_; 
lean_del_object(v___x_1983_);
lean_dec_ref(v_todo_1967_);
v___x_2083_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1, &l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1);
v___x_2084_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(v___x_2083_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_);
return v___x_2084_;
}
else
{
lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2088_; 
v___x_2085_ = lean_box(3);
v___x_2086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2085_);
lean_ctor_set(v___x_2086_, 1, v_todo_1967_);
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 0, v___x_2086_);
v___x_2088_ = v___x_1983_;
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
}
case 7:
{
lean_object* v_binderType_2090_; lean_object* v_body_2091_; lean_object* v_b_2093_; uint8_t v___x_2107_; 
lean_dec(v_a_1981_);
v_binderType_2090_ = lean_ctor_get(v___x_1985_, 1);
lean_inc_ref(v_binderType_2090_);
v_body_2091_ = lean_ctor_get(v___x_1985_, 2);
lean_inc_ref(v_body_2091_);
lean_dec_ref_known(v___x_1985_, 3);
v___x_2107_ = l_Lean_Expr_hasLooseBVars(v_body_2091_);
if (v___x_2107_ == 0)
{
v_b_2093_ = v_body_2091_;
goto v___jp_2092_;
}
else
{
lean_object* v___x_2108_; 
v___x_2108_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(v_body_2091_, v_a_1971_, v_a_1972_);
if (lean_obj_tag(v___x_2108_) == 0)
{
lean_object* v_a_2109_; 
v_a_2109_ = lean_ctor_get(v___x_2108_, 0);
lean_inc(v_a_2109_);
lean_dec_ref_known(v___x_2108_, 1);
v_b_2093_ = v_a_2109_;
goto v___jp_2092_;
}
else
{
lean_object* v_a_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2117_; 
lean_dec_ref(v_binderType_2090_);
lean_del_object(v___x_1983_);
lean_dec_ref(v_todo_1967_);
v_a_2110_ = lean_ctor_get(v___x_2108_, 0);
v_isSharedCheck_2117_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2112_ = v___x_2108_;
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_a_2110_);
lean_dec(v___x_2108_);
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
v___jp_2092_:
{
uint8_t v___x_2094_; 
v___x_2094_ = l_Lean_Expr_hasLooseBVars(v_b_2093_);
if (v___x_2094_ == 0)
{
lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2100_; 
v___x_2095_ = lean_box(5);
v___x_2096_ = lean_array_push(v_todo_1967_, v_binderType_2090_);
v___x_2097_ = lean_array_push(v___x_2096_, v_b_2093_);
v___x_2098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2095_);
lean_ctor_set(v___x_2098_, 1, v___x_2097_);
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 0, v___x_2098_);
v___x_2100_ = v___x_1983_;
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
else
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2105_; 
lean_dec_ref(v_b_2093_);
lean_dec_ref(v_binderType_2090_);
v___x_2102_ = lean_box(4);
v___x_2103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2103_, 0, v___x_2102_);
lean_ctor_set(v___x_2103_, 1, v_todo_1967_);
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 0, v___x_2103_);
v___x_2105_ = v___x_1983_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v___x_2103_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
return v___x_2105_;
}
}
}
}
default: 
{
lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2121_; 
lean_dec_ref(v___x_1985_);
lean_dec(v_a_1981_);
v___x_2118_ = lean_box(4);
v___x_2119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2118_);
lean_ctor_set(v___x_2119_, 1, v_todo_1967_);
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 0, v___x_2119_);
v___x_2121_ = v___x_1983_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v___x_2119_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
return v___x_2121_;
}
}
}
v___jp_1986_:
{
lean_object* v___x_1994_; 
lean_inc(v_nargs_1988_);
v___x_1994_ = l_Lean_Meta_getFunInfoNArgs(v___x_1985_, v_nargs_1988_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
if (lean_obj_tag(v___x_1994_) == 0)
{
lean_object* v_a_1995_; lean_object* v_paramInfo_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2022_; 
v_a_1995_ = lean_ctor_get(v___x_1994_, 0);
lean_inc(v_a_1995_);
lean_dec_ref_known(v___x_1994_, 1);
v_paramInfo_1996_ = lean_ctor_get(v_a_1995_, 0);
v_isSharedCheck_2022_ = !lean_is_exclusive(v_a_1995_);
if (v_isSharedCheck_2022_ == 0)
{
lean_object* v_unused_2023_; 
v_unused_2023_ = lean_ctor_get(v_a_1995_, 1);
lean_dec(v_unused_2023_);
v___x_1998_ = v_a_1995_;
v_isShared_1999_ = v_isSharedCheck_2022_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_paramInfo_1996_);
lean_dec(v_a_1995_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2022_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; 
v___x_2000_ = lean_unsigned_to_nat(1u);
v___x_2001_ = lean_nat_sub(v_nargs_1988_, v___x_2000_);
lean_dec(v_nargs_1988_);
v___x_2002_ = l_Lean_Meta_LazyDiscrTree_MatchClone_pushArgsAux(v_paramInfo_1996_, v___x_2001_, v_a_1981_, v_todo_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
lean_dec_ref(v_paramInfo_1996_);
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_object* v_a_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2013_; 
v_a_2003_ = lean_ctor_get(v___x_2002_, 0);
v_isSharedCheck_2013_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2013_ == 0)
{
v___x_2005_ = v___x_2002_;
v_isShared_2006_ = v_isSharedCheck_2013_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_a_2003_);
lean_dec(v___x_2002_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2013_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2008_; 
if (v_isShared_1999_ == 0)
{
lean_ctor_set(v___x_1998_, 1, v_a_2003_);
lean_ctor_set(v___x_1998_, 0, v_k_1987_);
v___x_2008_ = v___x_1998_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v_k_1987_);
lean_ctor_set(v_reuseFailAlloc_2012_, 1, v_a_2003_);
v___x_2008_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
lean_object* v___x_2010_; 
if (v_isShared_2006_ == 0)
{
lean_ctor_set(v___x_2005_, 0, v___x_2008_);
v___x_2010_ = v___x_2005_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v___x_2008_);
v___x_2010_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
return v___x_2010_;
}
}
}
}
else
{
lean_object* v_a_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2021_; 
lean_del_object(v___x_1998_);
lean_dec(v_k_1987_);
v_a_2014_ = lean_ctor_get(v___x_2002_, 0);
v_isSharedCheck_2021_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_2016_ = v___x_2002_;
v_isShared_2017_ = v_isSharedCheck_2021_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_a_2014_);
lean_dec(v___x_2002_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2021_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v___x_2019_; 
if (v_isShared_2017_ == 0)
{
v___x_2019_ = v___x_2016_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v_a_2014_);
v___x_2019_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
return v___x_2019_;
}
}
}
}
}
else
{
lean_object* v_a_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2031_; 
lean_dec_ref(v_todo_1989_);
lean_dec(v_nargs_1988_);
lean_dec(v_k_1987_);
lean_dec(v_a_1981_);
v_a_2024_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_2026_ = v___x_1994_;
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_a_2024_);
lean_dec(v___x_1994_);
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
}
else
{
lean_object* v_a_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2131_; 
lean_dec_ref(v_todo_1967_);
v_a_2124_ = lean_ctor_get(v___x_1980_, 0);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2126_ = v___x_1980_;
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_a_2124_);
lean_dec(v___x_1980_);
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
else
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
lean_dec_ref(v_e_1968_);
v___x_2132_ = lean_box(3);
v___x_2133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2132_);
lean_ctor_set(v___x_2133_, 1, v_todo_1967_);
v___x_2134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2133_);
return v___x_2134_;
}
v___jp_1974_:
{
lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1976_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1976_, 0, v_v_1975_);
v___x_1977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1977_, 0, v___x_1976_);
lean_ctor_set(v___x_1977_, 1, v_todo_1967_);
v___x_1978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1977_);
return v___x_1978_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushArgs___boxed(lean_object* v_root_2135_, lean_object* v_todo_2136_, lean_object* v_e_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_){
_start:
{
uint8_t v_root_boxed_2143_; lean_object* v_res_2144_; 
v_root_boxed_2143_ = lean_unbox(v_root_2135_);
v_res_2144_ = l_Lean_Meta_LazyDiscrTree_pushArgs(v_root_boxed_2143_, v_todo_2136_, v_e_2137_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_);
lean_dec(v_a_2141_);
lean_dec_ref(v_a_2140_);
lean_dec(v_a_2139_);
lean_dec_ref(v_a_2138_);
return v_res_2144_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0(lean_object* v_00_u03b1_2145_, lean_object* v_msg_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_){
_start:
{
lean_object* v___x_2152_; 
v___x_2152_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(v_msg_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___boxed(lean_object* v_00_u03b1_2153_, lean_object* v_msg_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_){
_start:
{
lean_object* v_res_2160_; 
v_res_2160_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0(v_00_u03b1_2153_, v_msg_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2155_);
return v_res_2160_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_initCapacity(void){
_start:
{
lean_object* v___x_2161_; 
v___x_2161_ = lean_unsigned_to_nat(8u);
return v___x_2161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_rootKey(lean_object* v_e_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_){
_start:
{
uint8_t v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2168_ = 1;
v___x_2169_ = lean_unsigned_to_nat(8u);
v___x_2170_ = lean_mk_empty_array_with_capacity(v___x_2169_);
v___x_2171_ = l_Lean_Meta_LazyDiscrTree_pushArgs(v___x_2168_, v___x_2170_, v_e_2162_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_);
return v___x_2171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_rootKey___boxed(lean_object* v_e_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_){
_start:
{
lean_object* v_res_2178_; 
v_res_2178_ = l_Lean_Meta_LazyDiscrTree_rootKey(v_e_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_);
lean_dec(v_a_2176_);
lean_dec_ref(v_a_2175_);
lean_dec(v_a_2174_);
lean_dec_ref(v_a_2173_);
return v_res_2178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_buildPath(lean_object* v_op_2179_, uint8_t v_root_2180_, lean_object* v_todo_2181_, lean_object* v_keys_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_){
_start:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; uint8_t v___x_2190_; 
v___x_2188_ = lean_array_get_size(v_todo_2181_);
v___x_2189_ = lean_unsigned_to_nat(0u);
v___x_2190_ = lean_nat_dec_eq(v___x_2188_, v___x_2189_);
if (v___x_2190_ == 0)
{
lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v_e_2194_; lean_object* v_todo_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2191_ = l_Lean_instInhabitedExpr;
v___x_2192_ = lean_unsigned_to_nat(1u);
v___x_2193_ = lean_nat_sub(v___x_2188_, v___x_2192_);
v_e_2194_ = lean_array_get(v___x_2191_, v_todo_2181_, v___x_2193_);
lean_dec(v___x_2193_);
v_todo_2195_ = lean_array_pop(v_todo_2181_);
v___x_2196_ = lean_box(v_root_2180_);
lean_inc_ref(v_op_2179_);
lean_inc(v_a_2186_);
lean_inc_ref(v_a_2185_);
lean_inc(v_a_2184_);
lean_inc_ref(v_a_2183_);
v___x_2197_ = lean_apply_8(v_op_2179_, v___x_2196_, v_todo_2195_, v_e_2194_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, lean_box(0));
if (lean_obj_tag(v___x_2197_) == 0)
{
lean_object* v_a_2198_; lean_object* v_fst_2199_; lean_object* v_snd_2200_; lean_object* v___x_2201_; 
v_a_2198_ = lean_ctor_get(v___x_2197_, 0);
lean_inc(v_a_2198_);
lean_dec_ref_known(v___x_2197_, 1);
v_fst_2199_ = lean_ctor_get(v_a_2198_, 0);
lean_inc(v_fst_2199_);
v_snd_2200_ = lean_ctor_get(v_a_2198_, 1);
lean_inc(v_snd_2200_);
lean_dec(v_a_2198_);
v___x_2201_ = lean_array_push(v_keys_2182_, v_fst_2199_);
v_root_2180_ = v___x_2190_;
v_todo_2181_ = v_snd_2200_;
v_keys_2182_ = v___x_2201_;
goto _start;
}
else
{
lean_object* v_a_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2210_; 
lean_dec_ref(v_keys_2182_);
lean_dec_ref(v_op_2179_);
v_a_2203_ = lean_ctor_get(v___x_2197_, 0);
v_isSharedCheck_2210_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2205_ = v___x_2197_;
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_a_2203_);
lean_dec(v___x_2197_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___x_2208_; 
if (v_isShared_2206_ == 0)
{
v___x_2208_ = v___x_2205_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v_a_2203_);
v___x_2208_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
return v___x_2208_;
}
}
}
}
else
{
lean_object* v___x_2211_; 
lean_dec_ref(v_todo_2181_);
lean_dec_ref(v_op_2179_);
v___x_2211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2211_, 0, v_keys_2182_);
return v___x_2211_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_buildPath___boxed(lean_object* v_op_2212_, lean_object* v_root_2213_, lean_object* v_todo_2214_, lean_object* v_keys_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_){
_start:
{
uint8_t v_root_boxed_2221_; lean_object* v_res_2222_; 
v_root_boxed_2221_ = lean_unbox(v_root_2213_);
v_res_2222_ = l_Lean_Meta_LazyDiscrTree_buildPath(v_op_2212_, v_root_boxed_2221_, v_todo_2214_, v_keys_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_);
lean_dec(v_a_2219_);
lean_dec_ref(v_a_2218_);
lean_dec(v_a_2217_);
lean_dec_ref(v_a_2216_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_patternPath(lean_object* v_e_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_){
_start:
{
lean_object* v_op_2230_; lean_object* v___x_2231_; lean_object* v_todo_2232_; uint8_t v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; 
v_op_2230_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_patternPath___closed__0));
v___x_2231_ = lean_unsigned_to_nat(8u);
v_todo_2232_ = lean_mk_empty_array_with_capacity(v___x_2231_);
v___x_2233_ = 1;
lean_inc_ref(v_todo_2232_);
v___x_2234_ = lean_array_push(v_todo_2232_, v_e_2224_);
v___x_2235_ = l_Lean_Meta_LazyDiscrTree_buildPath(v_op_2230_, v___x_2233_, v___x_2234_, v_todo_2232_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
return v___x_2235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_patternPath___boxed(lean_object* v_e_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_){
_start:
{
lean_object* v_res_2242_; 
v_res_2242_ = l_Lean_Meta_LazyDiscrTree_patternPath(v_e_2236_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_);
lean_dec(v_a_2240_);
lean_dec_ref(v_a_2239_);
lean_dec(v_a_2238_);
lean_dec_ref(v_a_2237_);
return v_res_2242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath___lam__0(uint8_t v_root_2243_, lean_object* v_todo_2244_, lean_object* v_e_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_){
_start:
{
uint8_t v___x_2251_; lean_object* v___x_2252_; 
v___x_2251_ = 1;
v___x_2252_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_2245_, v___x_2251_, v_root_2243_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_);
if (lean_obj_tag(v___x_2252_) == 0)
{
lean_object* v_a_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2270_; 
v_a_2253_ = lean_ctor_get(v___x_2252_, 0);
v_isSharedCheck_2270_ = !lean_is_exclusive(v___x_2252_);
if (v_isSharedCheck_2270_ == 0)
{
v___x_2255_ = v___x_2252_;
v_isShared_2256_ = v_isSharedCheck_2270_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_a_2253_);
lean_dec(v___x_2252_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2270_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v_fst_2257_; lean_object* v_snd_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2269_; 
v_fst_2257_ = lean_ctor_get(v_a_2253_, 0);
v_snd_2258_ = lean_ctor_get(v_a_2253_, 1);
v_isSharedCheck_2269_ = !lean_is_exclusive(v_a_2253_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2260_ = v_a_2253_;
v_isShared_2261_ = v_isSharedCheck_2269_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_snd_2258_);
lean_inc(v_fst_2257_);
lean_dec(v_a_2253_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2269_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
lean_object* v___x_2262_; lean_object* v___x_2264_; 
v___x_2262_ = l_Array_append___redArg(v_todo_2244_, v_snd_2258_);
lean_dec(v_snd_2258_);
if (v_isShared_2261_ == 0)
{
lean_ctor_set(v___x_2260_, 1, v___x_2262_);
v___x_2264_ = v___x_2260_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v_fst_2257_);
lean_ctor_set(v_reuseFailAlloc_2268_, 1, v___x_2262_);
v___x_2264_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
lean_object* v___x_2266_; 
if (v_isShared_2256_ == 0)
{
lean_ctor_set(v___x_2255_, 0, v___x_2264_);
v___x_2266_ = v___x_2255_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v___x_2264_);
v___x_2266_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
return v___x_2266_;
}
}
}
}
}
else
{
lean_dec_ref(v_todo_2244_);
return v___x_2252_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath___lam__0___boxed(lean_object* v_root_2271_, lean_object* v_todo_2272_, lean_object* v_e_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_){
_start:
{
uint8_t v_root_boxed_2279_; lean_object* v_res_2280_; 
v_root_boxed_2279_ = lean_unbox(v_root_2271_);
v_res_2280_ = l_Lean_Meta_LazyDiscrTree_targetPath___lam__0(v_root_boxed_2279_, v_todo_2272_, v_e_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_);
lean_dec(v___y_2277_);
lean_dec_ref(v___y_2276_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
return v_res_2280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath(lean_object* v_e_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_){
_start:
{
lean_object* v_op_2288_; lean_object* v___x_2289_; lean_object* v_todo_2290_; uint8_t v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; 
v_op_2288_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_targetPath___closed__0));
v___x_2289_ = lean_unsigned_to_nat(8u);
v_todo_2290_ = lean_mk_empty_array_with_capacity(v___x_2289_);
v___x_2291_ = 1;
lean_inc_ref(v_todo_2290_);
v___x_2292_ = lean_array_push(v_todo_2290_, v_e_2282_);
v___x_2293_ = l_Lean_Meta_LazyDiscrTree_buildPath(v_op_2288_, v___x_2291_, v___x_2292_, v_todo_2290_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_);
return v___x_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath___boxed(lean_object* v_e_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_){
_start:
{
lean_object* v_res_2300_; 
v_res_2300_ = l_Lean_Meta_LazyDiscrTree_targetPath(v_e_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_);
lean_dec(v_a_2298_);
lean_dec_ref(v_a_2297_);
lean_dec(v_a_2296_);
lean_dec_ref(v_a_2295_);
return v_res_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___redArg___lam__0(lean_object* v_tries_2301_, lean_object* v_m_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_){
_start:
{
lean_object* v___x_2308_; lean_object* v___x_2309_; 
v___x_2308_ = lean_st_mk_ref(v_tries_2301_);
lean_inc(v___x_2308_);
v___x_2309_ = lean_apply_6(v_m_2302_, v___x_2308_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, lean_box(0));
if (lean_obj_tag(v___x_2309_) == 0)
{
lean_object* v_a_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2319_; 
v_a_2310_ = lean_ctor_get(v___x_2309_, 0);
v_isSharedCheck_2319_ = !lean_is_exclusive(v___x_2309_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2312_ = v___x_2309_;
v_isShared_2313_ = v_isSharedCheck_2319_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_a_2310_);
lean_dec(v___x_2309_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2319_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2317_; 
v___x_2314_ = lean_st_ref_get(v___x_2308_);
lean_dec(v___x_2308_);
v___x_2315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2315_, 0, v_a_2310_);
lean_ctor_set(v___x_2315_, 1, v___x_2314_);
if (v_isShared_2313_ == 0)
{
lean_ctor_set(v___x_2312_, 0, v___x_2315_);
v___x_2317_ = v___x_2312_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v___x_2315_);
v___x_2317_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
return v___x_2317_;
}
}
}
else
{
lean_object* v_a_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2327_; 
lean_dec(v___x_2308_);
v_a_2320_ = lean_ctor_get(v___x_2309_, 0);
v_isSharedCheck_2327_ = !lean_is_exclusive(v___x_2309_);
if (v_isSharedCheck_2327_ == 0)
{
v___x_2322_ = v___x_2309_;
v_isShared_2323_ = v_isSharedCheck_2327_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_a_2320_);
lean_dec(v___x_2309_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2327_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v___x_2325_; 
if (v_isShared_2323_ == 0)
{
v___x_2325_ = v___x_2322_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_a_2320_);
v___x_2325_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
return v___x_2325_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___redArg___lam__0___boxed(lean_object* v_tries_2328_, lean_object* v_m_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_){
_start:
{
lean_object* v_res_2335_; 
v_res_2335_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg___lam__0(v_tries_2328_, v_m_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_);
return v_res_2335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___redArg(lean_object* v_d_2336_, lean_object* v_m_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_){
_start:
{
lean_object* v_tries_2343_; lean_object* v_roots_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2397_; 
v_tries_2343_ = lean_ctor_get(v_d_2336_, 0);
v_roots_2344_ = lean_ctor_get(v_d_2336_, 1);
v_isSharedCheck_2397_ = !lean_is_exclusive(v_d_2336_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2346_ = v_d_2336_;
v_isShared_2347_ = v_isSharedCheck_2397_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_roots_2344_);
lean_inc(v_tries_2343_);
lean_dec(v_d_2336_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2397_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v___y_2349_; lean_object* v___x_2378_; uint8_t v_transparency_2379_; uint8_t v___x_2380_; uint8_t v___x_2381_; 
v___x_2378_ = l_Lean_Meta_Context_config(v_a_2338_);
v_transparency_2379_ = lean_ctor_get_uint8(v___x_2378_, 9);
lean_dec_ref(v___x_2378_);
v___x_2380_ = 2;
v___x_2381_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2379_, v___x_2380_);
if (v___x_2381_ == 0)
{
lean_object* v_keyedConfig_2382_; uint8_t v_trackZetaDelta_2383_; lean_object* v_zetaDeltaSet_2384_; lean_object* v_lctx_2385_; lean_object* v_localInstances_2386_; lean_object* v_defEqCtx_x3f_2387_; lean_object* v_synthPendingDepth_2388_; lean_object* v_customCanUnfoldPredicate_x3f_2389_; uint8_t v_univApprox_2390_; uint8_t v_inTypeClassResolution_2391_; uint8_t v_cacheInferType_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; 
v_keyedConfig_2382_ = lean_ctor_get(v_a_2338_, 0);
v_trackZetaDelta_2383_ = lean_ctor_get_uint8(v_a_2338_, sizeof(void*)*7);
v_zetaDeltaSet_2384_ = lean_ctor_get(v_a_2338_, 1);
v_lctx_2385_ = lean_ctor_get(v_a_2338_, 2);
v_localInstances_2386_ = lean_ctor_get(v_a_2338_, 3);
v_defEqCtx_x3f_2387_ = lean_ctor_get(v_a_2338_, 4);
v_synthPendingDepth_2388_ = lean_ctor_get(v_a_2338_, 5);
v_customCanUnfoldPredicate_x3f_2389_ = lean_ctor_get(v_a_2338_, 6);
v_univApprox_2390_ = lean_ctor_get_uint8(v_a_2338_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2391_ = lean_ctor_get_uint8(v_a_2338_, sizeof(void*)*7 + 2);
v_cacheInferType_2392_ = lean_ctor_get_uint8(v_a_2338_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2382_);
v___x_2393_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2380_, v_keyedConfig_2382_);
lean_inc(v_customCanUnfoldPredicate_x3f_2389_);
lean_inc(v_synthPendingDepth_2388_);
lean_inc(v_defEqCtx_x3f_2387_);
lean_inc_ref(v_localInstances_2386_);
lean_inc_ref(v_lctx_2385_);
lean_inc(v_zetaDeltaSet_2384_);
v___x_2394_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2394_, 0, v___x_2393_);
lean_ctor_set(v___x_2394_, 1, v_zetaDeltaSet_2384_);
lean_ctor_set(v___x_2394_, 2, v_lctx_2385_);
lean_ctor_set(v___x_2394_, 3, v_localInstances_2386_);
lean_ctor_set(v___x_2394_, 4, v_defEqCtx_x3f_2387_);
lean_ctor_set(v___x_2394_, 5, v_synthPendingDepth_2388_);
lean_ctor_set(v___x_2394_, 6, v_customCanUnfoldPredicate_x3f_2389_);
lean_ctor_set_uint8(v___x_2394_, sizeof(void*)*7, v_trackZetaDelta_2383_);
lean_ctor_set_uint8(v___x_2394_, sizeof(void*)*7 + 1, v_univApprox_2390_);
lean_ctor_set_uint8(v___x_2394_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2391_);
lean_ctor_set_uint8(v___x_2394_, sizeof(void*)*7 + 3, v_cacheInferType_2392_);
lean_inc(v_a_2341_);
lean_inc_ref(v_a_2340_);
lean_inc(v_a_2339_);
v___x_2395_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg___lam__0(v_tries_2343_, v_m_2337_, v___x_2394_, v_a_2339_, v_a_2340_, v_a_2341_);
v___y_2349_ = v___x_2395_;
goto v___jp_2348_;
}
else
{
lean_object* v___x_2396_; 
lean_inc(v_a_2341_);
lean_inc_ref(v_a_2340_);
lean_inc(v_a_2339_);
lean_inc_ref(v_a_2338_);
v___x_2396_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg___lam__0(v_tries_2343_, v_m_2337_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_);
v___y_2349_ = v___x_2396_;
goto v___jp_2348_;
}
v___jp_2348_:
{
if (lean_obj_tag(v___y_2349_) == 0)
{
lean_object* v_a_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2369_; 
v_a_2350_ = lean_ctor_get(v___y_2349_, 0);
v_isSharedCheck_2369_ = !lean_is_exclusive(v___y_2349_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2352_ = v___y_2349_;
v_isShared_2353_ = v_isSharedCheck_2369_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_dec(v___y_2349_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2369_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v_fst_2354_; lean_object* v_snd_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2368_; 
v_fst_2354_ = lean_ctor_get(v_a_2350_, 0);
v_snd_2355_ = lean_ctor_get(v_a_2350_, 1);
v_isSharedCheck_2368_ = !lean_is_exclusive(v_a_2350_);
if (v_isSharedCheck_2368_ == 0)
{
v___x_2357_ = v_a_2350_;
v_isShared_2358_ = v_isSharedCheck_2368_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_snd_2355_);
lean_inc(v_fst_2354_);
lean_dec(v_a_2350_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2368_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2360_; 
if (v_isShared_2347_ == 0)
{
lean_ctor_set(v___x_2346_, 0, v_snd_2355_);
v___x_2360_ = v___x_2346_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v_snd_2355_);
lean_ctor_set(v_reuseFailAlloc_2367_, 1, v_roots_2344_);
v___x_2360_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
lean_object* v___x_2362_; 
if (v_isShared_2358_ == 0)
{
lean_ctor_set(v___x_2357_, 1, v___x_2360_);
v___x_2362_ = v___x_2357_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_fst_2354_);
lean_ctor_set(v_reuseFailAlloc_2366_, 1, v___x_2360_);
v___x_2362_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
lean_object* v___x_2364_; 
if (v_isShared_2353_ == 0)
{
lean_ctor_set(v___x_2352_, 0, v___x_2362_);
v___x_2364_ = v___x_2352_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v___x_2362_);
v___x_2364_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
return v___x_2364_;
}
}
}
}
}
}
else
{
lean_object* v_a_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2377_; 
lean_del_object(v___x_2346_);
lean_dec_ref(v_roots_2344_);
v_a_2370_ = lean_ctor_get(v___y_2349_, 0);
v_isSharedCheck_2377_ = !lean_is_exclusive(v___y_2349_);
if (v_isSharedCheck_2377_ == 0)
{
v___x_2372_ = v___y_2349_;
v_isShared_2373_ = v_isSharedCheck_2377_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_a_2370_);
lean_dec(v___y_2349_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2377_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v___x_2375_; 
if (v_isShared_2373_ == 0)
{
v___x_2375_ = v___x_2372_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v_a_2370_);
v___x_2375_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
return v___x_2375_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___redArg___boxed(lean_object* v_d_2398_, lean_object* v_m_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_){
_start:
{
lean_object* v_res_2405_; 
v_res_2405_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_d_2398_, v_m_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_);
lean_dec(v_a_2403_);
lean_dec_ref(v_a_2402_);
lean_dec(v_a_2401_);
lean_dec_ref(v_a_2400_);
return v_res_2405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch(lean_object* v_00_u03b1_2406_, lean_object* v_00_u03b2_2407_, lean_object* v_d_2408_, lean_object* v_m_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_){
_start:
{
lean_object* v___x_2415_; 
v___x_2415_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_d_2408_, v_m_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
return v___x_2415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___boxed(lean_object* v_00_u03b1_2416_, lean_object* v_00_u03b2_2417_, lean_object* v_d_2418_, lean_object* v_m_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_){
_start:
{
lean_object* v_res_2425_; 
v_res_2425_ = l_Lean_Meta_LazyDiscrTree_runMatch(v_00_u03b1_2416_, v_00_u03b2_2417_, v_d_2418_, v_m_2419_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_);
lean_dec(v_a_2423_);
lean_dec_ref(v_a_2422_);
lean_dec(v_a_2421_);
lean_dec_ref(v_a_2420_);
return v_res_2425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie___redArg(lean_object* v_i_2426_, lean_object* v_v_2427_, lean_object* v_a_2428_){
_start:
{
lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; 
v___x_2430_ = lean_st_ref_take(v_a_2428_);
v___x_2431_ = lean_box(0);
v___x_2432_ = lean_array_set(v___x_2430_, v_i_2426_, v_v_2427_);
v___x_2433_ = lean_st_ref_put(v_a_2428_, v___x_2432_);
v___x_2434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2434_, 0, v___x_2431_);
return v___x_2434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie___redArg___boxed(lean_object* v_i_2435_, lean_object* v_v_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_){
_start:
{
lean_object* v_res_2439_; 
v_res_2439_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_i_2435_, v_v_2436_, v_a_2437_);
lean_dec(v_a_2437_);
lean_dec(v_i_2435_);
return v_res_2439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie(lean_object* v_00_u03b1_2440_, lean_object* v_i_2441_, lean_object* v_v_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_){
_start:
{
lean_object* v___x_2449_; 
v___x_2449_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_i_2441_, v_v_2442_, v_a_2443_);
return v___x_2449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie___boxed(lean_object* v_00_u03b1_2450_, lean_object* v_i_2451_, lean_object* v_v_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_){
_start:
{
lean_object* v_res_2459_; 
v_res_2459_ = l_Lean_Meta_LazyDiscrTree_setTrie(v_00_u03b1_2450_, v_i_2451_, v_v_2452_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_);
lean_dec(v_a_2457_);
lean_dec_ref(v_a_2456_);
lean_dec(v_a_2455_);
lean_dec_ref(v_a_2454_);
lean_dec(v_a_2453_);
lean_dec(v_i_2451_);
return v_res_2459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___redArg___lam__0(lean_object* v_e_2460_, lean_object* v_a_2461_){
_start:
{
lean_object* v_sz_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; 
v_sz_2462_ = lean_array_get_size(v_a_2461_);
v___x_2463_ = lean_unsigned_to_nat(0u);
v___x_2464_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___x_2465_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2);
v___x_2466_ = lean_unsigned_to_nat(1u);
v___x_2467_ = lean_mk_empty_array_with_capacity(v___x_2466_);
v___x_2468_ = lean_array_push(v___x_2467_, v_e_2460_);
v___x_2469_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2469_, 0, v___x_2464_);
lean_ctor_set(v___x_2469_, 1, v___x_2463_);
lean_ctor_set(v___x_2469_, 2, v___x_2465_);
lean_ctor_set(v___x_2469_, 3, v___x_2468_);
v___x_2470_ = lean_array_push(v_a_2461_, v___x_2469_);
v___x_2471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2471_, 0, v_sz_2462_);
lean_ctor_set(v___x_2471_, 1, v___x_2470_);
return v___x_2471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___redArg(lean_object* v_inst_2472_, lean_object* v_e_2473_){
_start:
{
lean_object* v_modifyGet_2474_; lean_object* v___f_2475_; lean_object* v___x_2476_; 
v_modifyGet_2474_ = lean_ctor_get(v_inst_2472_, 2);
lean_inc(v_modifyGet_2474_);
lean_dec_ref(v_inst_2472_);
v___f_2475_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_newTrie___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2475_, 0, v_e_2473_);
v___x_2476_ = lean_apply_2(v_modifyGet_2474_, lean_box(0), v___f_2475_);
return v___x_2476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie(lean_object* v_m_2477_, lean_object* v_00_u03b1_2478_, lean_object* v_inst_2479_, lean_object* v_inst_2480_, lean_object* v_e_2481_){
_start:
{
lean_object* v___x_2482_; 
v___x_2482_ = l_Lean_Meta_LazyDiscrTree_newTrie___redArg(v_inst_2480_, v_e_2481_);
return v___x_2482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___boxed(lean_object* v_m_2483_, lean_object* v_00_u03b1_2484_, lean_object* v_inst_2485_, lean_object* v_inst_2486_, lean_object* v_e_2487_){
_start:
{
lean_object* v_res_2488_; 
v_res_2488_ = l_Lean_Meta_LazyDiscrTree_newTrie(v_m_2483_, v_00_u03b1_2484_, v_inst_2485_, v_inst_2486_, v_e_2487_);
lean_dec_ref(v_inst_2485_);
return v_res_2488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(lean_object* v_i_2489_, lean_object* v_e_2490_, lean_object* v_a_2491_){
_start:
{
lean_object* v___x_2493_; lean_object* v_fst_2495_; lean_object* v_snd_2496_; lean_object* v___x_2499_; lean_object* v___x_2500_; uint8_t v___x_2501_; 
v___x_2493_ = lean_st_ref_take(v_a_2491_);
v___x_2499_ = lean_box(0);
v___x_2500_ = lean_array_get_size(v___x_2493_);
v___x_2501_ = lean_nat_dec_lt(v_i_2489_, v___x_2500_);
if (v___x_2501_ == 0)
{
lean_dec_ref(v_e_2490_);
v_fst_2495_ = v___x_2499_;
v_snd_2496_ = v___x_2493_;
goto v___jp_2494_;
}
else
{
lean_object* v_v_2502_; lean_object* v_xs_x27_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; 
v_v_2502_ = lean_array_fget(v___x_2493_, v_i_2489_);
v_xs_x27_2503_ = lean_array_fset(v___x_2493_, v_i_2489_, v___x_2499_);
v___x_2504_ = l_Lean_Meta_LazyDiscrTree_Trie_pushPending___redArg(v_v_2502_, v_e_2490_);
v___x_2505_ = lean_array_fset(v_xs_x27_2503_, v_i_2489_, v___x_2504_);
v_fst_2495_ = v___x_2499_;
v_snd_2496_ = v___x_2505_;
goto v___jp_2494_;
}
v___jp_2494_:
{
lean_object* v___x_2497_; lean_object* v___x_2498_; 
v___x_2497_ = lean_st_ref_put(v_a_2491_, v_snd_2496_);
v___x_2498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2498_, 0, v_fst_2495_);
return v___x_2498_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg___boxed(lean_object* v_i_2506_, lean_object* v_e_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_){
_start:
{
lean_object* v_res_2510_; 
v_res_2510_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_i_2506_, v_e_2507_, v_a_2508_);
lean_dec(v_a_2508_);
lean_dec(v_i_2506_);
return v_res_2510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie(lean_object* v_00_u03b1_2511_, lean_object* v_i_2512_, lean_object* v_e_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_){
_start:
{
lean_object* v___x_2520_; 
v___x_2520_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_i_2512_, v_e_2513_, v_a_2514_);
return v___x_2520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___boxed(lean_object* v_00_u03b1_2521_, lean_object* v_i_2522_, lean_object* v_e_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_){
_start:
{
lean_object* v_res_2530_; 
v_res_2530_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie(v_00_u03b1_2521_, v_i_2522_, v_e_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_);
lean_dec(v_a_2528_);
lean_dec_ref(v_a_2527_);
lean_dec(v_a_2526_);
lean_dec_ref(v_a_2525_);
lean_dec(v_a_2524_);
lean_dec(v_i_2522_);
return v_res_2530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0(lean_object* v_x_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_){
_start:
{
lean_object* v___x_2538_; 
lean_inc(v___y_2532_);
v___x_2538_ = lean_apply_6(v_x_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, lean_box(0));
return v___x_2538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0___boxed(lean_object* v_x_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_){
_start:
{
lean_object* v_res_2546_; 
v_res_2546_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0(v_x_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
lean_dec(v___y_2540_);
return v_res_2546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(lean_object* v_lctx_2547_, lean_object* v_localInsts_2548_, lean_object* v_x_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_){
_start:
{
lean_object* v___f_2556_; lean_object* v___x_2557_; 
lean_inc(v___y_2550_);
v___f_2556_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2556_, 0, v_x_2549_);
lean_closure_set(v___f_2556_, 1, v___y_2550_);
v___x_2557_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_2547_, v_localInsts_2548_, v___f_2556_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_);
if (lean_obj_tag(v___x_2557_) == 0)
{
return v___x_2557_;
}
else
{
lean_object* v_a_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2565_; 
v_a_2558_ = lean_ctor_get(v___x_2557_, 0);
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2560_ = v___x_2557_;
v_isShared_2561_ = v_isSharedCheck_2565_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_a_2558_);
lean_dec(v___x_2557_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2565_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
lean_object* v___x_2563_; 
if (v_isShared_2561_ == 0)
{
v___x_2563_ = v___x_2560_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v_a_2558_);
v___x_2563_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
return v___x_2563_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___boxed(lean_object* v_lctx_2566_, lean_object* v_localInsts_2567_, lean_object* v_x_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_){
_start:
{
lean_object* v_res_2575_; 
v_res_2575_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(v_lctx_2566_, v_localInsts_2567_, v_x_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_);
lean_dec(v___y_2573_);
lean_dec_ref(v___y_2572_);
lean_dec(v___y_2571_);
lean_dec_ref(v___y_2570_);
lean_dec(v___y_2569_);
return v_res_2575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0(lean_object* v_00_u03b1_2576_, lean_object* v_00_u03b1_2577_, lean_object* v_lctx_2578_, lean_object* v_localInsts_2579_, lean_object* v_x_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_){
_start:
{
lean_object* v___x_2587_; 
v___x_2587_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(v_lctx_2578_, v_localInsts_2579_, v_x_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_);
return v___x_2587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___boxed(lean_object* v_00_u03b1_2588_, lean_object* v_00_u03b1_2589_, lean_object* v_lctx_2590_, lean_object* v_localInsts_2591_, lean_object* v_x_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_){
_start:
{
lean_object* v_res_2599_; 
v_res_2599_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0(v_00_u03b1_2588_, v_00_u03b1_2589_, v_lctx_2590_, v_localInsts_2591_, v_x_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
lean_dec(v___y_2595_);
lean_dec_ref(v___y_2594_);
lean_dec(v___y_2593_);
return v_res_2599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(lean_object* v_e_2600_, lean_object* v___y_2601_){
_start:
{
lean_object* v___x_2603_; lean_object* v_sz_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; 
v___x_2603_ = lean_st_ref_take(v___y_2601_);
v_sz_2604_ = lean_array_get_size(v___x_2603_);
v___x_2605_ = lean_unsigned_to_nat(0u);
v___x_2606_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___x_2607_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2);
v___x_2608_ = lean_unsigned_to_nat(1u);
v___x_2609_ = lean_mk_empty_array_with_capacity(v___x_2608_);
v___x_2610_ = lean_array_push(v___x_2609_, v_e_2600_);
v___x_2611_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2611_, 0, v___x_2606_);
lean_ctor_set(v___x_2611_, 1, v___x_2605_);
lean_ctor_set(v___x_2611_, 2, v___x_2607_);
lean_ctor_set(v___x_2611_, 3, v___x_2610_);
v___x_2612_ = lean_array_push(v___x_2603_, v___x_2611_);
v___x_2613_ = lean_st_ref_put(v___y_2601_, v___x_2612_);
v___x_2614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2614_, 0, v_sz_2604_);
return v___x_2614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg___boxed(lean_object* v_e_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_){
_start:
{
lean_object* v_res_2618_; 
v_res_2618_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v_e_2615_, v___y_2616_);
lean_dec(v___y_2616_);
return v_res_2618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2(lean_object* v_00_u03b1_2619_, lean_object* v_e_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_){
_start:
{
lean_object* v___x_2627_; 
v___x_2627_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v_e_2620_, v___y_2621_);
return v___x_2627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___boxed(lean_object* v_00_u03b1_2628_, lean_object* v_e_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_){
_start:
{
lean_object* v_res_2636_; 
v_res_2636_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2(v_00_u03b1_2628_, v_e_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec(v___y_2632_);
lean_dec_ref(v___y_2631_);
lean_dec(v___y_2630_);
return v_res_2636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0(uint8_t v___x_2637_, lean_object* v_todo_2638_, lean_object* v_e_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_){
_start:
{
lean_object* v___x_2646_; 
v___x_2646_ = l_Lean_Meta_LazyDiscrTree_pushArgs(v___x_2637_, v_todo_2638_, v_e_2639_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
return v___x_2646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0___boxed(lean_object* v___x_2647_, lean_object* v_todo_2648_, lean_object* v_e_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_){
_start:
{
uint8_t v___x_3423__boxed_2656_; lean_object* v_res_2657_; 
v___x_3423__boxed_2656_ = lean_unbox(v___x_2647_);
v_res_2657_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0(v___x_3423__boxed_2656_, v_todo_2648_, v_e_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_);
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2653_);
lean_dec(v___y_2652_);
lean_dec_ref(v___y_2651_);
lean_dec(v___y_2650_);
return v_res_2657_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(lean_object* v_a_2658_, lean_object* v_b_2659_, lean_object* v_x_2660_){
_start:
{
if (lean_obj_tag(v_x_2660_) == 0)
{
lean_dec(v_b_2659_);
lean_dec(v_a_2658_);
return v_x_2660_;
}
else
{
lean_object* v_key_2661_; lean_object* v_value_2662_; lean_object* v_tail_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2675_; 
v_key_2661_ = lean_ctor_get(v_x_2660_, 0);
v_value_2662_ = lean_ctor_get(v_x_2660_, 1);
v_tail_2663_ = lean_ctor_get(v_x_2660_, 2);
v_isSharedCheck_2675_ = !lean_is_exclusive(v_x_2660_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2665_ = v_x_2660_;
v_isShared_2666_ = v_isSharedCheck_2675_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_tail_2663_);
lean_inc(v_value_2662_);
lean_inc(v_key_2661_);
lean_dec(v_x_2660_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2675_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
uint8_t v___x_2667_; 
v___x_2667_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_2661_, v_a_2658_);
if (v___x_2667_ == 0)
{
lean_object* v___x_2668_; lean_object* v___x_2670_; 
v___x_2668_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(v_a_2658_, v_b_2659_, v_tail_2663_);
if (v_isShared_2666_ == 0)
{
lean_ctor_set(v___x_2665_, 2, v___x_2668_);
v___x_2670_ = v___x_2665_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v_key_2661_);
lean_ctor_set(v_reuseFailAlloc_2671_, 1, v_value_2662_);
lean_ctor_set(v_reuseFailAlloc_2671_, 2, v___x_2668_);
v___x_2670_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
return v___x_2670_;
}
}
else
{
lean_object* v___x_2673_; 
lean_dec(v_value_2662_);
lean_dec(v_key_2661_);
if (v_isShared_2666_ == 0)
{
lean_ctor_set(v___x_2665_, 1, v_b_2659_);
lean_ctor_set(v___x_2665_, 0, v_a_2658_);
v___x_2673_ = v___x_2665_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_a_2658_);
lean_ctor_set(v_reuseFailAlloc_2674_, 1, v_b_2659_);
lean_ctor_set(v_reuseFailAlloc_2674_, 2, v_tail_2663_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(lean_object* v_a_2676_, lean_object* v_x_2677_){
_start:
{
if (lean_obj_tag(v_x_2677_) == 0)
{
uint8_t v___x_2678_; 
v___x_2678_ = 0;
return v___x_2678_;
}
else
{
lean_object* v_key_2679_; lean_object* v_tail_2680_; uint8_t v___x_2681_; 
v_key_2679_ = lean_ctor_get(v_x_2677_, 0);
v_tail_2680_ = lean_ctor_get(v_x_2677_, 2);
v___x_2681_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_2679_, v_a_2676_);
if (v___x_2681_ == 0)
{
v_x_2677_ = v_tail_2680_;
goto _start;
}
else
{
return v___x_2681_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg___boxed(lean_object* v_a_2683_, lean_object* v_x_2684_){
_start:
{
uint8_t v_res_2685_; lean_object* v_r_2686_; 
v_res_2685_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(v_a_2683_, v_x_2684_);
lean_dec(v_x_2684_);
lean_dec(v_a_2683_);
v_r_2686_ = lean_box(v_res_2685_);
return v_r_2686_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7___redArg(lean_object* v_x_2687_, lean_object* v_x_2688_){
_start:
{
if (lean_obj_tag(v_x_2688_) == 0)
{
return v_x_2687_;
}
else
{
lean_object* v_key_2689_; lean_object* v_value_2690_; lean_object* v_tail_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2714_; 
v_key_2689_ = lean_ctor_get(v_x_2688_, 0);
v_value_2690_ = lean_ctor_get(v_x_2688_, 1);
v_tail_2691_ = lean_ctor_get(v_x_2688_, 2);
v_isSharedCheck_2714_ = !lean_is_exclusive(v_x_2688_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2693_ = v_x_2688_;
v_isShared_2694_ = v_isSharedCheck_2714_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_tail_2691_);
lean_inc(v_value_2690_);
lean_inc(v_key_2689_);
lean_dec(v_x_2688_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2714_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v___x_2695_; uint64_t v___x_2696_; uint64_t v___x_2697_; uint64_t v___x_2698_; uint64_t v_fold_2699_; uint64_t v___x_2700_; uint64_t v___x_2701_; uint64_t v___x_2702_; size_t v___x_2703_; size_t v___x_2704_; size_t v___x_2705_; size_t v___x_2706_; size_t v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2710_; 
v___x_2695_ = lean_array_get_size(v_x_2687_);
v___x_2696_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_key_2689_);
v___x_2697_ = 32ULL;
v___x_2698_ = lean_uint64_shift_right(v___x_2696_, v___x_2697_);
v_fold_2699_ = lean_uint64_xor(v___x_2696_, v___x_2698_);
v___x_2700_ = 16ULL;
v___x_2701_ = lean_uint64_shift_right(v_fold_2699_, v___x_2700_);
v___x_2702_ = lean_uint64_xor(v_fold_2699_, v___x_2701_);
v___x_2703_ = lean_uint64_to_usize(v___x_2702_);
v___x_2704_ = lean_usize_of_nat(v___x_2695_);
v___x_2705_ = ((size_t)1ULL);
v___x_2706_ = lean_usize_sub(v___x_2704_, v___x_2705_);
v___x_2707_ = lean_usize_land(v___x_2703_, v___x_2706_);
v___x_2708_ = lean_array_uget_borrowed(v_x_2687_, v___x_2707_);
lean_inc(v___x_2708_);
if (v_isShared_2694_ == 0)
{
lean_ctor_set(v___x_2693_, 2, v___x_2708_);
v___x_2710_ = v___x_2693_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v_key_2689_);
lean_ctor_set(v_reuseFailAlloc_2713_, 1, v_value_2690_);
lean_ctor_set(v_reuseFailAlloc_2713_, 2, v___x_2708_);
v___x_2710_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
lean_object* v___x_2711_; 
v___x_2711_ = lean_array_uset(v_x_2687_, v___x_2707_, v___x_2710_);
v_x_2687_ = v___x_2711_;
v_x_2688_ = v_tail_2691_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6___redArg(lean_object* v_i_2715_, lean_object* v_source_2716_, lean_object* v_target_2717_){
_start:
{
lean_object* v___x_2718_; uint8_t v___x_2719_; 
v___x_2718_ = lean_array_get_size(v_source_2716_);
v___x_2719_ = lean_nat_dec_lt(v_i_2715_, v___x_2718_);
if (v___x_2719_ == 0)
{
lean_dec_ref(v_source_2716_);
lean_dec(v_i_2715_);
return v_target_2717_;
}
else
{
lean_object* v_es_2720_; lean_object* v___x_2721_; lean_object* v_source_2722_; lean_object* v_target_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; 
v_es_2720_ = lean_array_fget(v_source_2716_, v_i_2715_);
v___x_2721_ = lean_box(0);
v_source_2722_ = lean_array_fset(v_source_2716_, v_i_2715_, v___x_2721_);
v_target_2723_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7___redArg(v_target_2717_, v_es_2720_);
v___x_2724_ = lean_unsigned_to_nat(1u);
v___x_2725_ = lean_nat_add(v_i_2715_, v___x_2724_);
lean_dec(v_i_2715_);
v_i_2715_ = v___x_2725_;
v_source_2716_ = v_source_2722_;
v_target_2717_ = v_target_2723_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5___redArg(lean_object* v_data_2727_){
_start:
{
lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v_nbuckets_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; 
v___x_2728_ = lean_array_get_size(v_data_2727_);
v___x_2729_ = lean_unsigned_to_nat(2u);
v_nbuckets_2730_ = lean_nat_mul(v___x_2728_, v___x_2729_);
v___x_2731_ = lean_unsigned_to_nat(0u);
v___x_2732_ = lean_box(0);
v___x_2733_ = lean_mk_array(v_nbuckets_2730_, v___x_2732_);
v___x_2734_ = lean_array_propagate_mark(v_data_2727_, v___x_2733_);
v___x_2735_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6___redArg(v___x_2731_, v_data_2727_, v___x_2734_);
return v___x_2735_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(lean_object* v_m_2736_, lean_object* v_a_2737_, lean_object* v_b_2738_){
_start:
{
lean_object* v_size_2739_; lean_object* v_buckets_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2783_; 
v_size_2739_ = lean_ctor_get(v_m_2736_, 0);
v_buckets_2740_ = lean_ctor_get(v_m_2736_, 1);
v_isSharedCheck_2783_ = !lean_is_exclusive(v_m_2736_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2742_ = v_m_2736_;
v_isShared_2743_ = v_isSharedCheck_2783_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_buckets_2740_);
lean_inc(v_size_2739_);
lean_dec(v_m_2736_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2783_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
lean_object* v___x_2744_; uint64_t v___x_2745_; uint64_t v___x_2746_; uint64_t v___x_2747_; uint64_t v_fold_2748_; uint64_t v___x_2749_; uint64_t v___x_2750_; uint64_t v___x_2751_; size_t v___x_2752_; size_t v___x_2753_; size_t v___x_2754_; size_t v___x_2755_; size_t v___x_2756_; lean_object* v_bkt_2757_; uint8_t v___x_2758_; 
v___x_2744_ = lean_array_get_size(v_buckets_2740_);
v___x_2745_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_a_2737_);
v___x_2746_ = 32ULL;
v___x_2747_ = lean_uint64_shift_right(v___x_2745_, v___x_2746_);
v_fold_2748_ = lean_uint64_xor(v___x_2745_, v___x_2747_);
v___x_2749_ = 16ULL;
v___x_2750_ = lean_uint64_shift_right(v_fold_2748_, v___x_2749_);
v___x_2751_ = lean_uint64_xor(v_fold_2748_, v___x_2750_);
v___x_2752_ = lean_uint64_to_usize(v___x_2751_);
v___x_2753_ = lean_usize_of_nat(v___x_2744_);
v___x_2754_ = ((size_t)1ULL);
v___x_2755_ = lean_usize_sub(v___x_2753_, v___x_2754_);
v___x_2756_ = lean_usize_land(v___x_2752_, v___x_2755_);
v_bkt_2757_ = lean_array_uget_borrowed(v_buckets_2740_, v___x_2756_);
v___x_2758_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(v_a_2737_, v_bkt_2757_);
if (v___x_2758_ == 0)
{
lean_object* v___x_2759_; lean_object* v_size_x27_2760_; lean_object* v___x_2761_; lean_object* v_buckets_x27_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; uint8_t v___x_2768_; 
v___x_2759_ = lean_unsigned_to_nat(1u);
v_size_x27_2760_ = lean_nat_add(v_size_2739_, v___x_2759_);
lean_dec(v_size_2739_);
lean_inc(v_bkt_2757_);
v___x_2761_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2761_, 0, v_a_2737_);
lean_ctor_set(v___x_2761_, 1, v_b_2738_);
lean_ctor_set(v___x_2761_, 2, v_bkt_2757_);
v_buckets_x27_2762_ = lean_array_uset(v_buckets_2740_, v___x_2756_, v___x_2761_);
v___x_2763_ = lean_unsigned_to_nat(4u);
v___x_2764_ = lean_nat_mul(v_size_x27_2760_, v___x_2763_);
v___x_2765_ = lean_unsigned_to_nat(3u);
v___x_2766_ = lean_nat_div(v___x_2764_, v___x_2765_);
lean_dec(v___x_2764_);
v___x_2767_ = lean_array_get_size(v_buckets_x27_2762_);
v___x_2768_ = lean_nat_dec_le(v___x_2766_, v___x_2767_);
lean_dec(v___x_2766_);
if (v___x_2768_ == 0)
{
lean_object* v_val_2769_; lean_object* v___x_2771_; 
v_val_2769_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5___redArg(v_buckets_x27_2762_);
if (v_isShared_2743_ == 0)
{
lean_ctor_set(v___x_2742_, 1, v_val_2769_);
lean_ctor_set(v___x_2742_, 0, v_size_x27_2760_);
v___x_2771_ = v___x_2742_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v_size_x27_2760_);
lean_ctor_set(v_reuseFailAlloc_2772_, 1, v_val_2769_);
v___x_2771_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
return v___x_2771_;
}
}
else
{
lean_object* v___x_2774_; 
if (v_isShared_2743_ == 0)
{
lean_ctor_set(v___x_2742_, 1, v_buckets_x27_2762_);
lean_ctor_set(v___x_2742_, 0, v_size_x27_2760_);
v___x_2774_ = v___x_2742_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v_size_x27_2760_);
lean_ctor_set(v_reuseFailAlloc_2775_, 1, v_buckets_x27_2762_);
v___x_2774_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
return v___x_2774_;
}
}
}
else
{
lean_object* v___x_2776_; lean_object* v_buckets_x27_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2781_; 
lean_inc(v_bkt_2757_);
v___x_2776_ = lean_box(0);
v_buckets_x27_2777_ = lean_array_uset(v_buckets_2740_, v___x_2756_, v___x_2776_);
v___x_2778_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(v_a_2737_, v_b_2738_, v_bkt_2757_);
v___x_2779_ = lean_array_uset(v_buckets_x27_2777_, v___x_2756_, v___x_2778_);
if (v_isShared_2743_ == 0)
{
lean_ctor_set(v___x_2742_, 1, v___x_2779_);
v___x_2781_ = v___x_2742_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v_size_2739_);
lean_ctor_set(v_reuseFailAlloc_2782_, 1, v___x_2779_);
v___x_2781_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
return v___x_2781_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(lean_object* v_a_2784_, lean_object* v_x_2785_){
_start:
{
if (lean_obj_tag(v_x_2785_) == 0)
{
lean_object* v___x_2786_; 
v___x_2786_ = lean_box(0);
return v___x_2786_;
}
else
{
lean_object* v_key_2787_; lean_object* v_value_2788_; lean_object* v_tail_2789_; uint8_t v___x_2790_; 
v_key_2787_ = lean_ctor_get(v_x_2785_, 0);
v_value_2788_ = lean_ctor_get(v_x_2785_, 1);
v_tail_2789_ = lean_ctor_get(v_x_2785_, 2);
v___x_2790_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_2787_, v_a_2784_);
if (v___x_2790_ == 0)
{
v_x_2785_ = v_tail_2789_;
goto _start;
}
else
{
lean_object* v___x_2792_; 
lean_inc(v_value_2788_);
v___x_2792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2792_, 0, v_value_2788_);
return v___x_2792_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg___boxed(lean_object* v_a_2793_, lean_object* v_x_2794_){
_start:
{
lean_object* v_res_2795_; 
v_res_2795_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(v_a_2793_, v_x_2794_);
lean_dec(v_x_2794_);
lean_dec(v_a_2793_);
return v_res_2795_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(lean_object* v_m_2796_, lean_object* v_a_2797_){
_start:
{
lean_object* v_buckets_2798_; lean_object* v___x_2799_; uint64_t v___x_2800_; uint64_t v___x_2801_; uint64_t v___x_2802_; uint64_t v_fold_2803_; uint64_t v___x_2804_; uint64_t v___x_2805_; uint64_t v___x_2806_; size_t v___x_2807_; size_t v___x_2808_; size_t v___x_2809_; size_t v___x_2810_; size_t v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; 
v_buckets_2798_ = lean_ctor_get(v_m_2796_, 1);
v___x_2799_ = lean_array_get_size(v_buckets_2798_);
v___x_2800_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_a_2797_);
v___x_2801_ = 32ULL;
v___x_2802_ = lean_uint64_shift_right(v___x_2800_, v___x_2801_);
v_fold_2803_ = lean_uint64_xor(v___x_2800_, v___x_2802_);
v___x_2804_ = 16ULL;
v___x_2805_ = lean_uint64_shift_right(v_fold_2803_, v___x_2804_);
v___x_2806_ = lean_uint64_xor(v_fold_2803_, v___x_2805_);
v___x_2807_ = lean_uint64_to_usize(v___x_2806_);
v___x_2808_ = lean_usize_of_nat(v___x_2799_);
v___x_2809_ = ((size_t)1ULL);
v___x_2810_ = lean_usize_sub(v___x_2808_, v___x_2809_);
v___x_2811_ = lean_usize_land(v___x_2807_, v___x_2810_);
v___x_2812_ = lean_array_uget_borrowed(v_buckets_2798_, v___x_2811_);
v___x_2813_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(v_a_2797_, v___x_2812_);
return v___x_2813_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg___boxed(lean_object* v_m_2814_, lean_object* v_a_2815_){
_start:
{
lean_object* v_res_2816_; 
v_res_2816_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_m_2814_, v_a_2815_);
lean_dec(v_a_2815_);
lean_dec_ref(v_m_2814_);
return v_res_2816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(lean_object* v_p_2817_, lean_object* v_entry_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_){
_start:
{
lean_object* v_snd_2825_; lean_object* v_snd_2826_; lean_object* v_fst_2827_; lean_object* v_fst_2828_; lean_object* v_snd_2829_; lean_object* v_fst_2830_; lean_object* v_fst_2831_; lean_object* v_snd_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; uint8_t v___x_2835_; 
v_snd_2825_ = lean_ctor_get(v_p_2817_, 1);
v_snd_2826_ = lean_ctor_get(v_entry_2818_, 1);
lean_inc(v_snd_2826_);
v_fst_2827_ = lean_ctor_get(v_p_2817_, 0);
v_fst_2828_ = lean_ctor_get(v_snd_2825_, 0);
v_snd_2829_ = lean_ctor_get(v_snd_2825_, 1);
v_fst_2830_ = lean_ctor_get(v_entry_2818_, 0);
lean_inc(v_fst_2830_);
lean_dec_ref(v_entry_2818_);
v_fst_2831_ = lean_ctor_get(v_snd_2826_, 0);
lean_inc(v_fst_2831_);
v_snd_2832_ = lean_ctor_get(v_snd_2826_, 1);
v___x_2833_ = lean_array_get_size(v_fst_2830_);
v___x_2834_ = lean_unsigned_to_nat(0u);
v___x_2835_ = lean_nat_dec_eq(v___x_2833_, v___x_2834_);
if (v___x_2835_ == 0)
{
lean_object* v_fst_2836_; lean_object* v_snd_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2942_; 
v_fst_2836_ = lean_ctor_get(v_fst_2831_, 0);
v_snd_2837_ = lean_ctor_get(v_fst_2831_, 1);
v_isSharedCheck_2942_ = !lean_is_exclusive(v_fst_2831_);
if (v_isSharedCheck_2942_ == 0)
{
v___x_2839_ = v_fst_2831_;
v_isShared_2840_ = v_isSharedCheck_2942_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_snd_2837_);
lean_inc(v_fst_2836_);
lean_dec(v_fst_2831_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2942_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v_e_2844_; lean_object* v_todo_2845_; lean_object* v___x_2846_; lean_object* v___f_2847_; lean_object* v___x_2848_; 
v___x_2841_ = l_Lean_instInhabitedExpr;
v___x_2842_ = lean_unsigned_to_nat(1u);
v___x_2843_ = lean_nat_sub(v___x_2833_, v___x_2842_);
v_e_2844_ = lean_array_get(v___x_2841_, v_fst_2830_, v___x_2843_);
lean_dec(v___x_2843_);
v_todo_2845_ = lean_array_pop(v_fst_2830_);
v___x_2846_ = lean_box(v___x_2835_);
v___f_2847_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2847_, 0, v___x_2846_);
lean_closure_set(v___f_2847_, 1, v_todo_2845_);
lean_closure_set(v___f_2847_, 2, v_e_2844_);
v___x_2848_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(v_fst_2836_, v_snd_2837_, v___f_2847_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_);
if (lean_obj_tag(v___x_2848_) == 0)
{
lean_object* v_a_2849_; lean_object* v_fst_2850_; lean_object* v_snd_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2933_; 
v_a_2849_ = lean_ctor_get(v___x_2848_, 0);
lean_inc(v_a_2849_);
lean_dec_ref_known(v___x_2848_, 1);
v_fst_2850_ = lean_ctor_get(v_a_2849_, 0);
v_snd_2851_ = lean_ctor_get(v_a_2849_, 1);
v_isSharedCheck_2933_ = !lean_is_exclusive(v_a_2849_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2853_ = v_a_2849_;
v_isShared_2854_ = v_isSharedCheck_2933_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_snd_2851_);
lean_inc(v_fst_2850_);
lean_dec(v_a_2849_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2933_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v___x_2855_; uint8_t v___x_2856_; 
v___x_2855_ = lean_box(3);
v___x_2856_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_fst_2850_, v___x_2855_);
if (v___x_2856_ == 0)
{
lean_object* v___x_2857_; 
v___x_2857_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_snd_2829_, v_fst_2850_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_object* v___x_2859_; 
lean_inc(v_snd_2829_);
lean_inc(v_fst_2828_);
lean_inc(v_fst_2827_);
lean_dec_ref(v_p_2817_);
lean_inc(v_snd_2826_);
if (v_isShared_2854_ == 0)
{
lean_ctor_set(v___x_2853_, 1, v_snd_2826_);
lean_ctor_set(v___x_2853_, 0, v_snd_2851_);
v___x_2859_ = v___x_2853_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v_snd_2851_);
lean_ctor_set(v_reuseFailAlloc_2882_, 1, v_snd_2826_);
v___x_2859_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_2879_; 
v_isSharedCheck_2879_ = !lean_is_exclusive(v_snd_2826_);
if (v_isSharedCheck_2879_ == 0)
{
lean_object* v_unused_2880_; lean_object* v_unused_2881_; 
v_unused_2880_ = lean_ctor_get(v_snd_2826_, 1);
lean_dec(v_unused_2880_);
v_unused_2881_ = lean_ctor_get(v_snd_2826_, 0);
lean_dec(v_unused_2881_);
v___x_2861_ = v_snd_2826_;
v_isShared_2862_ = v_isSharedCheck_2879_;
goto v_resetjp_2860_;
}
else
{
lean_dec(v_snd_2826_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_2879_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
lean_object* v___x_2863_; lean_object* v_a_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2878_; 
v___x_2863_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v___x_2859_, v_a_2819_);
v_a_2864_ = lean_ctor_get(v___x_2863_, 0);
v_isSharedCheck_2878_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2866_ = v___x_2863_;
v_isShared_2867_ = v_isSharedCheck_2878_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_a_2864_);
lean_dec(v___x_2863_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2878_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2868_; lean_object* v___x_2870_; 
v___x_2868_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_snd_2829_, v_fst_2850_, v_a_2864_);
if (v_isShared_2840_ == 0)
{
lean_ctor_set(v___x_2839_, 1, v___x_2868_);
lean_ctor_set(v___x_2839_, 0, v_fst_2828_);
v___x_2870_ = v___x_2839_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_fst_2828_);
lean_ctor_set(v_reuseFailAlloc_2877_, 1, v___x_2868_);
v___x_2870_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
lean_object* v___x_2872_; 
if (v_isShared_2862_ == 0)
{
lean_ctor_set(v___x_2861_, 1, v___x_2870_);
lean_ctor_set(v___x_2861_, 0, v_fst_2827_);
v___x_2872_ = v___x_2861_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v_fst_2827_);
lean_ctor_set(v_reuseFailAlloc_2876_, 1, v___x_2870_);
v___x_2872_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
lean_object* v___x_2874_; 
if (v_isShared_2867_ == 0)
{
lean_ctor_set(v___x_2866_, 0, v___x_2872_);
v___x_2874_ = v___x_2866_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v___x_2872_);
v___x_2874_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
return v___x_2874_;
}
}
}
}
}
}
}
else
{
lean_object* v_val_2883_; lean_object* v___x_2885_; 
lean_dec(v_fst_2850_);
lean_del_object(v___x_2839_);
v_val_2883_ = lean_ctor_get(v___x_2857_, 0);
lean_inc(v_val_2883_);
lean_dec_ref_known(v___x_2857_, 1);
if (v_isShared_2854_ == 0)
{
lean_ctor_set(v___x_2853_, 1, v_snd_2826_);
lean_ctor_set(v___x_2853_, 0, v_snd_2851_);
v___x_2885_ = v___x_2853_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v_snd_2851_);
lean_ctor_set(v_reuseFailAlloc_2895_, 1, v_snd_2826_);
v___x_2885_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
lean_object* v___x_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2893_; 
v___x_2886_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_val_2883_, v___x_2885_, v_a_2819_);
lean_dec(v_val_2883_);
v_isSharedCheck_2893_ = !lean_is_exclusive(v___x_2886_);
if (v_isSharedCheck_2893_ == 0)
{
lean_object* v_unused_2894_; 
v_unused_2894_ = lean_ctor_get(v___x_2886_, 0);
lean_dec(v_unused_2894_);
v___x_2888_ = v___x_2886_;
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
else
{
lean_dec(v___x_2886_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2891_; 
if (v_isShared_2889_ == 0)
{
lean_ctor_set(v___x_2888_, 0, v_p_2817_);
v___x_2891_ = v___x_2888_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v_p_2817_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
return v___x_2891_;
}
}
}
}
}
else
{
uint8_t v___x_2896_; 
lean_dec(v_fst_2850_);
v___x_2896_ = lean_nat_dec_eq(v_fst_2828_, v___x_2834_);
if (v___x_2896_ == 0)
{
lean_object* v___x_2898_; 
lean_del_object(v___x_2839_);
if (v_isShared_2854_ == 0)
{
lean_ctor_set(v___x_2853_, 1, v_snd_2826_);
lean_ctor_set(v___x_2853_, 0, v_snd_2851_);
v___x_2898_ = v___x_2853_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v_snd_2851_);
lean_ctor_set(v_reuseFailAlloc_2908_, 1, v_snd_2826_);
v___x_2898_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
lean_object* v___x_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2906_; 
v___x_2899_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_fst_2828_, v___x_2898_, v_a_2819_);
v_isSharedCheck_2906_ = !lean_is_exclusive(v___x_2899_);
if (v_isSharedCheck_2906_ == 0)
{
lean_object* v_unused_2907_; 
v_unused_2907_ = lean_ctor_get(v___x_2899_, 0);
lean_dec(v_unused_2907_);
v___x_2901_ = v___x_2899_;
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
else
{
lean_dec(v___x_2899_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
lean_object* v___x_2904_; 
if (v_isShared_2902_ == 0)
{
lean_ctor_set(v___x_2901_, 0, v_p_2817_);
v___x_2904_ = v___x_2901_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v_p_2817_);
v___x_2904_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
return v___x_2904_;
}
}
}
}
else
{
lean_object* v___x_2910_; 
lean_inc(v_snd_2829_);
lean_inc(v_fst_2827_);
lean_dec_ref(v_p_2817_);
lean_inc(v_snd_2826_);
if (v_isShared_2854_ == 0)
{
lean_ctor_set(v___x_2853_, 1, v_snd_2826_);
lean_ctor_set(v___x_2853_, 0, v_snd_2851_);
v___x_2910_ = v___x_2853_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_snd_2851_);
lean_ctor_set(v_reuseFailAlloc_2932_, 1, v_snd_2826_);
v___x_2910_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2929_; 
v_isSharedCheck_2929_ = !lean_is_exclusive(v_snd_2826_);
if (v_isSharedCheck_2929_ == 0)
{
lean_object* v_unused_2930_; lean_object* v_unused_2931_; 
v_unused_2930_ = lean_ctor_get(v_snd_2826_, 1);
lean_dec(v_unused_2930_);
v_unused_2931_ = lean_ctor_get(v_snd_2826_, 0);
lean_dec(v_unused_2931_);
v___x_2912_ = v_snd_2826_;
v_isShared_2913_ = v_isSharedCheck_2929_;
goto v_resetjp_2911_;
}
else
{
lean_dec(v_snd_2826_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_2929_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
lean_object* v___x_2914_; lean_object* v_a_2915_; lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2928_; 
v___x_2914_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v___x_2910_, v_a_2819_);
v_a_2915_ = lean_ctor_get(v___x_2914_, 0);
v_isSharedCheck_2928_ = !lean_is_exclusive(v___x_2914_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2917_ = v___x_2914_;
v_isShared_2918_ = v_isSharedCheck_2928_;
goto v_resetjp_2916_;
}
else
{
lean_inc(v_a_2915_);
lean_dec(v___x_2914_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_2928_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
lean_object* v___x_2920_; 
if (v_isShared_2840_ == 0)
{
lean_ctor_set(v___x_2839_, 1, v_snd_2829_);
lean_ctor_set(v___x_2839_, 0, v_a_2915_);
v___x_2920_ = v___x_2839_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v_a_2915_);
lean_ctor_set(v_reuseFailAlloc_2927_, 1, v_snd_2829_);
v___x_2920_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
lean_object* v___x_2922_; 
if (v_isShared_2913_ == 0)
{
lean_ctor_set(v___x_2912_, 1, v___x_2920_);
lean_ctor_set(v___x_2912_, 0, v_fst_2827_);
v___x_2922_ = v___x_2912_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2926_, 0, v_fst_2827_);
lean_ctor_set(v_reuseFailAlloc_2926_, 1, v___x_2920_);
v___x_2922_ = v_reuseFailAlloc_2926_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
lean_object* v___x_2924_; 
if (v_isShared_2918_ == 0)
{
lean_ctor_set(v___x_2917_, 0, v___x_2922_);
v___x_2924_ = v___x_2917_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v___x_2922_);
v___x_2924_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
return v___x_2924_;
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
lean_object* v_a_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2941_; 
lean_del_object(v___x_2839_);
lean_dec(v_snd_2826_);
lean_dec_ref(v_p_2817_);
v_a_2934_ = lean_ctor_get(v___x_2848_, 0);
v_isSharedCheck_2941_ = !lean_is_exclusive(v___x_2848_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2936_ = v___x_2848_;
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_a_2934_);
lean_dec(v___x_2848_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v___x_2939_; 
if (v_isShared_2937_ == 0)
{
v___x_2939_ = v___x_2936_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_a_2934_);
v___x_2939_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
return v___x_2939_;
}
}
}
}
}
else
{
lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2951_; 
lean_inc(v_snd_2832_);
lean_inc(v_fst_2827_);
lean_inc(v_snd_2825_);
lean_dec(v_fst_2831_);
lean_dec(v_fst_2830_);
lean_dec_ref(v_p_2817_);
v_isSharedCheck_2951_ = !lean_is_exclusive(v_snd_2826_);
if (v_isSharedCheck_2951_ == 0)
{
lean_object* v_unused_2952_; lean_object* v_unused_2953_; 
v_unused_2952_ = lean_ctor_get(v_snd_2826_, 1);
lean_dec(v_unused_2952_);
v_unused_2953_ = lean_ctor_get(v_snd_2826_, 0);
lean_dec(v_unused_2953_);
v___x_2944_ = v_snd_2826_;
v_isShared_2945_ = v_isSharedCheck_2951_;
goto v_resetjp_2943_;
}
else
{
lean_dec(v_snd_2826_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2951_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v_values_2946_; lean_object* v___x_2948_; 
v_values_2946_ = lean_array_push(v_fst_2827_, v_snd_2832_);
if (v_isShared_2945_ == 0)
{
lean_ctor_set(v___x_2944_, 1, v_snd_2825_);
lean_ctor_set(v___x_2944_, 0, v_values_2946_);
v___x_2948_ = v___x_2944_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v_values_2946_);
lean_ctor_set(v_reuseFailAlloc_2950_, 1, v_snd_2825_);
v___x_2948_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
lean_object* v___x_2949_; 
v___x_2949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2949_, 0, v___x_2948_);
return v___x_2949_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___boxed(lean_object* v_p_2954_, lean_object* v_entry_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_, lean_object* v_a_2961_){
_start:
{
lean_object* v_res_2962_; 
v_res_2962_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(v_p_2954_, v_entry_2955_, v_a_2956_, v_a_2957_, v_a_2958_, v_a_2959_, v_a_2960_);
lean_dec(v_a_2960_);
lean_dec_ref(v_a_2959_);
lean_dec(v_a_2958_);
lean_dec_ref(v_a_2957_);
lean_dec(v_a_2956_);
return v_res_2962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry(lean_object* v_00_u03b1_2963_, lean_object* v_p_2964_, lean_object* v_entry_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_){
_start:
{
lean_object* v___x_2972_; 
v___x_2972_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(v_p_2964_, v_entry_2965_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_);
return v___x_2972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___boxed(lean_object* v_00_u03b1_2973_, lean_object* v_p_2974_, lean_object* v_entry_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_){
_start:
{
lean_object* v_res_2982_; 
v_res_2982_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry(v_00_u03b1_2973_, v_p_2974_, v_entry_2975_, v_a_2976_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
lean_dec(v_a_2980_);
lean_dec_ref(v_a_2979_);
lean_dec(v_a_2978_);
lean_dec_ref(v_a_2977_);
lean_dec(v_a_2976_);
return v_res_2982_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1(lean_object* v_00_u03b2_2983_, lean_object* v_m_2984_, lean_object* v_a_2985_){
_start:
{
lean_object* v___x_2986_; 
v___x_2986_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_m_2984_, v_a_2985_);
return v___x_2986_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___boxed(lean_object* v_00_u03b2_2987_, lean_object* v_m_2988_, lean_object* v_a_2989_){
_start:
{
lean_object* v_res_2990_; 
v_res_2990_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1(v_00_u03b2_2987_, v_m_2988_, v_a_2989_);
lean_dec(v_a_2989_);
lean_dec_ref(v_m_2988_);
return v_res_2990_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3(lean_object* v_00_u03b2_2991_, lean_object* v_m_2992_, lean_object* v_a_2993_, lean_object* v_b_2994_){
_start:
{
lean_object* v___x_2995_; 
v___x_2995_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_m_2992_, v_a_2993_, v_b_2994_);
return v___x_2995_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1(lean_object* v_00_u03b2_2996_, lean_object* v_a_2997_, lean_object* v_x_2998_){
_start:
{
lean_object* v___x_2999_; 
v___x_2999_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(v_a_2997_, v_x_2998_);
return v___x_2999_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___boxed(lean_object* v_00_u03b2_3000_, lean_object* v_a_3001_, lean_object* v_x_3002_){
_start:
{
lean_object* v_res_3003_; 
v_res_3003_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1(v_00_u03b2_3000_, v_a_3001_, v_x_3002_);
lean_dec(v_x_3002_);
lean_dec(v_a_3001_);
return v_res_3003_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4(lean_object* v_00_u03b2_3004_, lean_object* v_a_3005_, lean_object* v_x_3006_){
_start:
{
uint8_t v___x_3007_; 
v___x_3007_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(v_a_3005_, v_x_3006_);
return v___x_3007_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___boxed(lean_object* v_00_u03b2_3008_, lean_object* v_a_3009_, lean_object* v_x_3010_){
_start:
{
uint8_t v_res_3011_; lean_object* v_r_3012_; 
v_res_3011_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4(v_00_u03b2_3008_, v_a_3009_, v_x_3010_);
lean_dec(v_x_3010_);
lean_dec(v_a_3009_);
v_r_3012_ = lean_box(v_res_3011_);
return v_r_3012_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5(lean_object* v_00_u03b2_3013_, lean_object* v_data_3014_){
_start:
{
lean_object* v___x_3015_; 
v___x_3015_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5___redArg(v_data_3014_);
return v___x_3015_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6(lean_object* v_00_u03b2_3016_, lean_object* v_a_3017_, lean_object* v_b_3018_, lean_object* v_x_3019_){
_start:
{
lean_object* v___x_3020_; 
v___x_3020_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(v_a_3017_, v_b_3018_, v_x_3019_);
return v___x_3020_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_3021_, lean_object* v_i_3022_, lean_object* v_source_3023_, lean_object* v_target_3024_){
_start:
{
lean_object* v___x_3025_; 
v___x_3025_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6___redArg(v_i_3022_, v_source_3023_, v_target_3024_);
return v___x_3025_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_3026_, lean_object* v_x_3027_, lean_object* v_x_3028_){
_start:
{
lean_object* v___x_3029_; 
v___x_3029_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7___redArg(v_x_3027_, v_x_3028_);
return v___x_3029_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(lean_object* v_as_3030_, size_t v_i_3031_, size_t v_stop_3032_, lean_object* v_b_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_){
_start:
{
uint8_t v___x_3040_; 
v___x_3040_ = lean_usize_dec_eq(v_i_3031_, v_stop_3032_);
if (v___x_3040_ == 0)
{
lean_object* v___x_3041_; lean_object* v___x_3042_; 
v___x_3041_ = lean_array_uget_borrowed(v_as_3030_, v_i_3031_);
lean_inc(v___x_3041_);
v___x_3042_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(v_b_3033_, v___x_3041_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_);
if (lean_obj_tag(v___x_3042_) == 0)
{
lean_object* v_a_3043_; size_t v___x_3044_; size_t v___x_3045_; 
v_a_3043_ = lean_ctor_get(v___x_3042_, 0);
lean_inc(v_a_3043_);
lean_dec_ref_known(v___x_3042_, 1);
v___x_3044_ = ((size_t)1ULL);
v___x_3045_ = lean_usize_add(v_i_3031_, v___x_3044_);
v_i_3031_ = v___x_3045_;
v_b_3033_ = v_a_3043_;
goto _start;
}
else
{
return v___x_3042_;
}
}
else
{
lean_object* v___x_3047_; 
v___x_3047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3047_, 0, v_b_3033_);
return v___x_3047_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg___boxed(lean_object* v_as_3048_, lean_object* v_i_3049_, lean_object* v_stop_3050_, lean_object* v_b_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_){
_start:
{
size_t v_i_boxed_3058_; size_t v_stop_boxed_3059_; lean_object* v_res_3060_; 
v_i_boxed_3058_ = lean_unbox_usize(v_i_3049_);
lean_dec(v_i_3049_);
v_stop_boxed_3059_ = lean_unbox_usize(v_stop_3050_);
lean_dec(v_stop_3050_);
v_res_3060_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_as_3048_, v_i_boxed_3058_, v_stop_boxed_3059_, v_b_3051_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_);
lean_dec(v___y_3056_);
lean_dec_ref(v___y_3055_);
lean_dec(v___y_3054_);
lean_dec_ref(v___y_3053_);
lean_dec(v___y_3052_);
lean_dec_ref(v_as_3048_);
return v_res_3060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(lean_object* v_values_3061_, lean_object* v_starIdx_3062_, lean_object* v_children_3063_, lean_object* v_entries_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_){
_start:
{
lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; uint8_t v___x_3075_; 
v___x_3071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3071_, 0, v_starIdx_3062_);
lean_ctor_set(v___x_3071_, 1, v_children_3063_);
v___x_3072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3072_, 0, v_values_3061_);
lean_ctor_set(v___x_3072_, 1, v___x_3071_);
v___x_3073_ = lean_unsigned_to_nat(0u);
v___x_3074_ = lean_array_get_size(v_entries_3064_);
v___x_3075_ = lean_nat_dec_lt(v___x_3073_, v___x_3074_);
if (v___x_3075_ == 0)
{
lean_object* v___x_3076_; 
v___x_3076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3076_, 0, v___x_3072_);
return v___x_3076_;
}
else
{
size_t v___x_3077_; size_t v___x_3078_; lean_object* v___x_3079_; 
v___x_3077_ = ((size_t)0ULL);
v___x_3078_ = lean_usize_of_nat(v___x_3074_);
v___x_3079_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_entries_3064_, v___x_3077_, v___x_3078_, v___x_3072_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
return v___x_3079_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg___boxed(lean_object* v_values_3080_, lean_object* v_starIdx_3081_, lean_object* v_children_3082_, lean_object* v_entries_3083_, lean_object* v_a_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_){
_start:
{
lean_object* v_res_3090_; 
v_res_3090_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(v_values_3080_, v_starIdx_3081_, v_children_3082_, v_entries_3083_, v_a_3084_, v_a_3085_, v_a_3086_, v_a_3087_, v_a_3088_);
lean_dec(v_a_3088_);
lean_dec_ref(v_a_3087_);
lean_dec(v_a_3086_);
lean_dec_ref(v_a_3085_);
lean_dec(v_a_3084_);
lean_dec_ref(v_entries_3083_);
return v_res_3090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries(lean_object* v_00_u03b1_3091_, lean_object* v_values_3092_, lean_object* v_starIdx_3093_, lean_object* v_children_3094_, lean_object* v_entries_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_){
_start:
{
lean_object* v___x_3102_; 
v___x_3102_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(v_values_3092_, v_starIdx_3093_, v_children_3094_, v_entries_3095_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_);
return v___x_3102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries___boxed(lean_object* v_00_u03b1_3103_, lean_object* v_values_3104_, lean_object* v_starIdx_3105_, lean_object* v_children_3106_, lean_object* v_entries_3107_, lean_object* v_a_3108_, lean_object* v_a_3109_, lean_object* v_a_3110_, lean_object* v_a_3111_, lean_object* v_a_3112_, lean_object* v_a_3113_){
_start:
{
lean_object* v_res_3114_; 
v_res_3114_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries(v_00_u03b1_3103_, v_values_3104_, v_starIdx_3105_, v_children_3106_, v_entries_3107_, v_a_3108_, v_a_3109_, v_a_3110_, v_a_3111_, v_a_3112_);
lean_dec(v_a_3112_);
lean_dec_ref(v_a_3111_);
lean_dec(v_a_3110_);
lean_dec_ref(v_a_3109_);
lean_dec(v_a_3108_);
lean_dec_ref(v_entries_3107_);
return v_res_3114_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0(lean_object* v_00_u03b1_3115_, lean_object* v_as_3116_, size_t v_i_3117_, size_t v_stop_3118_, lean_object* v_b_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_){
_start:
{
lean_object* v___x_3126_; 
v___x_3126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_as_3116_, v_i_3117_, v_stop_3118_, v_b_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_);
return v___x_3126_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___boxed(lean_object* v_00_u03b1_3127_, lean_object* v_as_3128_, lean_object* v_i_3129_, lean_object* v_stop_3130_, lean_object* v_b_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_){
_start:
{
size_t v_i_boxed_3138_; size_t v_stop_boxed_3139_; lean_object* v_res_3140_; 
v_i_boxed_3138_ = lean_unbox_usize(v_i_3129_);
lean_dec(v_i_3129_);
v_stop_boxed_3139_ = lean_unbox_usize(v_stop_3130_);
lean_dec(v_stop_3130_);
v_res_3140_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0(v_00_u03b1_3127_, v_as_3128_, v_i_boxed_3138_, v_stop_boxed_3139_, v_b_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_);
lean_dec(v___y_3136_);
lean_dec_ref(v___y_3135_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec(v___y_3132_);
lean_dec_ref(v_as_3128_);
return v_res_3140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode___redArg(lean_object* v_c_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_, lean_object* v_a_3146_){
_start:
{
lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v_values_3151_; lean_object* v_star_3152_; lean_object* v_children_3153_; lean_object* v_pending_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3184_; 
v___x_3148_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0);
v___x_3149_ = lean_st_ref_get(v_a_3142_);
v___x_3150_ = lean_array_get(v___x_3148_, v___x_3149_, v_c_3141_);
lean_dec(v___x_3149_);
v_values_3151_ = lean_ctor_get(v___x_3150_, 0);
v_star_3152_ = lean_ctor_get(v___x_3150_, 1);
v_children_3153_ = lean_ctor_get(v___x_3150_, 2);
v_pending_3154_ = lean_ctor_get(v___x_3150_, 3);
v_isSharedCheck_3184_ = !lean_is_exclusive(v___x_3150_);
if (v_isSharedCheck_3184_ == 0)
{
v___x_3156_ = v___x_3150_;
v_isShared_3157_ = v_isSharedCheck_3184_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_pending_3154_);
lean_inc(v_children_3153_);
lean_inc(v_star_3152_);
lean_inc(v_values_3151_);
lean_dec(v___x_3150_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3184_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
lean_object* v___x_3158_; lean_object* v___x_3159_; uint8_t v___x_3160_; 
v___x_3158_ = lean_array_get_size(v_pending_3154_);
v___x_3159_ = lean_unsigned_to_nat(0u);
v___x_3160_ = lean_nat_dec_eq(v___x_3158_, v___x_3159_);
if (v___x_3160_ == 0)
{
lean_object* v___x_3161_; lean_object* v___x_3162_; 
v___x_3161_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_c_3141_, v___x_3148_, v_a_3142_);
lean_dec_ref(v___x_3161_);
v___x_3162_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(v_values_3151_, v_star_3152_, v_children_3153_, v_pending_3154_, v_a_3142_, v_a_3143_, v_a_3144_, v_a_3145_, v_a_3146_);
lean_dec_ref(v_pending_3154_);
if (lean_obj_tag(v___x_3162_) == 0)
{
lean_object* v_a_3163_; lean_object* v_snd_3164_; lean_object* v_fst_3165_; lean_object* v_fst_3166_; lean_object* v_snd_3167_; lean_object* v___x_3168_; lean_object* v___x_3170_; 
v_a_3163_ = lean_ctor_get(v___x_3162_, 0);
lean_inc(v_a_3163_);
lean_dec_ref_known(v___x_3162_, 1);
v_snd_3164_ = lean_ctor_get(v_a_3163_, 1);
v_fst_3165_ = lean_ctor_get(v_a_3163_, 0);
v_fst_3166_ = lean_ctor_get(v_snd_3164_, 0);
v_snd_3167_ = lean_ctor_get(v_snd_3164_, 1);
v___x_3168_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__3));
lean_inc(v_snd_3167_);
lean_inc(v_fst_3166_);
lean_inc(v_fst_3165_);
if (v_isShared_3157_ == 0)
{
lean_ctor_set(v___x_3156_, 3, v___x_3168_);
lean_ctor_set(v___x_3156_, 2, v_snd_3167_);
lean_ctor_set(v___x_3156_, 1, v_fst_3166_);
lean_ctor_set(v___x_3156_, 0, v_fst_3165_);
v___x_3170_ = v___x_3156_;
goto v_reusejp_3169_;
}
else
{
lean_object* v_reuseFailAlloc_3180_; 
v_reuseFailAlloc_3180_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3180_, 0, v_fst_3165_);
lean_ctor_set(v_reuseFailAlloc_3180_, 1, v_fst_3166_);
lean_ctor_set(v_reuseFailAlloc_3180_, 2, v_snd_3167_);
lean_ctor_set(v_reuseFailAlloc_3180_, 3, v___x_3168_);
v___x_3170_ = v_reuseFailAlloc_3180_;
goto v_reusejp_3169_;
}
v_reusejp_3169_:
{
lean_object* v___x_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3178_; 
v___x_3171_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_c_3141_, v___x_3170_, v_a_3142_);
v_isSharedCheck_3178_ = !lean_is_exclusive(v___x_3171_);
if (v_isSharedCheck_3178_ == 0)
{
lean_object* v_unused_3179_; 
v_unused_3179_ = lean_ctor_get(v___x_3171_, 0);
lean_dec(v_unused_3179_);
v___x_3173_ = v___x_3171_;
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
else
{
lean_dec(v___x_3171_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
lean_object* v___x_3176_; 
if (v_isShared_3174_ == 0)
{
lean_ctor_set(v___x_3173_, 0, v_a_3163_);
v___x_3176_ = v___x_3173_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v_a_3163_);
v___x_3176_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
return v___x_3176_;
}
}
}
}
else
{
lean_del_object(v___x_3156_);
return v___x_3162_;
}
}
else
{
lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; 
lean_del_object(v___x_3156_);
lean_dec_ref(v_pending_3154_);
v___x_3181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3181_, 0, v_star_3152_);
lean_ctor_set(v___x_3181_, 1, v_children_3153_);
v___x_3182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3182_, 0, v_values_3151_);
lean_ctor_set(v___x_3182_, 1, v___x_3181_);
v___x_3183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3182_);
return v___x_3183_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode___redArg___boxed(lean_object* v_c_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_){
_start:
{
lean_object* v_res_3192_; 
v_res_3192_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_c_3185_, v_a_3186_, v_a_3187_, v_a_3188_, v_a_3189_, v_a_3190_);
lean_dec(v_a_3190_);
lean_dec_ref(v_a_3189_);
lean_dec(v_a_3188_);
lean_dec_ref(v_a_3187_);
lean_dec(v_a_3186_);
lean_dec(v_c_3185_);
return v_res_3192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode(lean_object* v_00_u03b1_3193_, lean_object* v_c_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_){
_start:
{
lean_object* v___x_3201_; 
v___x_3201_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_c_3194_, v_a_3195_, v_a_3196_, v_a_3197_, v_a_3198_, v_a_3199_);
return v___x_3201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode___boxed(lean_object* v_00_u03b1_3202_, lean_object* v_c_3203_, lean_object* v_a_3204_, lean_object* v_a_3205_, lean_object* v_a_3206_, lean_object* v_a_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_){
_start:
{
lean_object* v_res_3210_; 
v_res_3210_ = l_Lean_Meta_LazyDiscrTree_evalNode(v_00_u03b1_3202_, v_c_3203_, v_a_3204_, v_a_3205_, v_a_3206_, v_a_3207_, v_a_3208_);
lean_dec(v_a_3208_);
lean_dec_ref(v_a_3207_);
lean_dec(v_a_3206_);
lean_dec_ref(v_a_3205_);
lean_dec(v_a_3204_);
lean_dec(v_c_3203_);
return v_res_3210_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(lean_object* v_a_3211_, lean_object* v_fallback_3212_, lean_object* v_x_3213_){
_start:
{
if (lean_obj_tag(v_x_3213_) == 0)
{
lean_inc(v_fallback_3212_);
return v_fallback_3212_;
}
else
{
lean_object* v_key_3214_; lean_object* v_value_3215_; lean_object* v_tail_3216_; uint8_t v___x_3217_; 
v_key_3214_ = lean_ctor_get(v_x_3213_, 0);
v_value_3215_ = lean_ctor_get(v_x_3213_, 1);
v_tail_3216_ = lean_ctor_get(v_x_3213_, 2);
v___x_3217_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_3214_, v_a_3211_);
if (v___x_3217_ == 0)
{
v_x_3213_ = v_tail_3216_;
goto _start;
}
else
{
lean_inc(v_value_3215_);
return v_value_3215_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg___boxed(lean_object* v_a_3219_, lean_object* v_fallback_3220_, lean_object* v_x_3221_){
_start:
{
lean_object* v_res_3222_; 
v_res_3222_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(v_a_3219_, v_fallback_3220_, v_x_3221_);
lean_dec(v_x_3221_);
lean_dec(v_fallback_3220_);
lean_dec(v_a_3219_);
return v_res_3222_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(lean_object* v_m_3223_, lean_object* v_a_3224_, lean_object* v_fallback_3225_){
_start:
{
lean_object* v_buckets_3226_; lean_object* v___x_3227_; uint64_t v___x_3228_; uint64_t v___x_3229_; uint64_t v___x_3230_; uint64_t v_fold_3231_; uint64_t v___x_3232_; uint64_t v___x_3233_; uint64_t v___x_3234_; size_t v___x_3235_; size_t v___x_3236_; size_t v___x_3237_; size_t v___x_3238_; size_t v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; 
v_buckets_3226_ = lean_ctor_get(v_m_3223_, 1);
v___x_3227_ = lean_array_get_size(v_buckets_3226_);
v___x_3228_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_a_3224_);
v___x_3229_ = 32ULL;
v___x_3230_ = lean_uint64_shift_right(v___x_3228_, v___x_3229_);
v_fold_3231_ = lean_uint64_xor(v___x_3228_, v___x_3230_);
v___x_3232_ = 16ULL;
v___x_3233_ = lean_uint64_shift_right(v_fold_3231_, v___x_3232_);
v___x_3234_ = lean_uint64_xor(v_fold_3231_, v___x_3233_);
v___x_3235_ = lean_uint64_to_usize(v___x_3234_);
v___x_3236_ = lean_usize_of_nat(v___x_3227_);
v___x_3237_ = ((size_t)1ULL);
v___x_3238_ = lean_usize_sub(v___x_3236_, v___x_3237_);
v___x_3239_ = lean_usize_land(v___x_3235_, v___x_3238_);
v___x_3240_ = lean_array_uget_borrowed(v_buckets_3226_, v___x_3239_);
v___x_3241_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(v_a_3224_, v_fallback_3225_, v___x_3240_);
return v___x_3241_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg___boxed(lean_object* v_m_3242_, lean_object* v_a_3243_, lean_object* v_fallback_3244_){
_start:
{
lean_object* v_res_3245_; 
v_res_3245_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_m_3242_, v_a_3243_, v_fallback_3244_);
lean_dec(v_fallback_3244_);
lean_dec(v_a_3243_);
lean_dec_ref(v_m_3242_);
return v_res_3245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg(lean_object* v_next_3246_, lean_object* v_rest_3247_, lean_object* v_a_3248_, lean_object* v_a_3249_, lean_object* v_a_3250_, lean_object* v_a_3251_, lean_object* v_a_3252_){
_start:
{
lean_object* v___x_3254_; uint8_t v___x_3255_; 
v___x_3254_ = lean_unsigned_to_nat(0u);
v___x_3255_ = lean_nat_dec_eq(v_next_3246_, v___x_3254_);
if (v___x_3255_ == 0)
{
lean_object* v___x_3256_; 
v___x_3256_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_next_3246_, v_a_3248_, v_a_3249_, v_a_3250_, v_a_3251_, v_a_3252_);
if (lean_obj_tag(v___x_3256_) == 0)
{
lean_object* v_a_3257_; lean_object* v___x_3259_; uint8_t v_isShared_3260_; uint8_t v_isSharedCheck_3282_; 
v_a_3257_ = lean_ctor_get(v___x_3256_, 0);
v_isSharedCheck_3282_ = !lean_is_exclusive(v___x_3256_);
if (v_isSharedCheck_3282_ == 0)
{
v___x_3259_ = v___x_3256_;
v_isShared_3260_ = v_isSharedCheck_3282_;
goto v_resetjp_3258_;
}
else
{
lean_inc(v_a_3257_);
lean_dec(v___x_3256_);
v___x_3259_ = lean_box(0);
v_isShared_3260_ = v_isSharedCheck_3282_;
goto v_resetjp_3258_;
}
v_resetjp_3258_:
{
lean_object* v_snd_3261_; 
v_snd_3261_ = lean_ctor_get(v_a_3257_, 1);
lean_inc(v_snd_3261_);
lean_dec(v_a_3257_);
if (lean_obj_tag(v_rest_3247_) == 0)
{
lean_object* v_fst_3262_; lean_object* v_snd_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3271_; 
v_fst_3262_ = lean_ctor_get(v_snd_3261_, 0);
lean_inc(v_fst_3262_);
v_snd_3263_ = lean_ctor_get(v_snd_3261_, 1);
lean_inc(v_snd_3263_);
lean_dec(v_snd_3261_);
v___x_3264_ = lean_st_ref_take(v_a_3248_);
v___x_3265_ = lean_box(0);
v___x_3266_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___x_3267_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3267_, 0, v___x_3266_);
lean_ctor_set(v___x_3267_, 1, v_fst_3262_);
lean_ctor_set(v___x_3267_, 2, v_snd_3263_);
lean_ctor_set(v___x_3267_, 3, v___x_3266_);
v___x_3268_ = lean_array_set(v___x_3264_, v_next_3246_, v___x_3267_);
lean_dec(v_next_3246_);
v___x_3269_ = lean_st_ref_put(v_a_3248_, v___x_3268_);
if (v_isShared_3260_ == 0)
{
lean_ctor_set(v___x_3259_, 0, v___x_3265_);
v___x_3271_ = v___x_3259_;
goto v_reusejp_3270_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v___x_3265_);
v___x_3271_ = v_reuseFailAlloc_3272_;
goto v_reusejp_3270_;
}
v_reusejp_3270_:
{
return v___x_3271_;
}
}
else
{
lean_object* v_fst_3273_; lean_object* v_snd_3274_; lean_object* v_head_3275_; lean_object* v_tail_3276_; lean_object* v___x_3277_; uint8_t v___x_3278_; 
lean_del_object(v___x_3259_);
lean_dec(v_next_3246_);
v_fst_3273_ = lean_ctor_get(v_snd_3261_, 0);
lean_inc(v_fst_3273_);
v_snd_3274_ = lean_ctor_get(v_snd_3261_, 1);
lean_inc(v_snd_3274_);
lean_dec(v_snd_3261_);
v_head_3275_ = lean_ctor_get(v_rest_3247_, 0);
v_tail_3276_ = lean_ctor_get(v_rest_3247_, 1);
v___x_3277_ = lean_box(3);
v___x_3278_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_head_3275_, v___x_3277_);
if (v___x_3278_ == 0)
{
lean_object* v___x_3279_; 
lean_dec(v_fst_3273_);
v___x_3279_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_snd_3274_, v_head_3275_, v___x_3254_);
lean_dec(v_snd_3274_);
v_next_3246_ = v___x_3279_;
v_rest_3247_ = v_tail_3276_;
goto _start;
}
else
{
lean_dec(v_snd_3274_);
v_next_3246_ = v_fst_3273_;
v_rest_3247_ = v_tail_3276_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3290_; 
lean_dec(v_next_3246_);
v_a_3283_ = lean_ctor_get(v___x_3256_, 0);
v_isSharedCheck_3290_ = !lean_is_exclusive(v___x_3256_);
if (v_isSharedCheck_3290_ == 0)
{
v___x_3285_ = v___x_3256_;
v_isShared_3286_ = v_isSharedCheck_3290_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_a_3283_);
lean_dec(v___x_3256_);
v___x_3285_ = lean_box(0);
v_isShared_3286_ = v_isSharedCheck_3290_;
goto v_resetjp_3284_;
}
v_resetjp_3284_:
{
lean_object* v___x_3288_; 
if (v_isShared_3286_ == 0)
{
v___x_3288_ = v___x_3285_;
goto v_reusejp_3287_;
}
else
{
lean_object* v_reuseFailAlloc_3289_; 
v_reuseFailAlloc_3289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3289_, 0, v_a_3283_);
v___x_3288_ = v_reuseFailAlloc_3289_;
goto v_reusejp_3287_;
}
v_reusejp_3287_:
{
return v___x_3288_;
}
}
}
}
else
{
lean_object* v___x_3291_; lean_object* v___x_3292_; 
lean_dec(v_next_3246_);
v___x_3291_ = lean_box(0);
v___x_3292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3292_, 0, v___x_3291_);
return v___x_3292_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg___boxed(lean_object* v_next_3293_, lean_object* v_rest_3294_, lean_object* v_a_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_){
_start:
{
lean_object* v_res_3301_; 
v_res_3301_ = l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg(v_next_3293_, v_rest_3294_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_);
lean_dec(v_a_3299_);
lean_dec_ref(v_a_3298_);
lean_dec(v_a_3297_);
lean_dec_ref(v_a_3296_);
lean_dec(v_a_3295_);
lean_dec(v_rest_3294_);
return v_res_3301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux(lean_object* v_00_u03b1_3302_, lean_object* v_next_3303_, lean_object* v_rest_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_){
_start:
{
lean_object* v___x_3311_; 
v___x_3311_ = l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg(v_next_3303_, v_rest_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_);
return v___x_3311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux___boxed(lean_object* v_00_u03b1_3312_, lean_object* v_next_3313_, lean_object* v_rest_3314_, lean_object* v_a_3315_, lean_object* v_a_3316_, lean_object* v_a_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_, lean_object* v_a_3320_){
_start:
{
lean_object* v_res_3321_; 
v_res_3321_ = l_Lean_Meta_LazyDiscrTree_dropKeyAux(v_00_u03b1_3312_, v_next_3313_, v_rest_3314_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_, v_a_3319_);
lean_dec(v_a_3319_);
lean_dec_ref(v_a_3318_);
lean_dec(v_a_3317_);
lean_dec_ref(v_a_3316_);
lean_dec(v_a_3315_);
lean_dec(v_rest_3314_);
return v_res_3321_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0(lean_object* v_00_u03b2_3322_, lean_object* v_m_3323_, lean_object* v_a_3324_, lean_object* v_fallback_3325_){
_start:
{
lean_object* v___x_3326_; 
v___x_3326_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_m_3323_, v_a_3324_, v_fallback_3325_);
return v___x_3326_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___boxed(lean_object* v_00_u03b2_3327_, lean_object* v_m_3328_, lean_object* v_a_3329_, lean_object* v_fallback_3330_){
_start:
{
lean_object* v_res_3331_; 
v_res_3331_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0(v_00_u03b2_3327_, v_m_3328_, v_a_3329_, v_fallback_3330_);
lean_dec(v_fallback_3330_);
lean_dec(v_a_3329_);
lean_dec_ref(v_m_3328_);
return v_res_3331_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0(lean_object* v_00_u03b2_3332_, lean_object* v_a_3333_, lean_object* v_fallback_3334_, lean_object* v_x_3335_){
_start:
{
lean_object* v___x_3336_; 
v___x_3336_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(v_a_3333_, v_fallback_3334_, v_x_3335_);
return v___x_3336_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3337_, lean_object* v_a_3338_, lean_object* v_fallback_3339_, lean_object* v_x_3340_){
_start:
{
lean_object* v_res_3341_; 
v_res_3341_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0(v_00_u03b2_3337_, v_a_3338_, v_fallback_3339_, v_x_3340_);
lean_dec(v_x_3340_);
lean_dec(v_fallback_3339_);
lean_dec(v_a_3338_);
return v_res_3341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey___redArg(lean_object* v_t_3342_, lean_object* v_path_3343_, lean_object* v_a_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_){
_start:
{
if (lean_obj_tag(v_path_3343_) == 0)
{
lean_object* v___x_3349_; 
v___x_3349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3349_, 0, v_t_3342_);
return v___x_3349_;
}
else
{
lean_object* v_head_3350_; lean_object* v_tail_3351_; lean_object* v_roots_3352_; lean_object* v___x_3353_; lean_object* v_idx_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; 
v_head_3350_ = lean_ctor_get(v_path_3343_, 0);
lean_inc(v_head_3350_);
v_tail_3351_ = lean_ctor_get(v_path_3343_, 1);
lean_inc(v_tail_3351_);
lean_dec_ref_known(v_path_3343_, 2);
v_roots_3352_ = lean_ctor_get(v_t_3342_, 1);
v___x_3353_ = lean_unsigned_to_nat(0u);
v_idx_3354_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_roots_3352_, v_head_3350_, v___x_3353_);
lean_dec(v_head_3350_);
v___x_3355_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_dropKeyAux___boxed), 9, 3);
lean_closure_set(v___x_3355_, 0, lean_box(0));
lean_closure_set(v___x_3355_, 1, v_idx_3354_);
lean_closure_set(v___x_3355_, 2, v_tail_3351_);
v___x_3356_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_t_3342_, v___x_3355_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_);
if (lean_obj_tag(v___x_3356_) == 0)
{
lean_object* v_a_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3365_; 
v_a_3357_ = lean_ctor_get(v___x_3356_, 0);
v_isSharedCheck_3365_ = !lean_is_exclusive(v___x_3356_);
if (v_isSharedCheck_3365_ == 0)
{
v___x_3359_ = v___x_3356_;
v_isShared_3360_ = v_isSharedCheck_3365_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_a_3357_);
lean_dec(v___x_3356_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3365_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
lean_object* v_snd_3361_; lean_object* v___x_3363_; 
v_snd_3361_ = lean_ctor_get(v_a_3357_, 1);
lean_inc(v_snd_3361_);
lean_dec(v_a_3357_);
if (v_isShared_3360_ == 0)
{
lean_ctor_set(v___x_3359_, 0, v_snd_3361_);
v___x_3363_ = v___x_3359_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v_snd_3361_);
v___x_3363_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
return v___x_3363_;
}
}
}
else
{
lean_object* v_a_3366_; lean_object* v___x_3368_; uint8_t v_isShared_3369_; uint8_t v_isSharedCheck_3373_; 
v_a_3366_ = lean_ctor_get(v___x_3356_, 0);
v_isSharedCheck_3373_ = !lean_is_exclusive(v___x_3356_);
if (v_isSharedCheck_3373_ == 0)
{
v___x_3368_ = v___x_3356_;
v_isShared_3369_ = v_isSharedCheck_3373_;
goto v_resetjp_3367_;
}
else
{
lean_inc(v_a_3366_);
lean_dec(v___x_3356_);
v___x_3368_ = lean_box(0);
v_isShared_3369_ = v_isSharedCheck_3373_;
goto v_resetjp_3367_;
}
v_resetjp_3367_:
{
lean_object* v___x_3371_; 
if (v_isShared_3369_ == 0)
{
v___x_3371_ = v___x_3368_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3372_; 
v_reuseFailAlloc_3372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3372_, 0, v_a_3366_);
v___x_3371_ = v_reuseFailAlloc_3372_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
return v___x_3371_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey___redArg___boxed(lean_object* v_t_3374_, lean_object* v_path_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_){
_start:
{
lean_object* v_res_3381_; 
v_res_3381_ = l_Lean_Meta_LazyDiscrTree_dropKey___redArg(v_t_3374_, v_path_3375_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_);
lean_dec(v_a_3379_);
lean_dec_ref(v_a_3378_);
lean_dec(v_a_3377_);
lean_dec_ref(v_a_3376_);
return v_res_3381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey(lean_object* v_00_u03b1_3382_, lean_object* v_t_3383_, lean_object* v_path_3384_, lean_object* v_a_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_){
_start:
{
lean_object* v___x_3390_; 
v___x_3390_ = l_Lean_Meta_LazyDiscrTree_dropKey___redArg(v_t_3383_, v_path_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
return v___x_3390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey___boxed(lean_object* v_00_u03b1_3391_, lean_object* v_t_3392_, lean_object* v_path_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_){
_start:
{
lean_object* v_res_3399_; 
v_res_3399_ = l_Lean_Meta_LazyDiscrTree_dropKey(v_00_u03b1_3391_, v_t_3392_, v_path_3393_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_);
lean_dec(v_a_3397_);
lean_dec_ref(v_a_3396_);
lean_dec(v_a_3395_);
lean_dec_ref(v_a_3394_);
return v_res_3399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(lean_object* v_score_3402_, lean_object* v_e_3403_, lean_object* v_a_3404_){
_start:
{
lean_object* v___x_3405_; uint8_t v___x_3406_; 
v___x_3405_ = lean_array_get_size(v_a_3404_);
v___x_3406_ = lean_nat_dec_lt(v___x_3405_, v_score_3402_);
if (v___x_3406_ == 0)
{
lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3407_ = lean_unsigned_to_nat(1u);
v___x_3408_ = lean_mk_empty_array_with_capacity(v___x_3407_);
v___x_3409_ = lean_array_push(v___x_3408_, v_e_3403_);
v___x_3410_ = lean_array_push(v_a_3404_, v___x_3409_);
return v___x_3410_;
}
else
{
lean_object* v___x_3411_; lean_object* v___x_3412_; 
v___x_3411_ = ((lean_object*)(l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg___closed__0));
v___x_3412_ = lean_array_push(v_a_3404_, v___x_3411_);
v_a_3404_ = v___x_3412_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg___boxed(lean_object* v_score_3414_, lean_object* v_e_3415_, lean_object* v_a_3416_){
_start:
{
lean_object* v_res_3417_; 
v_res_3417_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(v_score_3414_, v_e_3415_, v_a_3416_);
lean_dec(v_score_3414_);
return v_res_3417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop(lean_object* v_00_u03b1_3418_, lean_object* v_score_3419_, lean_object* v_e_3420_, lean_object* v_a_3421_){
_start:
{
lean_object* v___x_3422_; 
v___x_3422_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(v_score_3419_, v_e_3420_, v_a_3421_);
return v___x_3422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___boxed(lean_object* v_00_u03b1_3423_, lean_object* v_score_3424_, lean_object* v_e_3425_, lean_object* v_a_3426_){
_start:
{
lean_object* v_res_3427_; 
v_res_3427_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop(v_00_u03b1_3423_, v_score_3424_, v_e_3425_, v_a_3426_);
lean_dec(v_score_3424_);
return v_res_3427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(lean_object* v_r_3428_, lean_object* v_score_3429_, lean_object* v_e_3430_){
_start:
{
lean_object* v___x_3431_; lean_object* v___x_3432_; uint8_t v___x_3433_; 
v___x_3431_ = lean_array_get_size(v_e_3430_);
v___x_3432_ = lean_unsigned_to_nat(0u);
v___x_3433_ = lean_nat_dec_eq(v___x_3431_, v___x_3432_);
if (v___x_3433_ == 0)
{
lean_object* v___x_3434_; uint8_t v___x_3435_; 
v___x_3434_ = lean_array_get_size(v_r_3428_);
v___x_3435_ = lean_nat_dec_lt(v_score_3429_, v___x_3434_);
if (v___x_3435_ == 0)
{
lean_object* v___x_3436_; 
v___x_3436_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(v_score_3429_, v_e_3430_, v_r_3428_);
return v___x_3436_;
}
else
{
lean_object* v_v_3437_; lean_object* v___x_3438_; lean_object* v_xs_x27_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; 
v_v_3437_ = lean_array_fget(v_r_3428_, v_score_3429_);
v___x_3438_ = lean_box(0);
v_xs_x27_3439_ = lean_array_fset(v_r_3428_, v_score_3429_, v___x_3438_);
v___x_3440_ = lean_array_push(v_v_3437_, v_e_3430_);
v___x_3441_ = lean_array_fset(v_xs_x27_3439_, v_score_3429_, v___x_3440_);
return v___x_3441_;
}
}
else
{
lean_dec_ref(v_e_3430_);
return v_r_3428_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg___boxed(lean_object* v_r_3442_, lean_object* v_score_3443_, lean_object* v_e_3444_){
_start:
{
lean_object* v_res_3445_; 
v_res_3445_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v_r_3442_, v_score_3443_, v_e_3444_);
lean_dec(v_score_3443_);
return v_res_3445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push(lean_object* v_00_u03b1_3446_, lean_object* v_r_3447_, lean_object* v_score_3448_, lean_object* v_e_3449_){
_start:
{
lean_object* v___x_3450_; 
v___x_3450_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v_r_3447_, v_score_3448_, v_e_3449_);
return v___x_3450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push___boxed(lean_object* v_00_u03b1_3451_, lean_object* v_r_3452_, lean_object* v_score_3453_, lean_object* v_e_3454_){
_start:
{
lean_object* v_res_3455_; 
v_res_3455_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push(v_00_u03b1_3451_, v_r_3452_, v_score_3453_, v_e_3454_);
lean_dec(v_score_3453_);
return v_res_3455_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(lean_object* v_as_3456_, size_t v_i_3457_, size_t v_stop_3458_, lean_object* v_b_3459_){
_start:
{
uint8_t v___x_3460_; 
v___x_3460_ = lean_usize_dec_eq(v_i_3457_, v_stop_3458_);
if (v___x_3460_ == 0)
{
lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; size_t v___x_3464_; size_t v___x_3465_; 
v___x_3461_ = lean_array_uget_borrowed(v_as_3456_, v_i_3457_);
v___x_3462_ = lean_array_get_size(v___x_3461_);
v___x_3463_ = lean_nat_add(v_b_3459_, v___x_3462_);
lean_dec(v_b_3459_);
v___x_3464_ = ((size_t)1ULL);
v___x_3465_ = lean_usize_add(v_i_3457_, v___x_3464_);
v_i_3457_ = v___x_3465_;
v_b_3459_ = v___x_3463_;
goto _start;
}
else
{
return v_b_3459_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg___boxed(lean_object* v_as_3467_, lean_object* v_i_3468_, lean_object* v_stop_3469_, lean_object* v_b_3470_){
_start:
{
size_t v_i_boxed_3471_; size_t v_stop_boxed_3472_; lean_object* v_res_3473_; 
v_i_boxed_3471_ = lean_unbox_usize(v_i_3468_);
lean_dec(v_i_3468_);
v_stop_boxed_3472_ = lean_unbox_usize(v_stop_3469_);
lean_dec(v_stop_3469_);
v_res_3473_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v_as_3467_, v_i_boxed_3471_, v_stop_boxed_3472_, v_b_3470_);
lean_dec_ref(v_as_3467_);
return v_res_3473_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(lean_object* v_as_3474_, size_t v_i_3475_, size_t v_stop_3476_, lean_object* v_b_3477_){
_start:
{
lean_object* v___y_3479_; uint8_t v___x_3483_; 
v___x_3483_ = lean_usize_dec_eq(v_i_3475_, v_stop_3476_);
if (v___x_3483_ == 0)
{
lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; uint8_t v___x_3487_; 
v___x_3484_ = lean_array_uget_borrowed(v_as_3474_, v_i_3475_);
v___x_3485_ = lean_unsigned_to_nat(0u);
v___x_3486_ = lean_array_get_size(v___x_3484_);
v___x_3487_ = lean_nat_dec_lt(v___x_3485_, v___x_3486_);
if (v___x_3487_ == 0)
{
v___y_3479_ = v_b_3477_;
goto v___jp_3478_;
}
else
{
size_t v___x_3488_; size_t v___x_3489_; lean_object* v___x_3490_; 
v___x_3488_ = ((size_t)0ULL);
v___x_3489_ = lean_usize_of_nat(v___x_3486_);
v___x_3490_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v___x_3484_, v___x_3488_, v___x_3489_, v_b_3477_);
v___y_3479_ = v___x_3490_;
goto v___jp_3478_;
}
}
else
{
return v_b_3477_;
}
v___jp_3478_:
{
size_t v___x_3480_; size_t v___x_3481_; 
v___x_3480_ = ((size_t)1ULL);
v___x_3481_ = lean_usize_add(v_i_3475_, v___x_3480_);
v_i_3475_ = v___x_3481_;
v_b_3477_ = v___y_3479_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg___boxed(lean_object* v_as_3491_, lean_object* v_i_3492_, lean_object* v_stop_3493_, lean_object* v_b_3494_){
_start:
{
size_t v_i_boxed_3495_; size_t v_stop_boxed_3496_; lean_object* v_res_3497_; 
v_i_boxed_3495_ = lean_unbox_usize(v_i_3492_);
lean_dec(v_i_3492_);
v_stop_boxed_3496_ = lean_unbox_usize(v_stop_3493_);
lean_dec(v_stop_3493_);
v_res_3497_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_as_3491_, v_i_boxed_3495_, v_stop_boxed_3496_, v_b_3494_);
lean_dec_ref(v_as_3491_);
return v_res_3497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(lean_object* v_mr_3498_){
_start:
{
lean_object* v___x_3499_; lean_object* v___x_3500_; uint8_t v___x_3501_; 
v___x_3499_ = lean_unsigned_to_nat(0u);
v___x_3500_ = lean_array_get_size(v_mr_3498_);
v___x_3501_ = lean_nat_dec_lt(v___x_3499_, v___x_3500_);
if (v___x_3501_ == 0)
{
return v___x_3499_;
}
else
{
size_t v___x_3502_; size_t v___x_3503_; lean_object* v___x_3504_; 
v___x_3502_ = ((size_t)0ULL);
v___x_3503_ = lean_usize_of_nat(v___x_3500_);
v___x_3504_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_mr_3498_, v___x_3502_, v___x_3503_, v___x_3499_);
return v___x_3504_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg___boxed(lean_object* v_mr_3505_){
_start:
{
lean_object* v_res_3506_; 
v_res_3506_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_mr_3505_);
lean_dec_ref(v_mr_3505_);
return v_res_3506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size(lean_object* v_00_u03b1_3507_, lean_object* v_mr_3508_){
_start:
{
lean_object* v___x_3509_; 
v___x_3509_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_mr_3508_);
return v___x_3509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size___boxed(lean_object* v_00_u03b1_3510_, lean_object* v_mr_3511_){
_start:
{
lean_object* v_res_3512_; 
v_res_3512_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size(v_00_u03b1_3510_, v_mr_3511_);
lean_dec_ref(v_mr_3511_);
return v_res_3512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0(lean_object* v_00_u03b1_3513_, lean_object* v_as_3514_, size_t v_i_3515_, size_t v_stop_3516_, lean_object* v_b_3517_){
_start:
{
lean_object* v___x_3518_; 
v___x_3518_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v_as_3514_, v_i_3515_, v_stop_3516_, v_b_3517_);
return v___x_3518_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___boxed(lean_object* v_00_u03b1_3519_, lean_object* v_as_3520_, lean_object* v_i_3521_, lean_object* v_stop_3522_, lean_object* v_b_3523_){
_start:
{
size_t v_i_boxed_3524_; size_t v_stop_boxed_3525_; lean_object* v_res_3526_; 
v_i_boxed_3524_ = lean_unbox_usize(v_i_3521_);
lean_dec(v_i_3521_);
v_stop_boxed_3525_ = lean_unbox_usize(v_stop_3522_);
lean_dec(v_stop_3522_);
v_res_3526_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0(v_00_u03b1_3519_, v_as_3520_, v_i_boxed_3524_, v_stop_boxed_3525_, v_b_3523_);
lean_dec_ref(v_as_3520_);
return v_res_3526_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1(lean_object* v_00_u03b1_3527_, lean_object* v_as_3528_, size_t v_i_3529_, size_t v_stop_3530_, lean_object* v_b_3531_){
_start:
{
lean_object* v___x_3532_; 
v___x_3532_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_as_3528_, v_i_3529_, v_stop_3530_, v_b_3531_);
return v___x_3532_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___boxed(lean_object* v_00_u03b1_3533_, lean_object* v_as_3534_, lean_object* v_i_3535_, lean_object* v_stop_3536_, lean_object* v_b_3537_){
_start:
{
size_t v_i_boxed_3538_; size_t v_stop_boxed_3539_; lean_object* v_res_3540_; 
v_i_boxed_3538_ = lean_unbox_usize(v_i_3535_);
lean_dec(v_i_3535_);
v_stop_boxed_3539_ = lean_unbox_usize(v_stop_3536_);
lean_dec(v_stop_3536_);
v_res_3540_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1(v_00_u03b1_3533_, v_as_3534_, v_i_boxed_3538_, v_stop_boxed_3539_, v_b_3537_);
lean_dec_ref(v_as_3534_);
return v_res_3540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__0(lean_object* v_f_3541_, lean_object* v_j_3542_, lean_object* v_x_3543_){
_start:
{
lean_object* v___x_3544_; 
v___x_3544_ = lean_apply_2(v_f_3541_, v_j_3542_, v_x_3543_);
return v___x_3544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1(lean_object* v___f_3564_, lean_object* v_x1_3565_, lean_object* v_x2_3566_){
_start:
{
lean_object* v___x_3567_; size_t v_sz_3568_; size_t v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; 
v___x_3567_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__9));
v_sz_3568_ = lean_array_size(v_x2_3566_);
v___x_3569_ = ((size_t)0ULL);
v___x_3570_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3567_, v___f_3564_, v_sz_3568_, v___x_3569_, v_x2_3566_);
v___x_3571_ = l_Array_append___redArg(v_x1_3565_, v___x_3570_);
lean_dec(v___x_3570_);
return v___x_3571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2(lean_object* v_n_3572_, lean_object* v_mr_3573_, lean_object* v_f_3574_, lean_object* v_i_3575_, lean_object* v_x_3576_, lean_object* v_r_3577_){
_start:
{
lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v_j_3580_; lean_object* v_b_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; uint8_t v___x_3585_; 
v___x_3578_ = lean_unsigned_to_nat(1u);
v___x_3579_ = lean_nat_sub(v_n_3572_, v___x_3578_);
v_j_3580_ = lean_nat_sub(v___x_3579_, v_i_3575_);
lean_dec(v___x_3579_);
v_b_3581_ = lean_array_fget_borrowed(v_mr_3573_, v_j_3580_);
v___x_3582_ = lean_unsigned_to_nat(0u);
v___x_3583_ = lean_array_get_size(v_b_3581_);
v___x_3584_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__9));
v___x_3585_ = lean_nat_dec_lt(v___x_3582_, v___x_3583_);
if (v___x_3585_ == 0)
{
lean_dec(v_j_3580_);
lean_dec(v_f_3574_);
return v_r_3577_;
}
else
{
lean_object* v___f_3586_; lean_object* v___f_3587_; size_t v___x_3588_; size_t v___x_3589_; lean_object* v___x_3590_; 
v___f_3586_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3586_, 0, v_f_3574_);
lean_closure_set(v___f_3586_, 1, v_j_3580_);
v___f_3587_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1), 3, 1);
lean_closure_set(v___f_3587_, 0, v___f_3586_);
v___x_3588_ = ((size_t)0ULL);
v___x_3589_ = lean_usize_of_nat(v___x_3583_);
lean_inc(v_b_3581_);
v___x_3590_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3584_, v___f_3587_, v_b_3581_, v___x_3588_, v___x_3589_, v_r_3577_);
return v___x_3590_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2___boxed(lean_object* v_n_3591_, lean_object* v_mr_3592_, lean_object* v_f_3593_, lean_object* v_i_3594_, lean_object* v_x_3595_, lean_object* v_r_3596_){
_start:
{
lean_object* v_res_3597_; 
v_res_3597_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2(v_n_3591_, v_mr_3592_, v_f_3593_, v_i_3594_, v_x_3595_, v_r_3596_);
lean_dec(v_i_3594_);
lean_dec_ref(v_mr_3592_);
lean_dec(v_n_3591_);
return v_res_3597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg(lean_object* v_mr_3598_, lean_object* v_a_3599_, lean_object* v_f_3600_){
_start:
{
lean_object* v_n_3601_; lean_object* v___f_3602_; lean_object* v___x_3603_; 
v_n_3601_ = lean_array_get_size(v_mr_3598_);
v___f_3602_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_3602_, 0, v_n_3601_);
lean_closure_set(v___f_3602_, 1, v_mr_3598_);
lean_closure_set(v___f_3602_, 2, v_f_3600_);
v___x_3603_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop(lean_box(0), v_n_3601_, v___f_3602_, v_n_3601_, lean_box(0), v_a_3599_);
return v___x_3603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux(lean_object* v_00_u03b1_3604_, lean_object* v_00_u03b2_3605_, lean_object* v_mr_3606_, lean_object* v_a_3607_, lean_object* v_f_3608_){
_start:
{
lean_object* v___x_3609_; 
v___x_3609_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg(v_mr_3606_, v_a_3607_, v_f_3608_);
return v___x_3609_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(size_t v_sz_3610_, size_t v_i_3611_, lean_object* v_bs_3612_){
_start:
{
uint8_t v___x_3613_; 
v___x_3613_ = lean_usize_dec_lt(v_i_3611_, v_sz_3610_);
if (v___x_3613_ == 0)
{
return v_bs_3612_;
}
else
{
lean_object* v_v_3614_; lean_object* v___x_3615_; lean_object* v_bs_x27_3616_; size_t v___x_3617_; size_t v___x_3618_; lean_object* v___x_3619_; 
v_v_3614_ = lean_array_uget(v_bs_3612_, v_i_3611_);
v___x_3615_ = lean_unsigned_to_nat(0u);
v_bs_x27_3616_ = lean_array_uset(v_bs_3612_, v_i_3611_, v___x_3615_);
v___x_3617_ = ((size_t)1ULL);
v___x_3618_ = lean_usize_add(v_i_3611_, v___x_3617_);
v___x_3619_ = lean_array_uset(v_bs_x27_3616_, v_i_3611_, v_v_3614_);
v_i_3611_ = v___x_3618_;
v_bs_3612_ = v___x_3619_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg___boxed(lean_object* v_sz_3621_, lean_object* v_i_3622_, lean_object* v_bs_3623_){
_start:
{
size_t v_sz_boxed_3624_; size_t v_i_boxed_3625_; lean_object* v_res_3626_; 
v_sz_boxed_3624_ = lean_unbox_usize(v_sz_3621_);
lean_dec(v_sz_3621_);
v_i_boxed_3625_ = lean_unbox_usize(v_i_3622_);
lean_dec(v_i_3622_);
v_res_3626_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(v_sz_boxed_3624_, v_i_boxed_3625_, v_bs_3623_);
return v_res_3626_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(lean_object* v_as_3627_, size_t v_i_3628_, size_t v_stop_3629_, lean_object* v_b_3630_){
_start:
{
uint8_t v___x_3631_; 
v___x_3631_ = lean_usize_dec_eq(v_i_3628_, v_stop_3629_);
if (v___x_3631_ == 0)
{
lean_object* v___x_3632_; size_t v_sz_3633_; size_t v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; size_t v___x_3637_; size_t v___x_3638_; 
v___x_3632_ = lean_array_uget_borrowed(v_as_3627_, v_i_3628_);
v_sz_3633_ = lean_array_size(v___x_3632_);
v___x_3634_ = ((size_t)0ULL);
lean_inc(v___x_3632_);
v___x_3635_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(v_sz_3633_, v___x_3634_, v___x_3632_);
v___x_3636_ = l_Array_append___redArg(v_b_3630_, v___x_3635_);
lean_dec_ref(v___x_3635_);
v___x_3637_ = ((size_t)1ULL);
v___x_3638_ = lean_usize_add(v_i_3628_, v___x_3637_);
v_i_3628_ = v___x_3638_;
v_b_3630_ = v___x_3636_;
goto _start;
}
else
{
return v_b_3630_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg___boxed(lean_object* v_as_3640_, lean_object* v_i_3641_, lean_object* v_stop_3642_, lean_object* v_b_3643_){
_start:
{
size_t v_i_boxed_3644_; size_t v_stop_boxed_3645_; lean_object* v_res_3646_; 
v_i_boxed_3644_ = lean_unbox_usize(v_i_3641_);
lean_dec(v_i_3641_);
v_stop_boxed_3645_ = lean_unbox_usize(v_stop_3642_);
lean_dec(v_stop_3642_);
v_res_3646_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(v_as_3640_, v_i_boxed_3644_, v_stop_boxed_3645_, v_b_3643_);
lean_dec_ref(v_as_3640_);
return v_res_3646_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(lean_object* v_n_3647_, lean_object* v_aa_3648_, lean_object* v_n_3649_, lean_object* v_j_3650_, lean_object* v_a_3651_){
_start:
{
lean_object* v_zero_3652_; uint8_t v_isZero_3653_; 
v_zero_3652_ = lean_unsigned_to_nat(0u);
v_isZero_3653_ = lean_nat_dec_eq(v_j_3650_, v_zero_3652_);
if (v_isZero_3653_ == 1)
{
lean_dec(v_j_3650_);
return v_a_3651_;
}
else
{
lean_object* v_one_3654_; lean_object* v_n_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v_j_3658_; lean_object* v_b_3659_; lean_object* v___x_3660_; uint8_t v___x_3661_; 
v_one_3654_ = lean_unsigned_to_nat(1u);
v_n_3655_ = lean_nat_sub(v_j_3650_, v_one_3654_);
v___x_3656_ = lean_nat_sub(v_n_3649_, v_j_3650_);
lean_dec(v_j_3650_);
v___x_3657_ = lean_nat_sub(v_n_3647_, v_one_3654_);
v_j_3658_ = lean_nat_sub(v___x_3657_, v___x_3656_);
lean_dec(v___x_3656_);
lean_dec(v___x_3657_);
v_b_3659_ = lean_array_fget_borrowed(v_aa_3648_, v_j_3658_);
lean_dec(v_j_3658_);
v___x_3660_ = lean_array_get_size(v_b_3659_);
v___x_3661_ = lean_nat_dec_lt(v_zero_3652_, v___x_3660_);
if (v___x_3661_ == 0)
{
v_j_3650_ = v_n_3655_;
goto _start;
}
else
{
size_t v___x_3663_; size_t v___x_3664_; lean_object* v___x_3665_; 
v___x_3663_ = ((size_t)0ULL);
v___x_3664_ = lean_usize_of_nat(v___x_3660_);
v___x_3665_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(v_b_3659_, v___x_3663_, v___x_3664_, v_a_3651_);
v_j_3650_ = v_n_3655_;
v_a_3651_ = v___x_3665_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg___boxed(lean_object* v_n_3667_, lean_object* v_aa_3668_, lean_object* v_n_3669_, lean_object* v_j_3670_, lean_object* v_a_3671_){
_start:
{
lean_object* v_res_3672_; 
v_res_3672_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(v_n_3667_, v_aa_3668_, v_n_3669_, v_j_3670_, v_a_3671_);
lean_dec(v_n_3669_);
lean_dec_ref(v_aa_3668_);
lean_dec(v_n_3667_);
return v_res_3672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(lean_object* v_mr_3673_, lean_object* v_a_3674_){
_start:
{
lean_object* v_n_3675_; lean_object* v___x_3676_; 
v_n_3675_ = lean_array_get_size(v_mr_3673_);
v___x_3676_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(v_n_3675_, v_mr_3673_, v_n_3675_, v_n_3675_, v_a_3674_);
return v___x_3676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg___boxed(lean_object* v_mr_3677_, lean_object* v_a_3678_){
_start:
{
lean_object* v_res_3679_; 
v_res_3679_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3677_, v_a_3678_);
lean_dec_ref(v_mr_3677_);
return v_res_3679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___redArg(lean_object* v_mr_3680_, lean_object* v_a_3681_){
_start:
{
lean_object* v___x_3682_; 
v___x_3682_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3680_, v_a_3681_);
return v___x_3682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___redArg___boxed(lean_object* v_mr_3683_, lean_object* v_a_3684_){
_start:
{
lean_object* v_res_3685_; 
v_res_3685_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___redArg(v_mr_3683_, v_a_3684_);
lean_dec_ref(v_mr_3683_);
return v_res_3685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults(lean_object* v_00_u03b1_3686_, lean_object* v_mr_3687_, lean_object* v_a_3688_){
_start:
{
lean_object* v___x_3689_; 
v___x_3689_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3687_, v_a_3688_);
return v___x_3689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___boxed(lean_object* v_00_u03b1_3690_, lean_object* v_mr_3691_, lean_object* v_a_3692_){
_start:
{
lean_object* v_res_3693_; 
v_res_3693_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults(v_00_u03b1_3690_, v_mr_3691_, v_a_3692_);
lean_dec_ref(v_mr_3691_);
return v_res_3693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0(lean_object* v_00_u03b1_3694_, lean_object* v_mr_3695_, lean_object* v_a_3696_){
_start:
{
lean_object* v___x_3697_; 
v___x_3697_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3695_, v_a_3696_);
return v___x_3697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___boxed(lean_object* v_00_u03b1_3698_, lean_object* v_mr_3699_, lean_object* v_a_3700_){
_start:
{
lean_object* v_res_3701_; 
v_res_3701_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0(v_00_u03b1_3698_, v_mr_3699_, v_a_3700_);
lean_dec_ref(v_mr_3699_);
return v_res_3701_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0(lean_object* v_00_u03b1_3702_, size_t v_sz_3703_, size_t v_i_3704_, lean_object* v_bs_3705_){
_start:
{
lean_object* v___x_3706_; 
v___x_3706_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(v_sz_3703_, v_i_3704_, v_bs_3705_);
return v___x_3706_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3707_, lean_object* v_sz_3708_, lean_object* v_i_3709_, lean_object* v_bs_3710_){
_start:
{
size_t v_sz_boxed_3711_; size_t v_i_boxed_3712_; lean_object* v_res_3713_; 
v_sz_boxed_3711_ = lean_unbox_usize(v_sz_3708_);
lean_dec(v_sz_3708_);
v_i_boxed_3712_ = lean_unbox_usize(v_i_3709_);
lean_dec(v_i_3709_);
v_res_3713_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0(v_00_u03b1_3707_, v_sz_boxed_3711_, v_i_boxed_3712_, v_bs_3710_);
return v_res_3713_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1(lean_object* v_00_u03b1_3714_, lean_object* v_as_3715_, size_t v_i_3716_, size_t v_stop_3717_, lean_object* v_b_3718_){
_start:
{
lean_object* v___x_3719_; 
v___x_3719_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(v_as_3715_, v_i_3716_, v_stop_3717_, v_b_3718_);
return v___x_3719_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3720_, lean_object* v_as_3721_, lean_object* v_i_3722_, lean_object* v_stop_3723_, lean_object* v_b_3724_){
_start:
{
size_t v_i_boxed_3725_; size_t v_stop_boxed_3726_; lean_object* v_res_3727_; 
v_i_boxed_3725_ = lean_unbox_usize(v_i_3722_);
lean_dec(v_i_3722_);
v_stop_boxed_3726_ = lean_unbox_usize(v_stop_3723_);
lean_dec(v_stop_3723_);
v_res_3727_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1(v_00_u03b1_3720_, v_as_3721_, v_i_boxed_3725_, v_stop_boxed_3726_, v_b_3724_);
lean_dec_ref(v_as_3721_);
return v_res_3727_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2(lean_object* v_00_u03b1_3728_, lean_object* v_n_3729_, lean_object* v_aa_3730_, lean_object* v_n_3731_, lean_object* v_j_3732_, lean_object* v_a_3733_, lean_object* v_a_3734_){
_start:
{
lean_object* v___x_3735_; 
v___x_3735_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(v_n_3729_, v_aa_3730_, v_n_3731_, v_j_3732_, v_a_3734_);
return v___x_3735_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___boxed(lean_object* v_00_u03b1_3736_, lean_object* v_n_3737_, lean_object* v_aa_3738_, lean_object* v_n_3739_, lean_object* v_j_3740_, lean_object* v_a_3741_, lean_object* v_a_3742_){
_start:
{
lean_object* v_res_3743_; 
v_res_3743_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2(v_00_u03b1_3736_, v_n_3737_, v_aa_3738_, v_n_3739_, v_j_3740_, v_a_3741_, v_a_3742_);
lean_dec(v_n_3739_);
lean_dec_ref(v_aa_3738_);
lean_dec(v_n_3737_);
return v_res_3743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0(lean_object* v_snd_3751_, lean_object* v___x_3752_, lean_object* v_score_3753_, lean_object* v___x_3754_, lean_object* v_k_3755_, lean_object* v_args_3756_, lean_object* v_cases_3757_){
_start:
{
lean_object* v___x_3758_; 
v___x_3758_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_snd_3751_, v_k_3755_);
if (lean_obj_tag(v___x_3758_) == 0)
{
lean_dec_ref(v___x_3752_);
return v_cases_3757_;
}
else
{
lean_object* v_val_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; 
v_val_3759_ = lean_ctor_get(v___x_3758_, 0);
lean_inc(v_val_3759_);
lean_dec_ref_known(v___x_3758_, 1);
v___x_3760_ = l_Array_append___redArg(v___x_3752_, v_args_3756_);
v___x_3761_ = lean_nat_add(v_score_3753_, v___x_3754_);
v___x_3762_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3762_, 0, v___x_3760_);
lean_ctor_set(v___x_3762_, 1, v___x_3761_);
lean_ctor_set(v___x_3762_, 2, v_val_3759_);
v___x_3763_ = lean_array_push(v_cases_3757_, v___x_3762_);
return v___x_3763_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0___boxed(lean_object* v_snd_3764_, lean_object* v___x_3765_, lean_object* v_score_3766_, lean_object* v___x_3767_, lean_object* v_k_3768_, lean_object* v_args_3769_, lean_object* v_cases_3770_){
_start:
{
lean_object* v_res_3771_; 
v_res_3771_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0(v_snd_3764_, v___x_3765_, v_score_3766_, v___x_3767_, v_k_3768_, v_args_3769_, v_cases_3770_);
lean_dec_ref(v_args_3769_);
lean_dec(v_k_3768_);
lean_dec(v___x_3767_);
lean_dec(v_score_3766_);
lean_dec_ref(v_snd_3764_);
return v_res_3771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(lean_object* v_cases_3772_, lean_object* v_result_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_, lean_object* v_a_3777_, lean_object* v_a_3778_){
_start:
{
lean_object* v___x_3780_; lean_object* v___x_3781_; uint8_t v___x_3782_; 
v___x_3780_ = lean_array_get_size(v_cases_3772_);
v___x_3781_ = lean_unsigned_to_nat(0u);
v___x_3782_ = lean_nat_dec_eq(v___x_3780_, v___x_3781_);
if (v___x_3782_ == 0)
{
lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v_ca_3786_; lean_object* v_todo_3787_; lean_object* v_score_3788_; lean_object* v_c_3789_; lean_object* v___x_3791_; uint8_t v_isShared_3792_; uint8_t v_isSharedCheck_3855_; 
v___x_3783_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedPartialMatch_default));
v___x_3784_ = lean_unsigned_to_nat(1u);
v___x_3785_ = lean_nat_sub(v___x_3780_, v___x_3784_);
v_ca_3786_ = lean_array_get(v___x_3783_, v_cases_3772_, v___x_3785_);
lean_dec(v___x_3785_);
v_todo_3787_ = lean_ctor_get(v_ca_3786_, 0);
v_score_3788_ = lean_ctor_get(v_ca_3786_, 1);
v_c_3789_ = lean_ctor_get(v_ca_3786_, 2);
v_isSharedCheck_3855_ = !lean_is_exclusive(v_ca_3786_);
if (v_isSharedCheck_3855_ == 0)
{
v___x_3791_ = v_ca_3786_;
v_isShared_3792_ = v_isSharedCheck_3855_;
goto v_resetjp_3790_;
}
else
{
lean_inc(v_c_3789_);
lean_inc(v_score_3788_);
lean_inc(v_todo_3787_);
lean_dec(v_ca_3786_);
v___x_3791_ = lean_box(0);
v_isShared_3792_ = v_isSharedCheck_3855_;
goto v_resetjp_3790_;
}
v_resetjp_3790_:
{
lean_object* v___x_3793_; lean_object* v_cases_3794_; lean_object* v___x_3795_; 
v___x_3793_ = l_Lean_instInhabitedExpr;
v_cases_3794_ = lean_array_pop(v_cases_3772_);
v___x_3795_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_c_3789_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_, v_a_3778_);
lean_dec(v_c_3789_);
if (lean_obj_tag(v___x_3795_) == 0)
{
lean_object* v_a_3796_; lean_object* v___y_3798_; uint8_t v___y_3799_; lean_object* v___y_3800_; lean_object* v___y_3801_; lean_object* v_snd_3824_; lean_object* v_fst_3825_; lean_object* v_fst_3826_; lean_object* v_snd_3827_; lean_object* v___x_3828_; uint8_t v___y_3830_; uint8_t v___x_3840_; 
v_a_3796_ = lean_ctor_get(v___x_3795_, 0);
lean_inc(v_a_3796_);
lean_dec_ref_known(v___x_3795_, 1);
v_snd_3824_ = lean_ctor_get(v_a_3796_, 1);
lean_inc(v_snd_3824_);
v_fst_3825_ = lean_ctor_get(v_a_3796_, 0);
lean_inc(v_fst_3825_);
lean_dec(v_a_3796_);
v_fst_3826_ = lean_ctor_get(v_snd_3824_, 0);
lean_inc(v_fst_3826_);
v_snd_3827_ = lean_ctor_get(v_snd_3824_, 1);
lean_inc(v_snd_3827_);
lean_dec(v_snd_3824_);
v___x_3828_ = lean_array_get_size(v_todo_3787_);
v___x_3840_ = lean_nat_dec_eq(v___x_3828_, v___x_3781_);
if (v___x_3840_ == 0)
{
uint8_t v___x_3841_; 
lean_dec(v_fst_3825_);
v___x_3841_ = lean_nat_dec_eq(v_fst_3826_, v___x_3781_);
if (v___x_3841_ == 0)
{
v___y_3830_ = v___x_3840_;
goto v___jp_3829_;
}
else
{
lean_object* v_size_3842_; uint8_t v___x_3843_; 
v_size_3842_ = lean_ctor_get(v_snd_3827_, 0);
v___x_3843_ = lean_nat_dec_eq(v_size_3842_, v___x_3781_);
if (v___x_3843_ == 0)
{
v___y_3830_ = v___x_3843_;
goto v___jp_3829_;
}
else
{
lean_dec(v_snd_3827_);
lean_dec(v_fst_3826_);
lean_del_object(v___x_3791_);
lean_dec(v_score_3788_);
lean_dec_ref(v_todo_3787_);
v_cases_3772_ = v_cases_3794_;
goto _start;
}
}
}
else
{
lean_object* v___x_3845_; 
lean_dec(v_snd_3827_);
lean_dec(v_fst_3826_);
lean_del_object(v___x_3791_);
lean_dec_ref(v_todo_3787_);
v___x_3845_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v_result_3773_, v_score_3788_, v_fst_3825_);
lean_dec(v_score_3788_);
v_cases_3772_ = v_cases_3794_;
v_result_3773_ = v___x_3845_;
goto _start;
}
v___jp_3797_:
{
uint8_t v___x_3802_; lean_object* v___x_3803_; 
v___x_3802_ = 1;
v___x_3803_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v___y_3800_, v___x_3802_, v___y_3799_, v_a_3775_, v_a_3776_, v_a_3777_, v_a_3778_);
if (lean_obj_tag(v___x_3803_) == 0)
{
lean_object* v_a_3804_; lean_object* v_fst_3805_; 
v_a_3804_ = lean_ctor_get(v___x_3803_, 0);
lean_inc(v_a_3804_);
lean_dec_ref_known(v___x_3803_, 1);
v_fst_3805_ = lean_ctor_get(v_a_3804_, 0);
lean_inc(v_fst_3805_);
switch(lean_obj_tag(v_fst_3805_))
{
case 3:
{
lean_dec(v_a_3804_);
lean_dec_ref(v___y_3798_);
v_cases_3772_ = v___y_3801_;
goto _start;
}
case 5:
{
lean_object* v_snd_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; 
v_snd_3807_ = lean_ctor_get(v_a_3804_, 1);
lean_inc(v_snd_3807_);
lean_dec(v_a_3804_);
v___x_3808_ = lean_box(4);
v___x_3809_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
lean_inc_ref(v___y_3798_);
v___x_3810_ = lean_apply_3(v___y_3798_, v___x_3808_, v___x_3809_, v___y_3801_);
v___x_3811_ = lean_apply_3(v___y_3798_, v_fst_3805_, v_snd_3807_, v___x_3810_);
v_cases_3772_ = v___x_3811_;
goto _start;
}
default: 
{
lean_object* v_snd_3813_; lean_object* v___x_3814_; 
v_snd_3813_ = lean_ctor_get(v_a_3804_, 1);
lean_inc(v_snd_3813_);
lean_dec(v_a_3804_);
v___x_3814_ = lean_apply_3(v___y_3798_, v_fst_3805_, v_snd_3813_, v___y_3801_);
v_cases_3772_ = v___x_3814_;
goto _start;
}
}
}
else
{
lean_object* v_a_3816_; lean_object* v___x_3818_; uint8_t v_isShared_3819_; uint8_t v_isSharedCheck_3823_; 
lean_dec_ref(v___y_3801_);
lean_dec_ref(v___y_3798_);
lean_dec_ref(v_result_3773_);
v_a_3816_ = lean_ctor_get(v___x_3803_, 0);
v_isSharedCheck_3823_ = !lean_is_exclusive(v___x_3803_);
if (v_isSharedCheck_3823_ == 0)
{
v___x_3818_ = v___x_3803_;
v_isShared_3819_ = v_isSharedCheck_3823_;
goto v_resetjp_3817_;
}
else
{
lean_inc(v_a_3816_);
lean_dec(v___x_3803_);
v___x_3818_ = lean_box(0);
v_isShared_3819_ = v_isSharedCheck_3823_;
goto v_resetjp_3817_;
}
v_resetjp_3817_:
{
lean_object* v___x_3821_; 
if (v_isShared_3819_ == 0)
{
v___x_3821_ = v___x_3818_;
goto v_reusejp_3820_;
}
else
{
lean_object* v_reuseFailAlloc_3822_; 
v_reuseFailAlloc_3822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3822_, 0, v_a_3816_);
v___x_3821_ = v_reuseFailAlloc_3822_;
goto v_reusejp_3820_;
}
v_reusejp_3820_:
{
return v___x_3821_;
}
}
}
}
v___jp_3829_:
{
lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___f_3834_; uint8_t v___x_3835_; 
v___x_3831_ = lean_nat_sub(v___x_3828_, v___x_3784_);
v___x_3832_ = lean_array_get(v___x_3793_, v_todo_3787_, v___x_3831_);
lean_dec(v___x_3831_);
v___x_3833_ = lean_array_pop(v_todo_3787_);
lean_inc(v_score_3788_);
lean_inc_ref(v___x_3833_);
v___f_3834_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0___boxed), 7, 4);
lean_closure_set(v___f_3834_, 0, v_snd_3827_);
lean_closure_set(v___f_3834_, 1, v___x_3833_);
lean_closure_set(v___f_3834_, 2, v_score_3788_);
lean_closure_set(v___f_3834_, 3, v___x_3784_);
v___x_3835_ = lean_nat_dec_eq(v_fst_3826_, v___x_3781_);
if (v___x_3835_ == 0)
{
lean_object* v___x_3837_; 
if (v_isShared_3792_ == 0)
{
lean_ctor_set(v___x_3791_, 2, v_fst_3826_);
lean_ctor_set(v___x_3791_, 0, v___x_3833_);
v___x_3837_ = v___x_3791_;
goto v_reusejp_3836_;
}
else
{
lean_object* v_reuseFailAlloc_3839_; 
v_reuseFailAlloc_3839_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3839_, 0, v___x_3833_);
lean_ctor_set(v_reuseFailAlloc_3839_, 1, v_score_3788_);
lean_ctor_set(v_reuseFailAlloc_3839_, 2, v_fst_3826_);
v___x_3837_ = v_reuseFailAlloc_3839_;
goto v_reusejp_3836_;
}
v_reusejp_3836_:
{
lean_object* v___x_3838_; 
v___x_3838_ = lean_array_push(v_cases_3794_, v___x_3837_);
v___y_3798_ = v___f_3834_;
v___y_3799_ = v___y_3830_;
v___y_3800_ = v___x_3832_;
v___y_3801_ = v___x_3838_;
goto v___jp_3797_;
}
}
else
{
lean_dec_ref(v___x_3833_);
lean_dec(v_fst_3826_);
lean_del_object(v___x_3791_);
lean_dec(v_score_3788_);
v___y_3798_ = v___f_3834_;
v___y_3799_ = v___y_3830_;
v___y_3800_ = v___x_3832_;
v___y_3801_ = v_cases_3794_;
goto v___jp_3797_;
}
}
}
else
{
lean_object* v_a_3847_; lean_object* v___x_3849_; uint8_t v_isShared_3850_; uint8_t v_isSharedCheck_3854_; 
lean_dec_ref(v_cases_3794_);
lean_del_object(v___x_3791_);
lean_dec(v_score_3788_);
lean_dec_ref(v_todo_3787_);
lean_dec_ref(v_result_3773_);
v_a_3847_ = lean_ctor_get(v___x_3795_, 0);
v_isSharedCheck_3854_ = !lean_is_exclusive(v___x_3795_);
if (v_isSharedCheck_3854_ == 0)
{
v___x_3849_ = v___x_3795_;
v_isShared_3850_ = v_isSharedCheck_3854_;
goto v_resetjp_3848_;
}
else
{
lean_inc(v_a_3847_);
lean_dec(v___x_3795_);
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
lean_dec_ref(v_cases_3772_);
v___x_3856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3856_, 0, v_result_3773_);
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
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1(void){
_start:
{
lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; 
v___x_4100_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__0));
v___x_4101_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2);
v___x_4102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4102_, 0, v___x_4101_);
lean_ctor_set(v___x_4102_, 1, v___x_4100_);
return v___x_4102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg(){
_start:
{
lean_object* v___x_4104_; 
v___x_4104_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1);
return v___x_4104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___boxed(lean_object* v___dummy_4105_){
_start:
{
lean_object* v_res_4106_; 
v_res_4106_ = l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg();
return v_res_4106_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0(void){
_start:
{
lean_object* v___x_4107_; 
v___x_4107_ = l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg();
return v___x_4107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default(lean_object* v_00_u03b1_4108_){
_start:
{
lean_object* v___x_4109_; 
v___x_4109_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0);
return v___x_4109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___redArg(){
_start:
{
lean_object* v___x_4111_; 
v___x_4111_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0);
return v___x_4111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___redArg___boxed(lean_object* v___dummy_4112_){
_start:
{
lean_object* v_res_4113_; 
v_res_4113_ = l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___redArg();
return v_res_4113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree(lean_object* v_a_4114_){
_start:
{
lean_object* v___x_4115_; 
v___x_4115_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0);
return v___x_4115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(lean_object* v_d_4116_, lean_object* v_k_4117_, lean_object* v_f_4118_){
_start:
{
lean_object* v_roots_4119_; lean_object* v_tries_4120_; lean_object* v___x_4121_; 
v_roots_4119_ = lean_ctor_get(v_d_4116_, 0);
v_tries_4120_ = lean_ctor_get(v_d_4116_, 1);
v___x_4121_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_roots_4119_, v_k_4117_);
if (lean_obj_tag(v___x_4121_) == 0)
{
lean_object* v___x_4123_; uint8_t v_isShared_4124_; uint8_t v_isSharedCheck_4133_; 
lean_inc_ref(v_tries_4120_);
lean_inc_ref(v_roots_4119_);
v_isSharedCheck_4133_ = !lean_is_exclusive(v_d_4116_);
if (v_isSharedCheck_4133_ == 0)
{
lean_object* v_unused_4134_; lean_object* v_unused_4135_; 
v_unused_4134_ = lean_ctor_get(v_d_4116_, 1);
lean_dec(v_unused_4134_);
v_unused_4135_ = lean_ctor_get(v_d_4116_, 0);
lean_dec(v_unused_4135_);
v___x_4123_ = v_d_4116_;
v_isShared_4124_ = v_isSharedCheck_4133_;
goto v_resetjp_4122_;
}
else
{
lean_dec(v_d_4116_);
v___x_4123_ = lean_box(0);
v_isShared_4124_ = v_isSharedCheck_4133_;
goto v_resetjp_4122_;
}
v_resetjp_4122_:
{
lean_object* v___x_4125_; lean_object* v_roots_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4131_; 
v___x_4125_ = lean_array_get_size(v_tries_4120_);
v_roots_4126_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_roots_4119_, v_k_4117_, v___x_4125_);
v___x_4127_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__3));
v___x_4128_ = lean_apply_1(v_f_4118_, v___x_4127_);
v___x_4129_ = lean_array_push(v_tries_4120_, v___x_4128_);
if (v_isShared_4124_ == 0)
{
lean_ctor_set(v___x_4123_, 1, v___x_4129_);
lean_ctor_set(v___x_4123_, 0, v_roots_4126_);
v___x_4131_ = v___x_4123_;
goto v_reusejp_4130_;
}
else
{
lean_object* v_reuseFailAlloc_4132_; 
v_reuseFailAlloc_4132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4132_, 0, v_roots_4126_);
lean_ctor_set(v_reuseFailAlloc_4132_, 1, v___x_4129_);
v___x_4131_ = v_reuseFailAlloc_4132_;
goto v_reusejp_4130_;
}
v_reusejp_4130_:
{
return v___x_4131_;
}
}
}
else
{
lean_object* v_val_4136_; lean_object* v___x_4137_; uint8_t v___x_4138_; 
lean_dec(v_k_4117_);
v_val_4136_ = lean_ctor_get(v___x_4121_, 0);
lean_inc(v_val_4136_);
lean_dec_ref_known(v___x_4121_, 1);
v___x_4137_ = lean_array_get_size(v_tries_4120_);
v___x_4138_ = lean_nat_dec_lt(v_val_4136_, v___x_4137_);
if (v___x_4138_ == 0)
{
lean_dec(v_val_4136_);
lean_dec_ref(v_f_4118_);
return v_d_4116_;
}
else
{
lean_object* v___x_4140_; uint8_t v_isShared_4141_; uint8_t v_isSharedCheck_4150_; 
lean_inc_ref(v_tries_4120_);
lean_inc_ref(v_roots_4119_);
v_isSharedCheck_4150_ = !lean_is_exclusive(v_d_4116_);
if (v_isSharedCheck_4150_ == 0)
{
lean_object* v_unused_4151_; lean_object* v_unused_4152_; 
v_unused_4151_ = lean_ctor_get(v_d_4116_, 1);
lean_dec(v_unused_4151_);
v_unused_4152_ = lean_ctor_get(v_d_4116_, 0);
lean_dec(v_unused_4152_);
v___x_4140_ = v_d_4116_;
v_isShared_4141_ = v_isSharedCheck_4150_;
goto v_resetjp_4139_;
}
else
{
lean_dec(v_d_4116_);
v___x_4140_ = lean_box(0);
v_isShared_4141_ = v_isSharedCheck_4150_;
goto v_resetjp_4139_;
}
v_resetjp_4139_:
{
lean_object* v_v_4142_; lean_object* v___x_4143_; lean_object* v_xs_x27_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4148_; 
v_v_4142_ = lean_array_fget(v_tries_4120_, v_val_4136_);
v___x_4143_ = lean_box(0);
v_xs_x27_4144_ = lean_array_fset(v_tries_4120_, v_val_4136_, v___x_4143_);
v___x_4145_ = lean_apply_1(v_f_4118_, v_v_4142_);
v___x_4146_ = lean_array_fset(v_xs_x27_4144_, v_val_4136_, v___x_4145_);
lean_dec(v_val_4136_);
if (v_isShared_4141_ == 0)
{
lean_ctor_set(v___x_4140_, 1, v___x_4146_);
v___x_4148_ = v___x_4140_;
goto v_reusejp_4147_;
}
else
{
lean_object* v_reuseFailAlloc_4149_; 
v_reuseFailAlloc_4149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4149_, 0, v_roots_4119_);
lean_ctor_set(v_reuseFailAlloc_4149_, 1, v___x_4146_);
v___x_4148_ = v_reuseFailAlloc_4149_;
goto v_reusejp_4147_;
}
v_reusejp_4147_:
{
return v___x_4148_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt(lean_object* v_00_u03b1_4153_, lean_object* v_d_4154_, lean_object* v_k_4155_, lean_object* v_f_4156_){
_start:
{
lean_object* v___x_4157_; 
v___x_4157_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(v_d_4154_, v_k_4155_, v_f_4156_);
return v___x_4157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg___lam__0(lean_object* v_e_4158_, lean_object* v_x_4159_){
_start:
{
lean_object* v___x_4160_; 
v___x_4160_ = lean_array_push(v_x_4159_, v_e_4158_);
return v___x_4160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg(lean_object* v_d_4161_, lean_object* v_k_4162_, lean_object* v_e_4163_){
_start:
{
lean_object* v___f_4164_; lean_object* v___x_4165_; 
v___f_4164_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4164_, 0, v_e_4163_);
v___x_4165_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(v_d_4161_, v_k_4162_, v___f_4164_);
return v___x_4165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push(lean_object* v_00_u03b1_4166_, lean_object* v_d_4167_, lean_object* v_k_4168_, lean_object* v_e_4169_){
_start:
{
lean_object* v___x_4170_; 
v___x_4170_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg(v_d_4167_, v_k_4168_, v_e_4169_);
return v___x_4170_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(size_t v_sz_4171_, size_t v_i_4172_, lean_object* v_bs_4173_){
_start:
{
uint8_t v___x_4174_; 
v___x_4174_ = lean_usize_dec_lt(v_i_4172_, v_sz_4171_);
if (v___x_4174_ == 0)
{
return v_bs_4173_;
}
else
{
lean_object* v_v_4175_; lean_object* v___x_4176_; lean_object* v_bs_x27_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; size_t v___x_4181_; size_t v___x_4182_; lean_object* v___x_4183_; 
v_v_4175_ = lean_array_uget(v_bs_4173_, v_i_4172_);
v___x_4176_ = lean_unsigned_to_nat(0u);
v_bs_x27_4177_ = lean_array_uset(v_bs_4173_, v_i_4172_, v___x_4176_);
v___x_4178_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__0));
v___x_4179_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2);
v___x_4180_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4180_, 0, v___x_4178_);
lean_ctor_set(v___x_4180_, 1, v___x_4176_);
lean_ctor_set(v___x_4180_, 2, v___x_4179_);
lean_ctor_set(v___x_4180_, 3, v_v_4175_);
v___x_4181_ = ((size_t)1ULL);
v___x_4182_ = lean_usize_add(v_i_4172_, v___x_4181_);
v___x_4183_ = lean_array_uset(v_bs_x27_4177_, v_i_4172_, v___x_4180_);
v_i_4172_ = v___x_4182_;
v_bs_4173_ = v___x_4183_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg___boxed(lean_object* v_sz_4185_, lean_object* v_i_4186_, lean_object* v_bs_4187_){
_start:
{
size_t v_sz_boxed_4188_; size_t v_i_boxed_4189_; lean_object* v_res_4190_; 
v_sz_boxed_4188_ = lean_unbox_usize(v_sz_4185_);
lean_dec(v_sz_4185_);
v_i_boxed_4189_ = lean_unbox_usize(v_i_4186_);
lean_dec(v_i_4186_);
v_res_4190_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(v_sz_boxed_4188_, v_i_boxed_4189_, v_bs_4187_);
return v_res_4190_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__1(lean_object* v_x_4191_, lean_object* v_x_4192_){
_start:
{
if (lean_obj_tag(v_x_4192_) == 0)
{
return v_x_4191_;
}
else
{
lean_object* v_key_4193_; lean_object* v_value_4194_; lean_object* v_tail_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; 
v_key_4193_ = lean_ctor_get(v_x_4192_, 0);
lean_inc(v_key_4193_);
v_value_4194_ = lean_ctor_get(v_x_4192_, 1);
lean_inc(v_value_4194_);
v_tail_4195_ = lean_ctor_get(v_x_4192_, 2);
lean_inc(v_tail_4195_);
lean_dec_ref_known(v_x_4192_, 3);
v___x_4196_ = lean_unsigned_to_nat(1u);
v___x_4197_ = lean_nat_add(v_value_4194_, v___x_4196_);
lean_dec(v_value_4194_);
v___x_4198_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_x_4191_, v_key_4193_, v___x_4197_);
v_x_4191_ = v___x_4198_;
v_x_4192_ = v_tail_4195_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(lean_object* v_as_4200_, size_t v_i_4201_, size_t v_stop_4202_, lean_object* v_b_4203_){
_start:
{
uint8_t v___x_4204_; 
v___x_4204_ = lean_usize_dec_eq(v_i_4201_, v_stop_4202_);
if (v___x_4204_ == 0)
{
lean_object* v___x_4205_; lean_object* v___x_4206_; size_t v___x_4207_; size_t v___x_4208_; 
v___x_4205_ = lean_array_uget_borrowed(v_as_4200_, v_i_4201_);
lean_inc(v___x_4205_);
v___x_4206_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__1(v_b_4203_, v___x_4205_);
v___x_4207_ = ((size_t)1ULL);
v___x_4208_ = lean_usize_add(v_i_4201_, v___x_4207_);
v_i_4201_ = v___x_4208_;
v_b_4203_ = v___x_4206_;
goto _start;
}
else
{
return v_b_4203_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2___boxed(lean_object* v_as_4210_, lean_object* v_i_4211_, lean_object* v_stop_4212_, lean_object* v_b_4213_){
_start:
{
size_t v_i_boxed_4214_; size_t v_stop_boxed_4215_; lean_object* v_res_4216_; 
v_i_boxed_4214_ = lean_unbox_usize(v_i_4211_);
lean_dec(v_i_4211_);
v_stop_boxed_4215_ = lean_unbox_usize(v_stop_4212_);
lean_dec(v_stop_4212_);
v_res_4216_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(v_as_4210_, v_i_boxed_4214_, v_stop_boxed_4215_, v_b_4213_);
lean_dec_ref(v_as_4210_);
return v_res_4216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(lean_object* v_d_4217_){
_start:
{
lean_object* v_roots_4218_; lean_object* v_tries_4219_; lean_object* v___x_4221_; uint8_t v_isShared_4222_; uint8_t v_isSharedCheck_4242_; 
v_roots_4218_ = lean_ctor_get(v_d_4217_, 0);
v_tries_4219_ = lean_ctor_get(v_d_4217_, 1);
v_isSharedCheck_4242_ = !lean_is_exclusive(v_d_4217_);
if (v_isSharedCheck_4242_ == 0)
{
v___x_4221_ = v_d_4217_;
v_isShared_4222_ = v_isSharedCheck_4242_;
goto v_resetjp_4220_;
}
else
{
lean_inc(v_tries_4219_);
lean_inc(v_roots_4218_);
lean_dec(v_d_4217_);
v___x_4221_ = lean_box(0);
v_isShared_4222_ = v_isSharedCheck_4242_;
goto v_resetjp_4220_;
}
v_resetjp_4220_:
{
lean_object* v___y_4224_; lean_object* v_buckets_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; uint8_t v___x_4238_; 
v_buckets_4235_ = lean_ctor_get(v_roots_4218_, 1);
v___x_4236_ = lean_unsigned_to_nat(0u);
v___x_4237_ = lean_array_get_size(v_buckets_4235_);
v___x_4238_ = lean_nat_dec_lt(v___x_4236_, v___x_4237_);
if (v___x_4238_ == 0)
{
v___y_4224_ = v_roots_4218_;
goto v___jp_4223_;
}
else
{
size_t v___x_4239_; size_t v___x_4240_; lean_object* v___x_4241_; 
lean_inc_ref(v_buckets_4235_);
v___x_4239_ = ((size_t)0ULL);
v___x_4240_ = lean_usize_of_nat(v___x_4237_);
v___x_4241_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(v_buckets_4235_, v___x_4239_, v___x_4240_, v_roots_4218_);
lean_dec_ref(v_buckets_4235_);
v___y_4224_ = v___x_4241_;
goto v___jp_4223_;
}
v___jp_4223_:
{
lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; size_t v_sz_4228_; size_t v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4233_; 
v___x_4225_ = lean_unsigned_to_nat(1u);
v___x_4226_ = lean_mk_empty_array_with_capacity(v___x_4225_);
lean_dec_ref(v___x_4226_);
v___x_4227_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabited___redArg___closed__0);
v_sz_4228_ = lean_array_size(v_tries_4219_);
v___x_4229_ = ((size_t)0ULL);
v___x_4230_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(v_sz_4228_, v___x_4229_, v_tries_4219_);
v___x_4231_ = l_Array_append___redArg(v___x_4227_, v___x_4230_);
lean_dec_ref(v___x_4230_);
if (v_isShared_4222_ == 0)
{
lean_ctor_set(v___x_4221_, 1, v___y_4224_);
lean_ctor_set(v___x_4221_, 0, v___x_4231_);
v___x_4233_ = v___x_4221_;
goto v_reusejp_4232_;
}
else
{
lean_object* v_reuseFailAlloc_4234_; 
v_reuseFailAlloc_4234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4234_, 0, v___x_4231_);
lean_ctor_set(v_reuseFailAlloc_4234_, 1, v___y_4224_);
v___x_4233_ = v_reuseFailAlloc_4234_;
goto v_reusejp_4232_;
}
v_reusejp_4232_:
{
return v___x_4233_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy(lean_object* v_00_u03b1_4243_, lean_object* v_d_4244_){
_start:
{
lean_object* v___x_4245_; 
v___x_4245_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_d_4244_);
return v___x_4245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0(lean_object* v_00_u03b1_4246_, size_t v_sz_4247_, size_t v_i_4248_, lean_object* v_bs_4249_){
_start:
{
lean_object* v___x_4250_; 
v___x_4250_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(v_sz_4247_, v_i_4248_, v_bs_4249_);
return v___x_4250_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___boxed(lean_object* v_00_u03b1_4251_, lean_object* v_sz_4252_, lean_object* v_i_4253_, lean_object* v_bs_4254_){
_start:
{
size_t v_sz_boxed_4255_; size_t v_i_boxed_4256_; lean_object* v_res_4257_; 
v_sz_boxed_4255_ = lean_unbox_usize(v_sz_4252_);
lean_dec(v_sz_4252_);
v_i_boxed_4256_ = lean_unbox_usize(v_i_4253_);
lean_dec(v_i_4253_);
v_res_4257_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0(v_00_u03b1_4251_, v_sz_boxed_4255_, v_i_boxed_4256_, v_bs_4254_);
return v_res_4257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___lam__0(lean_object* v_y_4258_, lean_object* v_x_4259_){
_start:
{
lean_object* v___x_4260_; 
v___x_4260_ = l_Array_append___redArg(v_x_4259_, v_y_4258_);
return v___x_4260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___lam__0___boxed(lean_object* v_y_4261_, lean_object* v_x_4262_){
_start:
{
lean_object* v_res_4263_; 
v_res_4263_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___lam__0(v_y_4261_, v_x_4262_);
lean_dec_ref(v_y_4261_);
return v_res_4263_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4264_; 
v___x_4264_ = l_Array_instInhabited___redArg();
return v___x_4264_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(lean_object* v_tries_4265_, lean_object* v_snd_4266_, lean_object* v_x_4267_, lean_object* v_x_4268_){
_start:
{
if (lean_obj_tag(v_x_4268_) == 0)
{
lean_dec_ref(v_snd_4266_);
return v_x_4267_;
}
else
{
lean_object* v_key_4269_; lean_object* v_value_4270_; lean_object* v_tail_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; 
v_key_4269_ = lean_ctor_get(v_x_4268_, 0);
lean_inc(v_key_4269_);
v_value_4270_ = lean_ctor_get(v_x_4268_, 1);
lean_inc(v_value_4270_);
v_tail_4271_ = lean_ctor_get(v_x_4268_, 2);
lean_inc(v_tail_4271_);
lean_dec_ref_known(v_x_4268_, 3);
v___x_4272_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0);
v___x_4273_ = lean_array_get_borrowed(v___x_4272_, v_tries_4265_, v_value_4270_);
lean_dec(v_value_4270_);
lean_inc_ref(v_snd_4266_);
lean_inc(v___x_4273_);
v___x_4274_ = lean_apply_1(v_snd_4266_, v___x_4273_);
v___x_4275_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(v_x_4267_, v_key_4269_, v___x_4274_);
v_x_4267_ = v___x_4275_;
v_x_4268_ = v_tail_4271_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___boxed(lean_object* v_tries_4277_, lean_object* v_snd_4278_, lean_object* v_x_4279_, lean_object* v_x_4280_){
_start:
{
lean_object* v_res_4281_; 
v_res_4281_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(v_tries_4277_, v_snd_4278_, v_x_4279_, v_x_4280_);
lean_dec_ref(v_tries_4277_);
return v_res_4281_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(lean_object* v_tries_4282_, lean_object* v_snd_4283_, lean_object* v_as_4284_, size_t v_i_4285_, size_t v_stop_4286_, lean_object* v_b_4287_){
_start:
{
uint8_t v___x_4288_; 
v___x_4288_ = lean_usize_dec_eq(v_i_4285_, v_stop_4286_);
if (v___x_4288_ == 0)
{
lean_object* v___x_4289_; lean_object* v___x_4290_; size_t v___x_4291_; size_t v___x_4292_; 
v___x_4289_ = lean_array_uget_borrowed(v_as_4284_, v_i_4285_);
lean_inc(v___x_4289_);
lean_inc_ref(v_snd_4283_);
v___x_4290_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(v_tries_4282_, v_snd_4283_, v_b_4287_, v___x_4289_);
v___x_4291_ = ((size_t)1ULL);
v___x_4292_ = lean_usize_add(v_i_4285_, v___x_4291_);
v_i_4285_ = v___x_4292_;
v_b_4287_ = v___x_4290_;
goto _start;
}
else
{
lean_dec_ref(v_snd_4283_);
return v_b_4287_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg___boxed(lean_object* v_tries_4294_, lean_object* v_snd_4295_, lean_object* v_as_4296_, lean_object* v_i_4297_, lean_object* v_stop_4298_, lean_object* v_b_4299_){
_start:
{
size_t v_i_boxed_4300_; size_t v_stop_boxed_4301_; lean_object* v_res_4302_; 
v_i_boxed_4300_ = lean_unbox_usize(v_i_4297_);
lean_dec(v_i_4297_);
v_stop_boxed_4301_ = lean_unbox_usize(v_stop_4298_);
lean_dec(v_stop_4298_);
v_res_4302_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(v_tries_4294_, v_snd_4295_, v_as_4296_, v_i_boxed_4300_, v_stop_boxed_4301_, v_b_4299_);
lean_dec_ref(v_as_4296_);
lean_dec_ref(v_tries_4294_);
return v_res_4302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg(lean_object* v_x_4305_, lean_object* v_y_4306_){
_start:
{
lean_object* v_fst_4308_; lean_object* v_buckets_4309_; lean_object* v_tries_4310_; lean_object* v_snd_4311_; lean_object* v_roots_4318_; lean_object* v_roots_4319_; lean_object* v_tries_4320_; lean_object* v_size_4321_; lean_object* v_buckets_4322_; lean_object* v_tries_4323_; lean_object* v_size_4324_; lean_object* v_buckets_4325_; uint8_t v___x_4326_; 
v_roots_4318_ = lean_ctor_get(v_y_4306_, 0);
v_roots_4319_ = lean_ctor_get(v_x_4305_, 0);
v_tries_4320_ = lean_ctor_get(v_y_4306_, 1);
v_size_4321_ = lean_ctor_get(v_roots_4318_, 0);
v_buckets_4322_ = lean_ctor_get(v_roots_4318_, 1);
v_tries_4323_ = lean_ctor_get(v_x_4305_, 1);
v_size_4324_ = lean_ctor_get(v_roots_4319_, 0);
v_buckets_4325_ = lean_ctor_get(v_roots_4319_, 1);
v___x_4326_ = lean_nat_dec_le(v_size_4321_, v_size_4324_);
if (v___x_4326_ == 0)
{
lean_object* v___f_4327_; 
lean_inc_ref(v_buckets_4325_);
lean_inc_ref(v_tries_4323_);
lean_dec_ref(v_x_4305_);
v___f_4327_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___closed__0));
v_fst_4308_ = v_y_4306_;
v_buckets_4309_ = v_buckets_4325_;
v_tries_4310_ = v_tries_4323_;
v_snd_4311_ = v___f_4327_;
goto v___jp_4307_;
}
else
{
lean_object* v___f_4328_; 
lean_inc_ref(v_buckets_4322_);
lean_inc_ref(v_tries_4320_);
lean_dec_ref(v_y_4306_);
v___f_4328_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___closed__1));
v_fst_4308_ = v_x_4305_;
v_buckets_4309_ = v_buckets_4322_;
v_tries_4310_ = v_tries_4320_;
v_snd_4311_ = v___f_4328_;
goto v___jp_4307_;
}
v___jp_4307_:
{
lean_object* v___x_4312_; lean_object* v___x_4313_; uint8_t v___x_4314_; 
v___x_4312_ = lean_unsigned_to_nat(0u);
v___x_4313_ = lean_array_get_size(v_buckets_4309_);
v___x_4314_ = lean_nat_dec_lt(v___x_4312_, v___x_4313_);
if (v___x_4314_ == 0)
{
lean_dec_ref(v_tries_4310_);
lean_dec_ref(v_buckets_4309_);
return v_fst_4308_;
}
else
{
size_t v___x_4315_; size_t v___x_4316_; lean_object* v___x_4317_; 
v___x_4315_ = ((size_t)0ULL);
v___x_4316_ = lean_usize_of_nat(v___x_4313_);
lean_inc_ref(v_snd_4311_);
v___x_4317_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(v_tries_4310_, v_snd_4311_, v_buckets_4309_, v___x_4315_, v___x_4316_, v_fst_4308_);
lean_dec_ref(v_buckets_4309_);
lean_dec_ref(v_tries_4310_);
return v___x_4317_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append(lean_object* v_00_u03b1_4329_, lean_object* v_x_4330_, lean_object* v_y_4331_){
_start:
{
lean_object* v___x_4332_; 
v___x_4332_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg(v_x_4330_, v_y_4331_);
return v___x_4332_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0(lean_object* v_00_u03b1_4333_, lean_object* v_tries_4334_, lean_object* v_snd_4335_, lean_object* v_x_4336_, lean_object* v_x_4337_){
_start:
{
lean_object* v___x_4338_; 
v___x_4338_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(v_tries_4334_, v_snd_4335_, v_x_4336_, v_x_4337_);
return v___x_4338_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___boxed(lean_object* v_00_u03b1_4339_, lean_object* v_tries_4340_, lean_object* v_snd_4341_, lean_object* v_x_4342_, lean_object* v_x_4343_){
_start:
{
lean_object* v_res_4344_; 
v_res_4344_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0(v_00_u03b1_4339_, v_tries_4340_, v_snd_4341_, v_x_4342_, v_x_4343_);
lean_dec_ref(v_tries_4340_);
return v_res_4344_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1(lean_object* v_00_u03b1_4345_, lean_object* v_tries_4346_, lean_object* v_snd_4347_, lean_object* v_as_4348_, size_t v_i_4349_, size_t v_stop_4350_, lean_object* v_b_4351_){
_start:
{
lean_object* v___x_4352_; 
v___x_4352_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(v_tries_4346_, v_snd_4347_, v_as_4348_, v_i_4349_, v_stop_4350_, v_b_4351_);
return v___x_4352_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___boxed(lean_object* v_00_u03b1_4353_, lean_object* v_tries_4354_, lean_object* v_snd_4355_, lean_object* v_as_4356_, lean_object* v_i_4357_, lean_object* v_stop_4358_, lean_object* v_b_4359_){
_start:
{
size_t v_i_boxed_4360_; size_t v_stop_boxed_4361_; lean_object* v_res_4362_; 
v_i_boxed_4360_ = lean_unbox_usize(v_i_4357_);
lean_dec(v_i_4357_);
v_stop_boxed_4361_ = lean_unbox_usize(v_stop_4358_);
lean_dec(v_stop_4358_);
v_res_4362_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1(v_00_u03b1_4353_, v_tries_4354_, v_snd_4355_, v_as_4356_, v_i_boxed_4360_, v_stop_boxed_4361_, v_b_4359_);
lean_dec_ref(v_as_4356_);
lean_dec_ref(v_tries_4354_);
return v_res_4362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend___redArg(){
_start:
{
lean_object* v___x_4365_; 
v___x_4365_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend___redArg___closed__0));
return v___x_4365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend___redArg___boxed(lean_object* v___dummy_4366_){
_start:
{
lean_object* v_res_4367_; 
v_res_4367_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend___redArg();
return v_res_4367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend(lean_object* v_00_u03b1_4368_){
_start:
{
lean_object* v___x_4369_; 
v___x_4369_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend___redArg___closed__0));
return v___x_4369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(lean_object* v_expr_4370_, lean_object* v_value_4371_, lean_object* v_a_4372_, lean_object* v_a_4373_, lean_object* v_a_4374_, lean_object* v_a_4375_){
_start:
{
lean_object* v_lctx_4377_; lean_object* v_localInstances_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; 
v_lctx_4377_ = lean_ctor_get(v_a_4372_, 2);
v_localInstances_4378_ = lean_ctor_get(v_a_4372_, 3);
lean_inc_ref(v_localInstances_4378_);
lean_inc_ref(v_lctx_4377_);
v___x_4379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4379_, 0, v_lctx_4377_);
lean_ctor_set(v___x_4379_, 1, v_localInstances_4378_);
v___x_4380_ = l_Lean_Meta_LazyDiscrTree_rootKey(v_expr_4370_, v_a_4372_, v_a_4373_, v_a_4374_, v_a_4375_);
if (lean_obj_tag(v___x_4380_) == 0)
{
lean_object* v_a_4381_; lean_object* v___x_4383_; uint8_t v_isShared_4384_; uint8_t v_isSharedCheck_4399_; 
v_a_4381_ = lean_ctor_get(v___x_4380_, 0);
v_isSharedCheck_4399_ = !lean_is_exclusive(v___x_4380_);
if (v_isSharedCheck_4399_ == 0)
{
v___x_4383_ = v___x_4380_;
v_isShared_4384_ = v_isSharedCheck_4399_;
goto v_resetjp_4382_;
}
else
{
lean_inc(v_a_4381_);
lean_dec(v___x_4380_);
v___x_4383_ = lean_box(0);
v_isShared_4384_ = v_isSharedCheck_4399_;
goto v_resetjp_4382_;
}
v_resetjp_4382_:
{
lean_object* v_fst_4385_; lean_object* v_snd_4386_; lean_object* v___x_4388_; uint8_t v_isShared_4389_; uint8_t v_isSharedCheck_4398_; 
v_fst_4385_ = lean_ctor_get(v_a_4381_, 0);
v_snd_4386_ = lean_ctor_get(v_a_4381_, 1);
v_isSharedCheck_4398_ = !lean_is_exclusive(v_a_4381_);
if (v_isSharedCheck_4398_ == 0)
{
v___x_4388_ = v_a_4381_;
v_isShared_4389_ = v_isSharedCheck_4398_;
goto v_resetjp_4387_;
}
else
{
lean_inc(v_snd_4386_);
lean_inc(v_fst_4385_);
lean_dec(v_a_4381_);
v___x_4388_ = lean_box(0);
v_isShared_4389_ = v_isSharedCheck_4398_;
goto v_resetjp_4387_;
}
v_resetjp_4387_:
{
lean_object* v___x_4391_; 
if (v_isShared_4389_ == 0)
{
lean_ctor_set(v___x_4388_, 1, v_value_4371_);
lean_ctor_set(v___x_4388_, 0, v___x_4379_);
v___x_4391_ = v___x_4388_;
goto v_reusejp_4390_;
}
else
{
lean_object* v_reuseFailAlloc_4397_; 
v_reuseFailAlloc_4397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4397_, 0, v___x_4379_);
lean_ctor_set(v_reuseFailAlloc_4397_, 1, v_value_4371_);
v___x_4391_ = v_reuseFailAlloc_4397_;
goto v_reusejp_4390_;
}
v_reusejp_4390_:
{
lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4395_; 
v___x_4392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4392_, 0, v_snd_4386_);
lean_ctor_set(v___x_4392_, 1, v___x_4391_);
v___x_4393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4393_, 0, v_fst_4385_);
lean_ctor_set(v___x_4393_, 1, v___x_4392_);
if (v_isShared_4384_ == 0)
{
lean_ctor_set(v___x_4383_, 0, v___x_4393_);
v___x_4395_ = v___x_4383_;
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
lean_dec_ref_known(v___x_4379_, 2);
lean_dec(v_value_4371_);
v_a_4400_ = lean_ctor_get(v___x_4380_, 0);
v_isSharedCheck_4407_ = !lean_is_exclusive(v___x_4380_);
if (v_isSharedCheck_4407_ == 0)
{
v___x_4402_ = v___x_4380_;
v_isShared_4403_ = v_isSharedCheck_4407_;
goto v_resetjp_4401_;
}
else
{
lean_inc(v_a_4400_);
lean_dec(v___x_4380_);
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
v___x_4526_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
v_isModule_4543_ = lean_ctor_get_uint8(v___x_4542_, sizeof(void*)*8 + 4);
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
lean_object* v___x_4564_; uint8_t v___x_4565_; 
v___x_4564_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__1));
v___x_4565_ = lean_name_eq(v_declName_4561_, v___x_4564_);
if (v___x_4565_ == 0)
{
uint8_t v___x_4574_; 
lean_inc(v_declName_4561_);
v___x_4574_ = l_Lean_Name_isInternalDetail(v_declName_4561_);
if (v___x_4574_ == 0)
{
lean_dec_ref(v_env_4560_);
goto v___jp_4570_;
}
else
{
uint8_t v___x_4575_; 
v___x_4575_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName(v_env_4560_, v_declName_4561_);
lean_dec_ref(v_env_4560_);
if (v___x_4575_ == 0)
{
lean_dec(v_declName_4561_);
return v___x_4574_;
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_blacklistInsertion___boxed(lean_object* v_env_4576_, lean_object* v_declName_4577_){
_start:
{
uint8_t v_res_4578_; lean_object* v_r_4579_; 
v_res_4578_ = l_Lean_Meta_LazyDiscrTree_blacklistInsertion(v_env_4576_, v_declName_4577_);
v_r_4579_ = lean_box(v_res_4578_);
return v_r_4579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(lean_object* v_opts_4580_, lean_object* v_opt_4581_){
_start:
{
lean_object* v_name_4582_; lean_object* v_defValue_4583_; lean_object* v_map_4584_; lean_object* v___x_4585_; 
v_name_4582_ = lean_ctor_get(v_opt_4581_, 0);
v_defValue_4583_ = lean_ctor_get(v_opt_4581_, 1);
v_map_4584_ = lean_ctor_get(v_opts_4580_, 0);
v___x_4585_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4584_, v_name_4582_);
if (lean_obj_tag(v___x_4585_) == 0)
{
lean_inc(v_defValue_4583_);
return v_defValue_4583_;
}
else
{
lean_object* v_val_4586_; 
v_val_4586_ = lean_ctor_get(v___x_4585_, 0);
lean_inc(v_val_4586_);
lean_dec_ref_known(v___x_4585_, 1);
if (lean_obj_tag(v_val_4586_) == 3)
{
lean_object* v_v_4587_; 
v_v_4587_ = lean_ctor_get(v_val_4586_, 0);
lean_inc(v_v_4587_);
lean_dec_ref_known(v_val_4586_, 1);
return v_v_4587_;
}
else
{
lean_dec(v_val_4586_);
lean_inc(v_defValue_4583_);
return v_defValue_4583_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0___boxed(lean_object* v_opts_4588_, lean_object* v_opt_4589_){
_start:
{
lean_object* v_res_4590_; 
v_res_4590_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(v_opts_4588_, v_opt_4589_);
lean_dec_ref(v_opt_4589_);
lean_dec_ref(v_opts_4588_);
return v_res_4590_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1___redArg(lean_object* v_as_4591_, size_t v_i_4592_, size_t v_stop_4593_, lean_object* v_b_4594_){
_start:
{
uint8_t v___x_4595_; 
v___x_4595_ = lean_usize_dec_eq(v_i_4592_, v_stop_4593_);
if (v___x_4595_ == 0)
{
lean_object* v___x_4596_; lean_object* v_key_4597_; lean_object* v_entry_4598_; lean_object* v___x_4599_; size_t v___x_4600_; size_t v___x_4601_; 
v___x_4596_ = lean_array_uget_borrowed(v_as_4591_, v_i_4592_);
v_key_4597_ = lean_ctor_get(v___x_4596_, 0);
v_entry_4598_ = lean_ctor_get(v___x_4596_, 1);
lean_inc_ref(v_entry_4598_);
lean_inc(v_key_4597_);
v___x_4599_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg(v_b_4594_, v_key_4597_, v_entry_4598_);
v___x_4600_ = ((size_t)1ULL);
v___x_4601_ = lean_usize_add(v_i_4592_, v___x_4600_);
v_i_4592_ = v___x_4601_;
v_b_4594_ = v___x_4599_;
goto _start;
}
else
{
return v_b_4594_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1___redArg___boxed(lean_object* v_as_4603_, lean_object* v_i_4604_, lean_object* v_stop_4605_, lean_object* v_b_4606_){
_start:
{
size_t v_i_boxed_4607_; size_t v_stop_boxed_4608_; lean_object* v_res_4609_; 
v_i_boxed_4607_ = lean_unbox_usize(v_i_4604_);
lean_dec(v_i_4604_);
v_stop_boxed_4608_ = lean_unbox_usize(v_stop_4605_);
lean_dec(v_stop_4605_);
v_res_4609_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1___redArg(v_as_4603_, v_i_boxed_4607_, v_stop_boxed_4608_, v_b_4606_);
lean_dec_ref(v_as_4603_);
return v_res_4609_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0(void){
_start:
{
lean_object* v___x_4610_; lean_object* v___x_4611_; 
v___x_4610_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0);
v___x_4611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4611_, 0, v___x_4610_);
return v___x_4611_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1(void){
_start:
{
lean_object* v___x_4612_; lean_object* v___x_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; 
v___x_4612_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_4613_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0);
v___x_4614_ = lean_unsigned_to_nat(0u);
v___x_4615_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_4615_, 0, v___x_4614_);
lean_ctor_set(v___x_4615_, 1, v___x_4614_);
lean_ctor_set(v___x_4615_, 2, v___x_4614_);
lean_ctor_set(v___x_4615_, 3, v___x_4614_);
lean_ctor_set(v___x_4615_, 4, v___x_4613_);
lean_ctor_set(v___x_4615_, 5, v___x_4613_);
lean_ctor_set(v___x_4615_, 6, v___x_4613_);
lean_ctor_set(v___x_4615_, 7, v___x_4613_);
lean_ctor_set(v___x_4615_, 8, v___x_4613_);
lean_ctor_set(v___x_4615_, 9, v___x_4613_);
lean_ctor_set(v___x_4615_, 10, v___x_4613_);
lean_ctor_set(v___x_4615_, 11, v___x_4612_);
return v___x_4615_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2(void){
_start:
{
lean_object* v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; 
v___x_4616_ = lean_unsigned_to_nat(32u);
v___x_4617_ = lean_mk_empty_array_with_capacity(v___x_4616_);
v___x_4618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4618_, 0, v___x_4617_);
return v___x_4618_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3(void){
_start:
{
size_t v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; 
v___x_4619_ = ((size_t)5ULL);
v___x_4620_ = lean_unsigned_to_nat(0u);
v___x_4621_ = lean_unsigned_to_nat(32u);
v___x_4622_ = lean_mk_empty_array_with_capacity(v___x_4621_);
v___x_4623_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2);
v___x_4624_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4624_, 0, v___x_4623_);
lean_ctor_set(v___x_4624_, 1, v___x_4622_);
lean_ctor_set(v___x_4624_, 2, v___x_4620_);
lean_ctor_set(v___x_4624_, 3, v___x_4620_);
lean_ctor_set_usize(v___x_4624_, 4, v___x_4619_);
return v___x_4624_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4(void){
_start:
{
lean_object* v___x_4625_; lean_object* v___x_4626_; 
v___x_4625_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0);
v___x_4626_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4626_, 0, v___x_4625_);
lean_ctor_set(v___x_4626_, 1, v___x_4625_);
lean_ctor_set(v___x_4626_, 2, v___x_4625_);
lean_ctor_set(v___x_4626_, 3, v___x_4625_);
lean_ctor_set(v___x_4626_, 4, v___x_4625_);
return v___x_4626_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5(void){
_start:
{
lean_object* v___x_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; lean_object* v___x_4630_; 
v___x_4627_ = lean_box(1);
v___x_4628_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3);
v___x_4629_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0);
v___x_4630_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4630_, 0, v___x_4629_);
lean_ctor_set(v___x_4630_, 1, v___x_4628_);
lean_ctor_set(v___x_4630_, 2, v___x_4627_);
return v___x_4630_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__7(void){
_start:
{
lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; 
v___x_4633_ = lean_unsigned_to_nat(1u);
v___x_4634_ = l_Lean_firstFrontendMacroScope;
v___x_4635_ = lean_nat_add(v___x_4634_, v___x_4633_);
return v___x_4635_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__9(void){
_start:
{
lean_object* v___x_4640_; uint64_t v___x_4641_; lean_object* v___x_4642_; 
v___x_4640_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3);
v___x_4641_ = 0ULL;
v___x_4642_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4642_, 0, v___x_4640_);
lean_ctor_set_uint64(v___x_4642_, sizeof(void*)*1, v___x_4641_);
return v___x_4642_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10(void){
_start:
{
lean_object* v___x_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; 
v___x_4643_ = lean_unsigned_to_nat(0u);
v___x_4644_ = l_Lean_Options_empty;
v___x_4645_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6));
v___x_4646_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4646_, 0, v___x_4645_);
lean_ctor_set(v___x_4646_, 1, v___x_4644_);
lean_ctor_set(v___x_4646_, 2, v___x_4645_);
lean_ctor_set(v___x_4646_, 3, v___x_4643_);
lean_ctor_set(v___x_4646_, 4, v___x_4643_);
lean_ctor_set(v___x_4646_, 5, v___x_4643_);
return v___x_4646_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11(void){
_start:
{
lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; 
v___x_4647_ = l_Lean_NameSet_empty;
v___x_4648_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3);
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
v___x_4650_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3);
v___x_4651_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0);
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
v___x_4654_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0);
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
lean_object* v___x_4668_; uint8_t v___x_4669_; lean_object* v___x_4670_; lean_object* v_ngen_4671_; lean_object* v_core_4672_; lean_object* v_meta_4673_; lean_object* v___x_4675_; uint8_t v_isShared_4676_; uint8_t v_isSharedCheck_4797_; 
v___x_4668_ = lean_box(1);
v___x_4669_ = 1;
v___x_4670_ = lean_st_ref_get(v_cacheRef_4660_);
v_ngen_4671_ = lean_ctor_get(v___x_4670_, 0);
v_core_4672_ = lean_ctor_get(v___x_4670_, 1);
v_meta_4673_ = lean_ctor_get(v___x_4670_, 2);
v_isSharedCheck_4797_ = !lean_is_exclusive(v___x_4670_);
if (v_isSharedCheck_4797_ == 0)
{
v___x_4675_ = v___x_4670_;
v_isShared_4676_ = v_isSharedCheck_4797_;
goto v_resetjp_4674_;
}
else
{
lean_inc(v_meta_4673_);
lean_inc(v_core_4672_);
lean_inc(v_ngen_4671_);
lean_dec(v___x_4670_);
v___x_4675_ = lean_box(0);
v_isShared_4676_ = v_isSharedCheck_4797_;
goto v_resetjp_4674_;
}
v_resetjp_4674_:
{
lean_object* v___x_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; uint8_t v___x_4684_; uint8_t v___x_4685_; uint8_t v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; uint16_t v___y_4702_; lean_object* v___y_4703_; lean_object* v_fileName_4704_; lean_object* v_fileMap_4705_; lean_object* v_currNamespace_4706_; lean_object* v_openDecls_4707_; lean_object* v_initHeartbeats_4708_; lean_object* v_maxHeartbeats_4709_; lean_object* v_quotContext_4710_; lean_object* v_currMacroScope_4711_; lean_object* v_cancelTk_x3f_4712_; lean_object* v_inheritedTraceOptions_4713_; lean_object* v_currRecDepth_4714_; lean_object* v_ref_4715_; uint8_t v_suppressElabErrors_4716_; uint8_t v_isRecordingDeps_4717_; lean_object* v___x_4744_; lean_object* v___x_4745_; lean_object* v_toCold_4746_; lean_object* v_currRecDepth_4747_; lean_object* v_ref_4748_; uint8_t v_suppressElabErrors_4749_; uint8_t v_isRecordingDeps_4750_; lean_object* v_fileName_4751_; lean_object* v_fileMap_4752_; lean_object* v_options_4753_; lean_object* v_currNamespace_4754_; lean_object* v_openDecls_4755_; lean_object* v_initHeartbeats_4756_; lean_object* v_maxHeartbeats_4757_; lean_object* v_quotContext_4758_; lean_object* v_currMacroScope_4759_; lean_object* v_cancelTk_x3f_4760_; uint16_t v___y_4762_; lean_object* v___y_4763_; uint8_t v___y_4764_; lean_object* v___y_4787_; 
v___x_4677_ = lean_unsigned_to_nat(0u);
v___x_4678_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4679_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3);
v___x_4680_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4681_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4681_, 0, v___x_4678_);
lean_ctor_set(v___x_4681_, 1, v_meta_4673_);
lean_ctor_set(v___x_4681_, 2, v___x_4668_);
lean_ctor_set(v___x_4681_, 3, v___x_4679_);
lean_ctor_set(v___x_4681_, 4, v___x_4680_);
lean_inc_ref(v_ngen_4671_);
v___x_4682_ = l_Lean_Meta_LazyDiscrTree_Cache_empty(v_ngen_4671_);
v___x_4683_ = lean_st_ref_swap(v_cacheRef_4660_, v___x_4682_);
lean_dec(v___x_4683_);
v___x_4684_ = 2;
v___x_4685_ = 0;
v___x_4686_ = 2;
v___x_4687_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_4687_, 0, v___x_4667_);
lean_ctor_set_uint8(v___x_4687_, 1, v___x_4667_);
lean_ctor_set_uint8(v___x_4687_, 2, v___x_4667_);
lean_ctor_set_uint8(v___x_4687_, 3, v___x_4667_);
lean_ctor_set_uint8(v___x_4687_, 4, v___x_4667_);
lean_ctor_set_uint8(v___x_4687_, 5, v___x_4669_);
lean_ctor_set_uint8(v___x_4687_, 6, v___x_4669_);
lean_ctor_set_uint8(v___x_4687_, 7, v___x_4667_);
lean_ctor_set_uint8(v___x_4687_, 8, v___x_4669_);
lean_ctor_set_uint8(v___x_4687_, 9, v___x_4684_);
lean_ctor_set_uint8(v___x_4687_, 10, v___x_4685_);
lean_ctor_set_uint8(v___x_4687_, 11, v___x_4669_);
lean_ctor_set_uint8(v___x_4687_, 12, v___x_4669_);
lean_ctor_set_uint8(v___x_4687_, 13, v___x_4669_);
lean_ctor_set_uint8(v___x_4687_, 14, v___x_4686_);
lean_ctor_set_uint8(v___x_4687_, 15, v___x_4669_);
lean_ctor_set_uint8(v___x_4687_, 16, v___x_4669_);
lean_ctor_set_uint8(v___x_4687_, 17, v___x_4669_);
lean_ctor_set_uint8(v___x_4687_, 18, v___x_4669_);
lean_ctor_set_uint8(v___x_4687_, 19, v___x_4667_);
v___x_4688_ = l_Lean_Meta_Config_toConfigWithKey(v___x_4687_);
v___x_4689_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5);
v___x_4690_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6));
v___x_4691_ = lean_box(0);
v___x_4692_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4692_, 0, v___x_4688_);
lean_ctor_set(v___x_4692_, 1, v___x_4668_);
lean_ctor_set(v___x_4692_, 2, v___x_4689_);
lean_ctor_set(v___x_4692_, 3, v___x_4690_);
lean_ctor_set(v___x_4692_, 4, v___x_4691_);
lean_ctor_set(v___x_4692_, 5, v___x_4677_);
lean_ctor_set(v___x_4692_, 6, v___x_4691_);
lean_ctor_set_uint8(v___x_4692_, sizeof(void*)*7, v___x_4667_);
lean_ctor_set_uint8(v___x_4692_, sizeof(void*)*7 + 1, v___x_4667_);
lean_ctor_set_uint8(v___x_4692_, sizeof(void*)*7 + 2, v___x_4667_);
lean_ctor_set_uint8(v___x_4692_, sizeof(void*)*7 + 3, v___x_4669_);
v___x_4693_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__7, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__7_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__7);
v___x_4694_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__8));
v___x_4695_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__9, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__9_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__9);
v___x_4696_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10);
v___x_4697_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11);
v___x_4698_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12);
v___x_4699_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4699_, 0, v_env_4657_);
lean_ctor_set(v___x_4699_, 1, v___x_4693_);
lean_ctor_set(v___x_4699_, 2, v_ngen_4671_);
lean_ctor_set(v___x_4699_, 3, v___x_4694_);
lean_ctor_set(v___x_4699_, 4, v___x_4695_);
lean_ctor_set(v___x_4699_, 5, v_core_4672_);
lean_ctor_set(v___x_4699_, 6, v___x_4696_);
lean_ctor_set(v___x_4699_, 7, v___x_4697_);
lean_ctor_set(v___x_4699_, 8, v___x_4698_);
lean_ctor_set(v___x_4699_, 9, v___x_4690_);
v___x_4700_ = lean_st_mk_ref(v___x_4699_);
v___x_4744_ = l_Lean_inheritedTraceOptions;
v___x_4745_ = lean_st_ref_get(v___x_4744_);
v_toCold_4746_ = lean_ctor_get(v_cctx_4656_, 0);
lean_inc_ref(v_toCold_4746_);
v_currRecDepth_4747_ = lean_ctor_get(v_cctx_4656_, 1);
lean_inc(v_currRecDepth_4747_);
v_ref_4748_ = lean_ctor_get(v_cctx_4656_, 2);
lean_inc(v_ref_4748_);
v_suppressElabErrors_4749_ = lean_ctor_get_uint8(v_cctx_4656_, sizeof(void*)*3 + 2);
v_isRecordingDeps_4750_ = lean_ctor_get_uint8(v_cctx_4656_, sizeof(void*)*3 + 3);
lean_dec_ref(v_cctx_4656_);
v_fileName_4751_ = lean_ctor_get(v_toCold_4746_, 0);
lean_inc_ref(v_fileName_4751_);
v_fileMap_4752_ = lean_ctor_get(v_toCold_4746_, 1);
lean_inc_ref(v_fileMap_4752_);
v_options_4753_ = lean_ctor_get(v_toCold_4746_, 2);
lean_inc_ref(v_options_4753_);
v_currNamespace_4754_ = lean_ctor_get(v_toCold_4746_, 4);
lean_inc(v_currNamespace_4754_);
v_openDecls_4755_ = lean_ctor_get(v_toCold_4746_, 5);
lean_inc(v_openDecls_4755_);
v_initHeartbeats_4756_ = lean_ctor_get(v_toCold_4746_, 6);
lean_inc(v_initHeartbeats_4756_);
v_maxHeartbeats_4757_ = lean_ctor_get(v_toCold_4746_, 7);
lean_inc(v_maxHeartbeats_4757_);
v_quotContext_4758_ = lean_ctor_get(v_toCold_4746_, 8);
lean_inc(v_quotContext_4758_);
v_currMacroScope_4759_ = lean_ctor_get(v_toCold_4746_, 9);
lean_inc(v_currMacroScope_4759_);
v_cancelTk_x3f_4760_ = lean_ctor_get(v_toCold_4746_, 10);
lean_inc(v_cancelTk_x3f_4760_);
lean_dec_ref(v_toCold_4746_);
if (v_isRecordingDeps_4750_ == 0)
{
v___y_4787_ = v_options_4753_;
goto v___jp_4786_;
}
else
{
lean_object* v___x_4796_; 
v___x_4796_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_4753_);
v___y_4787_ = v___x_4796_;
goto v___jp_4786_;
}
v___jp_4701_:
{
lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; 
v___x_4718_ = l_Lean_maxRecDepth;
v___x_4719_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(v___y_4703_, v___x_4718_);
v___x_4720_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_4720_, 0, v_fileName_4704_);
lean_ctor_set(v___x_4720_, 1, v_fileMap_4705_);
lean_ctor_set(v___x_4720_, 2, v___y_4703_);
lean_ctor_set(v___x_4720_, 3, v___x_4719_);
lean_ctor_set(v___x_4720_, 4, v_currNamespace_4706_);
lean_ctor_set(v___x_4720_, 5, v_openDecls_4707_);
lean_ctor_set(v___x_4720_, 6, v_initHeartbeats_4708_);
lean_ctor_set(v___x_4720_, 7, v_maxHeartbeats_4709_);
lean_ctor_set(v___x_4720_, 8, v_quotContext_4710_);
lean_ctor_set(v___x_4720_, 9, v_currMacroScope_4711_);
lean_ctor_set(v___x_4720_, 10, v_cancelTk_x3f_4712_);
lean_ctor_set(v___x_4720_, 11, v_inheritedTraceOptions_4713_);
v___x_4721_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_4721_, 0, v___x_4720_);
lean_ctor_set(v___x_4721_, 1, v_currRecDepth_4714_);
lean_ctor_set(v___x_4721_, 2, v_ref_4715_);
lean_ctor_set_uint16(v___x_4721_, sizeof(void*)*3, v___y_4702_);
lean_ctor_set_uint8(v___x_4721_, sizeof(void*)*3 + 2, v_suppressElabErrors_4716_);
lean_ctor_set_uint8(v___x_4721_, sizeof(void*)*3 + 3, v_isRecordingDeps_4717_);
v___x_4722_ = lean_st_mk_ref(v___x_4681_);
lean_inc(v___x_4700_);
lean_inc(v___x_4722_);
lean_inc(v_name_4666_);
v___x_4723_ = lean_apply_7(v_act_4662_, v_name_4666_, v_c_4663_, v___x_4692_, v___x_4722_, v___x_4721_, v___x_4700_, lean_box(0));
if (lean_obj_tag(v___x_4723_) == 0)
{
lean_object* v_a_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v_ngen_4727_; lean_object* v_cache_4728_; lean_object* v_cache_4729_; lean_object* v___x_4731_; 
lean_dec(v_name_4666_);
lean_dec(v_modName_4658_);
v_a_4724_ = lean_ctor_get(v___x_4723_, 0);
lean_inc(v_a_4724_);
lean_dec_ref_known(v___x_4723_, 1);
v___x_4725_ = lean_st_ref_get(v___x_4722_);
lean_dec(v___x_4722_);
v___x_4726_ = lean_st_ref_get(v___x_4700_);
lean_dec(v___x_4700_);
v_ngen_4727_ = lean_ctor_get(v___x_4726_, 2);
lean_inc_ref(v_ngen_4727_);
v_cache_4728_ = lean_ctor_get(v___x_4726_, 5);
lean_inc_ref(v_cache_4728_);
lean_dec(v___x_4726_);
v_cache_4729_ = lean_ctor_get(v___x_4725_, 1);
lean_inc_ref(v_cache_4729_);
lean_dec(v___x_4725_);
if (v_isShared_4676_ == 0)
{
lean_ctor_set(v___x_4675_, 2, v_cache_4729_);
lean_ctor_set(v___x_4675_, 1, v_cache_4728_);
lean_ctor_set(v___x_4675_, 0, v_ngen_4727_);
v___x_4731_ = v___x_4675_;
goto v_reusejp_4730_;
}
else
{
lean_object* v_reuseFailAlloc_4738_; 
v_reuseFailAlloc_4738_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4738_, 0, v_ngen_4727_);
lean_ctor_set(v_reuseFailAlloc_4738_, 1, v_cache_4728_);
lean_ctor_set(v_reuseFailAlloc_4738_, 2, v_cache_4729_);
v___x_4731_ = v_reuseFailAlloc_4738_;
goto v_reusejp_4730_;
}
v_reusejp_4730_:
{
lean_object* v___x_4732_; lean_object* v___x_4733_; uint8_t v___x_4734_; 
v___x_4732_ = lean_st_ref_swap(v_cacheRef_4660_, v___x_4731_);
lean_dec(v___x_4732_);
v___x_4733_ = lean_array_get_size(v_a_4724_);
v___x_4734_ = lean_nat_dec_lt(v___x_4677_, v___x_4733_);
if (v___x_4734_ == 0)
{
lean_dec(v_a_4724_);
return v_tree_4661_;
}
else
{
size_t v___x_4735_; size_t v___x_4736_; lean_object* v___x_4737_; 
v___x_4735_ = ((size_t)0ULL);
v___x_4736_ = lean_usize_of_nat(v___x_4733_);
v___x_4737_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1___redArg(v_a_4724_, v___x_4735_, v___x_4736_, v_tree_4661_);
lean_dec(v_a_4724_);
return v___x_4737_;
}
}
}
else
{
lean_object* v_a_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v___x_4743_; 
lean_dec(v___x_4722_);
lean_dec(v___x_4700_);
lean_del_object(v___x_4675_);
v_a_4739_ = lean_ctor_get(v___x_4723_, 0);
lean_inc(v_a_4739_);
lean_dec_ref_known(v___x_4723_, 1);
v___x_4740_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4740_, 0, v_modName_4658_);
lean_ctor_set(v___x_4740_, 1, v_name_4666_);
lean_ctor_set(v___x_4740_, 2, v_a_4739_);
v___x_4741_ = lean_st_ref_take(v_d_4659_);
v___x_4742_ = lean_array_push(v___x_4741_, v___x_4740_);
v___x_4743_ = lean_st_ref_put(v_d_4659_, v___x_4742_);
return v_tree_4661_;
}
}
v___jp_4761_:
{
lean_object* v___x_4765_; lean_object* v_env_4766_; lean_object* v_nextMacroScope_4767_; lean_object* v_ngen_4768_; lean_object* v_auxDeclNGen_4769_; lean_object* v_traceState_4770_; lean_object* v_recordedDeps_4771_; lean_object* v_messages_4772_; lean_object* v_infoState_4773_; lean_object* v_snapshotTasks_4774_; lean_object* v___x_4776_; uint8_t v_isShared_4777_; uint8_t v_isSharedCheck_4784_; 
v___x_4765_ = lean_st_ref_take(v___x_4700_);
v_env_4766_ = lean_ctor_get(v___x_4765_, 0);
v_nextMacroScope_4767_ = lean_ctor_get(v___x_4765_, 1);
v_ngen_4768_ = lean_ctor_get(v___x_4765_, 2);
v_auxDeclNGen_4769_ = lean_ctor_get(v___x_4765_, 3);
v_traceState_4770_ = lean_ctor_get(v___x_4765_, 4);
v_recordedDeps_4771_ = lean_ctor_get(v___x_4765_, 6);
v_messages_4772_ = lean_ctor_get(v___x_4765_, 7);
v_infoState_4773_ = lean_ctor_get(v___x_4765_, 8);
v_snapshotTasks_4774_ = lean_ctor_get(v___x_4765_, 9);
v_isSharedCheck_4784_ = !lean_is_exclusive(v___x_4765_);
if (v_isSharedCheck_4784_ == 0)
{
lean_object* v_unused_4785_; 
v_unused_4785_ = lean_ctor_get(v___x_4765_, 5);
lean_dec(v_unused_4785_);
v___x_4776_ = v___x_4765_;
v_isShared_4777_ = v_isSharedCheck_4784_;
goto v_resetjp_4775_;
}
else
{
lean_inc(v_snapshotTasks_4774_);
lean_inc(v_infoState_4773_);
lean_inc(v_messages_4772_);
lean_inc(v_recordedDeps_4771_);
lean_inc(v_traceState_4770_);
lean_inc(v_auxDeclNGen_4769_);
lean_inc(v_ngen_4768_);
lean_inc(v_nextMacroScope_4767_);
lean_inc(v_env_4766_);
lean_dec(v___x_4765_);
v___x_4776_ = lean_box(0);
v_isShared_4777_ = v_isSharedCheck_4784_;
goto v_resetjp_4775_;
}
v_resetjp_4775_:
{
lean_object* v___x_4778_; lean_object* v___x_4779_; lean_object* v___x_4781_; 
v___x_4778_ = l_Lean_Kernel_enableDiag(v_env_4766_, v___y_4764_);
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
v_reuseFailAlloc_4783_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4783_, 0, v___x_4778_);
lean_ctor_set(v_reuseFailAlloc_4783_, 1, v_nextMacroScope_4767_);
lean_ctor_set(v_reuseFailAlloc_4783_, 2, v_ngen_4768_);
lean_ctor_set(v_reuseFailAlloc_4783_, 3, v_auxDeclNGen_4769_);
lean_ctor_set(v_reuseFailAlloc_4783_, 4, v_traceState_4770_);
lean_ctor_set(v_reuseFailAlloc_4783_, 5, v___x_4779_);
lean_ctor_set(v_reuseFailAlloc_4783_, 6, v_recordedDeps_4771_);
lean_ctor_set(v_reuseFailAlloc_4783_, 7, v_messages_4772_);
lean_ctor_set(v_reuseFailAlloc_4783_, 8, v_infoState_4773_);
lean_ctor_set(v_reuseFailAlloc_4783_, 9, v_snapshotTasks_4774_);
v___x_4781_ = v_reuseFailAlloc_4783_;
goto v_reusejp_4780_;
}
v_reusejp_4780_:
{
lean_object* v___x_4782_; 
v___x_4782_ = lean_st_ref_put(v___x_4700_, v___x_4781_);
v___y_4702_ = v___y_4762_;
v___y_4703_ = v___y_4763_;
v_fileName_4704_ = v_fileName_4751_;
v_fileMap_4705_ = v_fileMap_4752_;
v_currNamespace_4706_ = v_currNamespace_4754_;
v_openDecls_4707_ = v_openDecls_4755_;
v_initHeartbeats_4708_ = v_initHeartbeats_4756_;
v_maxHeartbeats_4709_ = v_maxHeartbeats_4757_;
v_quotContext_4710_ = v_quotContext_4758_;
v_currMacroScope_4711_ = v_currMacroScope_4759_;
v_cancelTk_x3f_4712_ = v_cancelTk_x3f_4760_;
v_inheritedTraceOptions_4713_ = v___x_4745_;
v_currRecDepth_4714_ = v_currRecDepth_4747_;
v_ref_4715_ = v_ref_4748_;
v_suppressElabErrors_4716_ = v_suppressElabErrors_4749_;
v_isRecordingDeps_4717_ = v_isRecordingDeps_4750_;
goto v___jp_4701_;
}
}
}
v___jp_4786_:
{
uint16_t v___x_4788_; lean_object* v___x_4789_; lean_object* v_env_4790_; uint8_t v___x_4791_; uint16_t v___x_4792_; uint16_t v___x_4793_; uint16_t v___x_4794_; uint8_t v___x_4795_; 
v___x_4788_ = l_Lean_OptionFlags_ofOptions(v___y_4787_);
v___x_4789_ = lean_st_ref_get(v___x_4700_);
v_env_4790_ = lean_ctor_get(v___x_4789_, 0);
lean_inc_ref(v_env_4790_);
lean_dec(v___x_4789_);
v___x_4791_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4790_);
lean_dec_ref(v_env_4790_);
v___x_4792_ = 512;
v___x_4793_ = lean_uint16_land(v___x_4788_, v___x_4792_);
v___x_4794_ = 0;
v___x_4795_ = lean_uint16_dec_eq(v___x_4793_, v___x_4794_);
if (v___x_4795_ == 0)
{
if (v___x_4791_ == 0)
{
v___y_4762_ = v___x_4788_;
v___y_4763_ = v___y_4787_;
v___y_4764_ = v___x_4669_;
goto v___jp_4761_;
}
else
{
v___y_4702_ = v___x_4788_;
v___y_4703_ = v___y_4787_;
v_fileName_4704_ = v_fileName_4751_;
v_fileMap_4705_ = v_fileMap_4752_;
v_currNamespace_4706_ = v_currNamespace_4754_;
v_openDecls_4707_ = v_openDecls_4755_;
v_initHeartbeats_4708_ = v_initHeartbeats_4756_;
v_maxHeartbeats_4709_ = v_maxHeartbeats_4757_;
v_quotContext_4710_ = v_quotContext_4758_;
v_currMacroScope_4711_ = v_currMacroScope_4759_;
v_cancelTk_x3f_4712_ = v_cancelTk_x3f_4760_;
v_inheritedTraceOptions_4713_ = v___x_4745_;
v_currRecDepth_4714_ = v_currRecDepth_4747_;
v_ref_4715_ = v_ref_4748_;
v_suppressElabErrors_4716_ = v_suppressElabErrors_4749_;
v_isRecordingDeps_4717_ = v_isRecordingDeps_4750_;
goto v___jp_4701_;
}
}
else
{
if (v___x_4791_ == 0)
{
v___y_4702_ = v___x_4788_;
v___y_4703_ = v___y_4787_;
v_fileName_4704_ = v_fileName_4751_;
v_fileMap_4705_ = v_fileMap_4752_;
v_currNamespace_4706_ = v_currNamespace_4754_;
v_openDecls_4707_ = v_openDecls_4755_;
v_initHeartbeats_4708_ = v_initHeartbeats_4756_;
v_maxHeartbeats_4709_ = v_maxHeartbeats_4757_;
v_quotContext_4710_ = v_quotContext_4758_;
v_currMacroScope_4711_ = v_currMacroScope_4759_;
v_cancelTk_x3f_4712_ = v_cancelTk_x3f_4760_;
v_inheritedTraceOptions_4713_ = v___x_4745_;
v_currRecDepth_4714_ = v_currRecDepth_4747_;
v_ref_4715_ = v_ref_4748_;
v_suppressElabErrors_4716_ = v_suppressElabErrors_4749_;
v_isRecordingDeps_4717_ = v_isRecordingDeps_4750_;
goto v___jp_4701_;
}
else
{
v___y_4762_ = v___x_4788_;
v___y_4763_ = v___y_4787_;
v___y_4764_ = v___x_4667_;
goto v___jp_4761_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___boxed(lean_object* v_cctx_4798_, lean_object* v_env_4799_, lean_object* v_modName_4800_, lean_object* v_d_4801_, lean_object* v_cacheRef_4802_, lean_object* v_tree_4803_, lean_object* v_act_4804_, lean_object* v_c_4805_, lean_object* v_a_4806_){
_start:
{
lean_object* v_res_4807_; 
v_res_4807_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_4798_, v_env_4799_, v_modName_4800_, v_d_4801_, v_cacheRef_4802_, v_tree_4803_, v_act_4804_, v_c_4805_);
lean_dec(v_cacheRef_4802_);
lean_dec(v_d_4801_);
return v_res_4807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData(lean_object* v_00_u03b1_4808_, lean_object* v_cctx_4809_, lean_object* v_env_4810_, lean_object* v_modName_4811_, lean_object* v_d_4812_, lean_object* v_cacheRef_4813_, lean_object* v_tree_4814_, lean_object* v_act_4815_, lean_object* v_c_4816_){
_start:
{
lean_object* v___x_4818_; 
v___x_4818_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_4809_, v_env_4810_, v_modName_4811_, v_d_4812_, v_cacheRef_4813_, v_tree_4814_, v_act_4815_, v_c_4816_);
return v___x_4818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___boxed(lean_object* v_00_u03b1_4819_, lean_object* v_cctx_4820_, lean_object* v_env_4821_, lean_object* v_modName_4822_, lean_object* v_d_4823_, lean_object* v_cacheRef_4824_, lean_object* v_tree_4825_, lean_object* v_act_4826_, lean_object* v_c_4827_, lean_object* v_a_4828_){
_start:
{
lean_object* v_res_4829_; 
v_res_4829_ = l_Lean_Meta_LazyDiscrTree_addConstImportData(v_00_u03b1_4819_, v_cctx_4820_, v_env_4821_, v_modName_4822_, v_d_4823_, v_cacheRef_4824_, v_tree_4825_, v_act_4826_, v_c_4827_);
lean_dec(v_cacheRef_4824_);
lean_dec(v_d_4823_);
return v_res_4829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1(lean_object* v_00_u03b1_4830_, lean_object* v_as_4831_, size_t v_i_4832_, size_t v_stop_4833_, lean_object* v_b_4834_){
_start:
{
lean_object* v___x_4835_; 
v___x_4835_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1___redArg(v_as_4831_, v_i_4832_, v_stop_4833_, v_b_4834_);
return v___x_4835_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1___boxed(lean_object* v_00_u03b1_4836_, lean_object* v_as_4837_, lean_object* v_i_4838_, lean_object* v_stop_4839_, lean_object* v_b_4840_){
_start:
{
size_t v_i_boxed_4841_; size_t v_stop_boxed_4842_; lean_object* v_res_4843_; 
v_i_boxed_4841_ = lean_unbox_usize(v_i_4838_);
lean_dec(v_i_4838_);
v_stop_boxed_4842_ = lean_unbox_usize(v_stop_4839_);
lean_dec(v_stop_4839_);
v_res_4843_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1(v_00_u03b1_4836_, v_as_4837_, v_i_boxed_4841_, v_stop_boxed_4842_, v_b_4840_);
lean_dec_ref(v_as_4837_);
return v_res_4843_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___redArg___closed__0(void){
_start:
{
lean_object* v___x_4844_; lean_object* v___x_4845_; lean_object* v___x_4846_; 
v___x_4844_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__0));
v___x_4845_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1);
v___x_4846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4846_, 0, v___x_4845_);
lean_ctor_set(v___x_4846_, 1, v___x_4844_);
return v___x_4846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___redArg(){
_start:
{
lean_object* v___x_4848_; 
v___x_4848_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___redArg___closed__0);
return v___x_4848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___redArg___boxed(lean_object* v___dummy_4849_){
_start:
{
lean_object* v_res_4850_; 
v_res_4850_ = l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___redArg();
return v_res_4850_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0(void){
_start:
{
lean_object* v___x_4851_; 
v___x_4851_ = l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___redArg();
return v___x_4851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults(lean_object* v_00_u03b1_4852_){
_start:
{
lean_object* v___x_4853_; 
v___x_4853_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0);
return v___x_4853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_append___redArg(lean_object* v_x_4854_, lean_object* v_y_4855_){
_start:
{
lean_object* v_tree_4856_; lean_object* v_errors_4857_; lean_object* v_tree_4858_; lean_object* v_errors_4859_; lean_object* v___x_4861_; uint8_t v_isShared_4862_; uint8_t v_isSharedCheck_4868_; 
v_tree_4856_ = lean_ctor_get(v_x_4854_, 0);
lean_inc_ref(v_tree_4856_);
v_errors_4857_ = lean_ctor_get(v_x_4854_, 1);
lean_inc_ref(v_errors_4857_);
lean_dec_ref(v_x_4854_);
v_tree_4858_ = lean_ctor_get(v_y_4855_, 0);
v_errors_4859_ = lean_ctor_get(v_y_4855_, 1);
v_isSharedCheck_4868_ = !lean_is_exclusive(v_y_4855_);
if (v_isSharedCheck_4868_ == 0)
{
v___x_4861_ = v_y_4855_;
v_isShared_4862_ = v_isSharedCheck_4868_;
goto v_resetjp_4860_;
}
else
{
lean_inc(v_errors_4859_);
lean_inc(v_tree_4858_);
lean_dec(v_y_4855_);
v___x_4861_ = lean_box(0);
v_isShared_4862_ = v_isSharedCheck_4868_;
goto v_resetjp_4860_;
}
v_resetjp_4860_:
{
lean_object* v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4866_; 
v___x_4863_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg(v_tree_4856_, v_tree_4858_);
v___x_4864_ = l_Array_append___redArg(v_errors_4857_, v_errors_4859_);
lean_dec_ref(v_errors_4859_);
if (v_isShared_4862_ == 0)
{
lean_ctor_set(v___x_4861_, 1, v___x_4864_);
lean_ctor_set(v___x_4861_, 0, v___x_4863_);
v___x_4866_ = v___x_4861_;
goto v_reusejp_4865_;
}
else
{
lean_object* v_reuseFailAlloc_4867_; 
v_reuseFailAlloc_4867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4867_, 0, v___x_4863_);
lean_ctor_set(v_reuseFailAlloc_4867_, 1, v___x_4864_);
v___x_4866_ = v_reuseFailAlloc_4867_;
goto v_reusejp_4865_;
}
v_reusejp_4865_:
{
return v___x_4866_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_append(lean_object* v_00_u03b1_4869_, lean_object* v_x_4870_, lean_object* v_y_4871_){
_start:
{
lean_object* v___x_4872_; 
v___x_4872_ = l_Lean_Meta_LazyDiscrTree_InitResults_append___redArg(v_x_4870_, v_y_4871_);
return v___x_4872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___redArg(){
_start:
{
lean_object* v___x_4875_; 
v___x_4875_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___redArg___closed__0));
return v___x_4875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___redArg___boxed(lean_object* v___dummy_4876_){
_start:
{
lean_object* v_res_4877_; 
v_res_4877_ = l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___redArg();
return v_res_4877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_instAppend(lean_object* v_00_u03b1_4878_){
_start:
{
lean_object* v___x_4879_; 
v___x_4879_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___redArg___closed__0));
return v___x_4879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat___redArg(lean_object* v_d_4880_, lean_object* v_tree_4881_){
_start:
{
lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; 
v___x_4883_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_ImportData_new___closed__0));
v___x_4884_ = lean_st_ref_swap(v_d_4880_, v___x_4883_);
v___x_4885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4885_, 0, v_tree_4881_);
lean_ctor_set(v___x_4885_, 1, v___x_4884_);
return v___x_4885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat___redArg___boxed(lean_object* v_d_4886_, lean_object* v_tree_4887_, lean_object* v_a_4888_){
_start:
{
lean_object* v_res_4889_; 
v_res_4889_ = l_Lean_Meta_LazyDiscrTree_toFlat___redArg(v_d_4886_, v_tree_4887_);
lean_dec(v_d_4886_);
return v_res_4889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat(lean_object* v_00_u03b1_4890_, lean_object* v_d_4891_, lean_object* v_tree_4892_){
_start:
{
lean_object* v___x_4894_; 
v___x_4894_ = l_Lean_Meta_LazyDiscrTree_toFlat___redArg(v_d_4891_, v_tree_4892_);
return v___x_4894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat___boxed(lean_object* v_00_u03b1_4895_, lean_object* v_d_4896_, lean_object* v_tree_4897_, lean_object* v_a_4898_){
_start:
{
lean_object* v_res_4899_; 
v_res_4899_ = l_Lean_Meta_LazyDiscrTree_toFlat(v_00_u03b1_4895_, v_d_4896_, v_tree_4897_);
lean_dec(v_d_4896_);
return v_res_4899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(lean_object* v_cctx_4900_, lean_object* v_env_4901_, lean_object* v_act_4902_, lean_object* v_d_4903_, lean_object* v_cacheRef_4904_, lean_object* v_tree_4905_, lean_object* v_mname_4906_, lean_object* v_mdata_4907_, lean_object* v_i_4908_){
_start:
{
lean_object* v_constants_4910_; lean_object* v___x_4911_; uint8_t v___x_4912_; 
v_constants_4910_ = lean_ctor_get(v_mdata_4907_, 2);
v___x_4911_ = lean_array_get_size(v_constants_4910_);
v___x_4912_ = lean_nat_dec_lt(v_i_4908_, v___x_4911_);
if (v___x_4912_ == 0)
{
lean_dec(v_i_4908_);
lean_dec(v_mname_4906_);
lean_dec_ref(v_act_4902_);
lean_dec_ref(v_env_4901_);
lean_dec_ref(v_cctx_4900_);
return v_tree_4905_;
}
else
{
lean_object* v___x_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; 
v___x_4913_ = lean_array_fget_borrowed(v_constants_4910_, v_i_4908_);
lean_inc(v___x_4913_);
v___x_4914_ = l_Lean_AsyncConstantInfo_ofConstantInfo(v___x_4913_);
lean_inc_ref(v_act_4902_);
lean_inc(v_mname_4906_);
lean_inc_ref(v_env_4901_);
lean_inc_ref(v_cctx_4900_);
v___x_4915_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_4900_, v_env_4901_, v_mname_4906_, v_d_4903_, v_cacheRef_4904_, v_tree_4905_, v_act_4902_, v___x_4914_);
v___x_4916_ = lean_unsigned_to_nat(1u);
v___x_4917_ = lean_nat_add(v_i_4908_, v___x_4916_);
lean_dec(v_i_4908_);
v_tree_4905_ = v___x_4915_;
v_i_4908_ = v___x_4917_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg___boxed(lean_object* v_cctx_4919_, lean_object* v_env_4920_, lean_object* v_act_4921_, lean_object* v_d_4922_, lean_object* v_cacheRef_4923_, lean_object* v_tree_4924_, lean_object* v_mname_4925_, lean_object* v_mdata_4926_, lean_object* v_i_4927_, lean_object* v_a_4928_){
_start:
{
lean_object* v_res_4929_; 
v_res_4929_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(v_cctx_4919_, v_env_4920_, v_act_4921_, v_d_4922_, v_cacheRef_4923_, v_tree_4924_, v_mname_4925_, v_mdata_4926_, v_i_4927_);
lean_dec_ref(v_mdata_4926_);
lean_dec(v_cacheRef_4923_);
lean_dec(v_d_4922_);
return v_res_4929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule(lean_object* v_00_u03b1_4930_, lean_object* v_cctx_4931_, lean_object* v_env_4932_, lean_object* v_act_4933_, lean_object* v_d_4934_, lean_object* v_cacheRef_4935_, lean_object* v_tree_4936_, lean_object* v_mname_4937_, lean_object* v_mdata_4938_, lean_object* v_i_4939_){
_start:
{
lean_object* v___x_4941_; 
v___x_4941_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(v_cctx_4931_, v_env_4932_, v_act_4933_, v_d_4934_, v_cacheRef_4935_, v_tree_4936_, v_mname_4937_, v_mdata_4938_, v_i_4939_);
return v___x_4941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule___boxed(lean_object* v_00_u03b1_4942_, lean_object* v_cctx_4943_, lean_object* v_env_4944_, lean_object* v_act_4945_, lean_object* v_d_4946_, lean_object* v_cacheRef_4947_, lean_object* v_tree_4948_, lean_object* v_mname_4949_, lean_object* v_mdata_4950_, lean_object* v_i_4951_, lean_object* v_a_4952_){
_start:
{
lean_object* v_res_4953_; 
v_res_4953_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule(v_00_u03b1_4942_, v_cctx_4943_, v_env_4944_, v_act_4945_, v_d_4946_, v_cacheRef_4947_, v_tree_4948_, v_mname_4949_, v_mdata_4950_, v_i_4951_);
lean_dec_ref(v_mdata_4950_);
lean_dec(v_cacheRef_4947_);
lean_dec(v_d_4946_);
return v_res_4953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg(lean_object* v_cctx_4954_, lean_object* v_env_4955_, lean_object* v_act_4956_, lean_object* v_d_4957_, lean_object* v_cacheRef_4958_, lean_object* v_tree_4959_, lean_object* v_start_4960_, lean_object* v_stop_4961_){
_start:
{
uint8_t v___x_4963_; 
v___x_4963_ = lean_nat_dec_lt(v_start_4960_, v_stop_4961_);
if (v___x_4963_ == 0)
{
lean_object* v___x_4964_; 
lean_dec(v_start_4960_);
lean_dec_ref(v_act_4956_);
lean_dec_ref(v_env_4955_);
lean_dec_ref(v_cctx_4954_);
v___x_4964_ = l_Lean_Meta_LazyDiscrTree_toFlat___redArg(v_d_4957_, v_tree_4959_);
return v___x_4964_;
}
else
{
lean_object* v___x_4965_; lean_object* v_moduleNames_4966_; lean_object* v_moduleData_4967_; lean_object* v___x_4968_; lean_object* v___x_4969_; lean_object* v_mname_4970_; lean_object* v_mdata_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; 
v___x_4965_ = l_Lean_Environment_header(v_env_4955_);
v_moduleNames_4966_ = lean_ctor_get(v___x_4965_, 4);
lean_inc_ref(v_moduleNames_4966_);
v_moduleData_4967_ = lean_ctor_get(v___x_4965_, 7);
lean_inc_ref(v_moduleData_4967_);
lean_dec_ref(v___x_4965_);
v___x_4968_ = lean_box(0);
v___x_4969_ = l_Lean_instInhabitedModuleData_default;
v_mname_4970_ = lean_array_get(v___x_4968_, v_moduleNames_4966_, v_start_4960_);
lean_dec_ref(v_moduleNames_4966_);
v_mdata_4971_ = lean_array_get(v___x_4969_, v_moduleData_4967_, v_start_4960_);
lean_dec_ref(v_moduleData_4967_);
v___x_4972_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_act_4956_);
lean_inc_ref(v_env_4955_);
lean_inc_ref(v_cctx_4954_);
v___x_4973_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(v_cctx_4954_, v_env_4955_, v_act_4956_, v_d_4957_, v_cacheRef_4958_, v_tree_4959_, v_mname_4970_, v_mdata_4971_, v___x_4972_);
lean_dec(v_mdata_4971_);
v___x_4974_ = lean_unsigned_to_nat(1u);
v___x_4975_ = lean_nat_add(v_start_4960_, v___x_4974_);
lean_dec(v_start_4960_);
v_tree_4959_ = v___x_4973_;
v_start_4960_ = v___x_4975_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg___boxed(lean_object* v_cctx_4977_, lean_object* v_env_4978_, lean_object* v_act_4979_, lean_object* v_d_4980_, lean_object* v_cacheRef_4981_, lean_object* v_tree_4982_, lean_object* v_start_4983_, lean_object* v_stop_4984_, lean_object* v_a_4985_){
_start:
{
lean_object* v_res_4986_; 
v_res_4986_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg(v_cctx_4977_, v_env_4978_, v_act_4979_, v_d_4980_, v_cacheRef_4981_, v_tree_4982_, v_start_4983_, v_stop_4984_);
lean_dec(v_stop_4984_);
lean_dec(v_cacheRef_4981_);
lean_dec(v_d_4980_);
return v_res_4986_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go(lean_object* v_00_u03b1_4987_, lean_object* v_cctx_4988_, lean_object* v_env_4989_, lean_object* v_act_4990_, lean_object* v_d_4991_, lean_object* v_cacheRef_4992_, lean_object* v_tree_4993_, lean_object* v_start_4994_, lean_object* v_stop_4995_){
_start:
{
lean_object* v___x_4997_; 
v___x_4997_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg(v_cctx_4988_, v_env_4989_, v_act_4990_, v_d_4991_, v_cacheRef_4992_, v_tree_4993_, v_start_4994_, v_stop_4995_);
return v___x_4997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___boxed(lean_object* v_00_u03b1_4998_, lean_object* v_cctx_4999_, lean_object* v_env_5000_, lean_object* v_act_5001_, lean_object* v_d_5002_, lean_object* v_cacheRef_5003_, lean_object* v_tree_5004_, lean_object* v_start_5005_, lean_object* v_stop_5006_, lean_object* v_a_5007_){
_start:
{
lean_object* v_res_5008_; 
v_res_5008_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go(v_00_u03b1_4998_, v_cctx_4999_, v_env_5000_, v_act_5001_, v_d_5002_, v_cacheRef_5003_, v_tree_5004_, v_start_5005_, v_stop_5006_);
lean_dec(v_stop_5006_);
lean_dec(v_cacheRef_5003_);
lean_dec(v_d_5002_);
return v_res_5008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___redArg(lean_object* v_cctx_5009_, lean_object* v_ngen_5010_, lean_object* v_env_5011_, lean_object* v_act_5012_, lean_object* v_start_5013_, lean_object* v_stop_5014_){
_start:
{
lean_object* v___x_5016_; lean_object* v___x_5017_; lean_object* v___x_5018_; lean_object* v___x_5019_; lean_object* v___x_5020_; 
v___x_5016_ = l_Lean_Meta_LazyDiscrTree_Cache_empty(v_ngen_5010_);
v___x_5017_ = lean_st_mk_ref(v___x_5016_);
v___x_5018_ = l_Lean_Meta_LazyDiscrTree_ImportData_new();
v___x_5019_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1);
v___x_5020_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg(v_cctx_5009_, v_env_5011_, v_act_5012_, v___x_5018_, v___x_5017_, v___x_5019_, v_start_5013_, v_stop_5014_);
lean_dec(v___x_5017_);
lean_dec(v___x_5018_);
return v___x_5020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___redArg___boxed(lean_object* v_cctx_5021_, lean_object* v_ngen_5022_, lean_object* v_env_5023_, lean_object* v_act_5024_, lean_object* v_start_5025_, lean_object* v_stop_5026_, lean_object* v_a_5027_){
_start:
{
lean_object* v_res_5028_; 
v_res_5028_ = l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___redArg(v_cctx_5021_, v_ngen_5022_, v_env_5023_, v_act_5024_, v_start_5025_, v_stop_5026_);
lean_dec(v_stop_5026_);
return v_res_5028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq(lean_object* v_00_u03b1_5029_, lean_object* v_cctx_5030_, lean_object* v_ngen_5031_, lean_object* v_env_5032_, lean_object* v_act_5033_, lean_object* v_start_5034_, lean_object* v_stop_5035_){
_start:
{
lean_object* v___x_5037_; 
v___x_5037_ = l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___redArg(v_cctx_5030_, v_ngen_5031_, v_env_5032_, v_act_5033_, v_start_5034_, v_stop_5035_);
return v___x_5037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed(lean_object* v_00_u03b1_5038_, lean_object* v_cctx_5039_, lean_object* v_ngen_5040_, lean_object* v_env_5041_, lean_object* v_act_5042_, lean_object* v_start_5043_, lean_object* v_stop_5044_, lean_object* v_a_5045_){
_start:
{
lean_object* v_res_5046_; 
v_res_5046_ = l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq(v_00_u03b1_5038_, v_cctx_5039_, v_ngen_5040_, v_env_5041_, v_act_5042_, v_start_5043_, v_stop_5044_);
lean_dec(v_stop_5044_);
return v_res_5046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___redArg___lam__0(lean_object* v_inst_5047_, lean_object* v_x1_5048_, lean_object* v_x2_5049_){
_start:
{
lean_object* v___x_5050_; lean_object* v___x_5051_; 
v___x_5050_ = lean_task_get_own(v_x2_5049_);
v___x_5051_ = lean_apply_2(v_inst_5047_, v_x1_5048_, v___x_5050_);
return v___x_5051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___redArg(lean_object* v_inst_5052_, lean_object* v_z_5053_, lean_object* v_tasks_5054_){
_start:
{
lean_object* v___x_5055_; lean_object* v___x_5056_; lean_object* v___x_5057_; uint8_t v___x_5058_; 
v___x_5055_ = lean_unsigned_to_nat(0u);
v___x_5056_ = lean_array_get_size(v_tasks_5054_);
v___x_5057_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__9));
v___x_5058_ = lean_nat_dec_lt(v___x_5055_, v___x_5056_);
if (v___x_5058_ == 0)
{
lean_dec_ref(v_tasks_5054_);
lean_dec(v_inst_5052_);
return v_z_5053_;
}
else
{
lean_object* v___f_5059_; size_t v___x_5060_; size_t v___x_5061_; lean_object* v___x_5062_; 
v___f_5059_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_combineGet___redArg___lam__0), 3, 1);
lean_closure_set(v___f_5059_, 0, v_inst_5052_);
v___x_5060_ = ((size_t)0ULL);
v___x_5061_ = lean_usize_of_nat(v___x_5056_);
v___x_5062_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_5057_, v___f_5059_, v_tasks_5054_, v___x_5060_, v___x_5061_, v_z_5053_);
return v___x_5062_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet(lean_object* v_00_u03b1_5063_, lean_object* v_inst_5064_, lean_object* v_z_5065_, lean_object* v_tasks_5066_){
_start:
{
lean_object* v___x_5067_; 
v___x_5067_ = l_Lean_Meta_LazyDiscrTree_combineGet___redArg(v_inst_5064_, v_z_5065_, v_tasks_5066_);
return v___x_5067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg___lam__0(lean_object* v_toPure_5068_, lean_object* v___x_5069_, lean_object* v_____r_5070_){
_start:
{
lean_object* v___x_5071_; 
v___x_5071_ = lean_apply_2(v_toPure_5068_, lean_box(0), v___x_5069_);
return v___x_5071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg___lam__1(lean_object* v_toPure_5072_, lean_object* v_setNGen_5073_, lean_object* v_toBind_5074_, lean_object* v_ngen_5075_){
_start:
{
lean_object* v_namePrefix_5076_; lean_object* v_idx_5077_; lean_object* v___x_5079_; uint8_t v_isShared_5080_; uint8_t v_isSharedCheck_5091_; 
v_namePrefix_5076_ = lean_ctor_get(v_ngen_5075_, 0);
v_idx_5077_ = lean_ctor_get(v_ngen_5075_, 1);
v_isSharedCheck_5091_ = !lean_is_exclusive(v_ngen_5075_);
if (v_isSharedCheck_5091_ == 0)
{
v___x_5079_ = v_ngen_5075_;
v_isShared_5080_ = v_isSharedCheck_5091_;
goto v_resetjp_5078_;
}
else
{
lean_inc(v_idx_5077_);
lean_inc(v_namePrefix_5076_);
lean_dec(v_ngen_5075_);
v___x_5079_ = lean_box(0);
v_isShared_5080_ = v_isSharedCheck_5091_;
goto v_resetjp_5078_;
}
v_resetjp_5078_:
{
lean_object* v___x_5081_; lean_object* v___x_5082_; lean_object* v___x_5084_; 
lean_inc(v_idx_5077_);
lean_inc(v_namePrefix_5076_);
v___x_5081_ = l_Lean_Name_num___override(v_namePrefix_5076_, v_idx_5077_);
v___x_5082_ = lean_unsigned_to_nat(1u);
if (v_isShared_5080_ == 0)
{
lean_ctor_set(v___x_5079_, 1, v___x_5082_);
lean_ctor_set(v___x_5079_, 0, v___x_5081_);
v___x_5084_ = v___x_5079_;
goto v_reusejp_5083_;
}
else
{
lean_object* v_reuseFailAlloc_5090_; 
v_reuseFailAlloc_5090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5090_, 0, v___x_5081_);
lean_ctor_set(v_reuseFailAlloc_5090_, 1, v___x_5082_);
v___x_5084_ = v_reuseFailAlloc_5090_;
goto v_reusejp_5083_;
}
v_reusejp_5083_:
{
lean_object* v___f_5085_; lean_object* v___x_5086_; lean_object* v___x_5087_; lean_object* v___x_5088_; lean_object* v___x_5089_; 
v___f_5085_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5085_, 0, v_toPure_5072_);
lean_closure_set(v___f_5085_, 1, v___x_5084_);
v___x_5086_ = lean_nat_add(v_idx_5077_, v___x_5082_);
lean_dec(v_idx_5077_);
v___x_5087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5087_, 0, v_namePrefix_5076_);
lean_ctor_set(v___x_5087_, 1, v___x_5086_);
v___x_5088_ = lean_apply_1(v_setNGen_5073_, v___x_5087_);
v___x_5089_ = lean_apply_4(v_toBind_5074_, lean_box(0), lean_box(0), v___x_5088_, v___f_5085_);
return v___x_5089_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg(lean_object* v_inst_5092_, lean_object* v_inst_5093_){
_start:
{
lean_object* v_toApplicative_5094_; lean_object* v_toBind_5095_; lean_object* v_getNGen_5096_; lean_object* v_setNGen_5097_; lean_object* v_toPure_5098_; lean_object* v___f_5099_; lean_object* v___x_5100_; 
v_toApplicative_5094_ = lean_ctor_get(v_inst_5092_, 0);
lean_inc_ref(v_toApplicative_5094_);
v_toBind_5095_ = lean_ctor_get(v_inst_5092_, 1);
lean_inc_n(v_toBind_5095_, 2);
lean_dec_ref(v_inst_5092_);
v_getNGen_5096_ = lean_ctor_get(v_inst_5093_, 0);
lean_inc(v_getNGen_5096_);
v_setNGen_5097_ = lean_ctor_get(v_inst_5093_, 1);
lean_inc(v_setNGen_5097_);
lean_dec_ref(v_inst_5093_);
v_toPure_5098_ = lean_ctor_get(v_toApplicative_5094_, 1);
lean_inc(v_toPure_5098_);
lean_dec_ref(v_toApplicative_5094_);
v___f_5099_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg___lam__1), 4, 3);
lean_closure_set(v___f_5099_, 0, v_toPure_5098_);
lean_closure_set(v___f_5099_, 1, v_setNGen_5097_);
lean_closure_set(v___f_5099_, 2, v_toBind_5095_);
v___x_5100_ = lean_apply_4(v_toBind_5095_, lean_box(0), lean_box(0), v_getNGen_5096_, v___f_5099_);
return v___x_5100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen(lean_object* v_M_5101_, lean_object* v_inst_5102_, lean_object* v_inst_5103_){
_start:
{
lean_object* v___x_5104_; 
v___x_5104_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg(v_inst_5102_, v_inst_5103_);
return v___x_5104_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg(lean_object* v_cctx_5105_, lean_object* v_env_5106_, lean_object* v_modName_5107_, lean_object* v_d_5108_, lean_object* v_val_5109_, lean_object* v_act_5110_, lean_object* v_as_5111_, size_t v_sz_5112_, size_t v_i_5113_, lean_object* v_b_5114_){
_start:
{
uint8_t v___x_5116_; 
v___x_5116_ = lean_usize_dec_lt(v_i_5113_, v_sz_5112_);
if (v___x_5116_ == 0)
{
lean_dec_ref(v_act_5110_);
lean_dec(v_modName_5107_);
lean_dec_ref(v_env_5106_);
lean_dec_ref(v_cctx_5105_);
return v_b_5114_;
}
else
{
lean_object* v_a_5117_; lean_object* v___x_5118_; size_t v___x_5119_; size_t v___x_5120_; 
v_a_5117_ = lean_array_uget_borrowed(v_as_5111_, v_i_5113_);
lean_inc(v_a_5117_);
lean_inc_ref(v_act_5110_);
lean_inc(v_modName_5107_);
lean_inc_ref(v_env_5106_);
lean_inc_ref(v_cctx_5105_);
v___x_5118_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_5105_, v_env_5106_, v_modName_5107_, v_d_5108_, v_val_5109_, v_b_5114_, v_act_5110_, v_a_5117_);
v___x_5119_ = ((size_t)1ULL);
v___x_5120_ = lean_usize_add(v_i_5113_, v___x_5119_);
v_i_5113_ = v___x_5120_;
v_b_5114_ = v___x_5118_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg___boxed(lean_object* v_cctx_5122_, lean_object* v_env_5123_, lean_object* v_modName_5124_, lean_object* v_d_5125_, lean_object* v_val_5126_, lean_object* v_act_5127_, lean_object* v_as_5128_, lean_object* v_sz_5129_, lean_object* v_i_5130_, lean_object* v_b_5131_, lean_object* v___y_5132_){
_start:
{
size_t v_sz_boxed_5133_; size_t v_i_boxed_5134_; lean_object* v_res_5135_; 
v_sz_boxed_5133_ = lean_unbox_usize(v_sz_5129_);
lean_dec(v_sz_5129_);
v_i_boxed_5134_ = lean_unbox_usize(v_i_5130_);
lean_dec(v_i_5130_);
v_res_5135_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg(v_cctx_5122_, v_env_5123_, v_modName_5124_, v_d_5125_, v_val_5126_, v_act_5127_, v_as_5128_, v_sz_boxed_5133_, v_i_boxed_5134_, v_b_5131_);
lean_dec_ref(v_as_5128_);
lean_dec(v_val_5126_);
lean_dec(v_d_5125_);
return v_res_5135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(lean_object* v_cctx_5136_, lean_object* v_ngen_5137_, lean_object* v_env_5138_, lean_object* v_d_5139_, lean_object* v_act_5140_){
_start:
{
lean_object* v___x_5142_; lean_object* v_mainModule_5143_; lean_object* v___x_5144_; lean_object* v___x_5145_; lean_object* v___x_5146_; uint8_t v___x_5147_; lean_object* v___x_5148_; size_t v_sz_5149_; size_t v___x_5150_; lean_object* v___x_5151_; 
v___x_5142_ = l_Lean_Environment_header(v_env_5138_);
v_mainModule_5143_ = lean_ctor_get(v___x_5142_, 0);
lean_inc(v_mainModule_5143_);
lean_dec_ref(v___x_5142_);
v___x_5144_ = l_Lean_Meta_LazyDiscrTree_Cache_empty(v_ngen_5137_);
v___x_5145_ = lean_st_mk_ref(v___x_5144_);
v___x_5146_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___redArg___closed__1);
v___x_5147_ = 1;
v___x_5148_ = l_Lean_Environment_getLocalConstantInfos(v_env_5138_, v___x_5147_);
v_sz_5149_ = lean_array_size(v___x_5148_);
v___x_5150_ = ((size_t)0ULL);
v___x_5151_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg(v_cctx_5136_, v_env_5138_, v_mainModule_5143_, v_d_5139_, v___x_5145_, v_act_5140_, v___x_5148_, v_sz_5149_, v___x_5150_, v___x_5146_);
lean_dec_ref(v___x_5148_);
lean_dec(v___x_5145_);
return v___x_5151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg___boxed(lean_object* v_cctx_5152_, lean_object* v_ngen_5153_, lean_object* v_env_5154_, lean_object* v_d_5155_, lean_object* v_act_5156_, lean_object* v_a_5157_){
_start:
{
lean_object* v_res_5158_; 
v_res_5158_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(v_cctx_5152_, v_ngen_5153_, v_env_5154_, v_d_5155_, v_act_5156_);
lean_dec(v_d_5155_);
return v_res_5158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree(lean_object* v_00_u03b1_5159_, lean_object* v_cctx_5160_, lean_object* v_ngen_5161_, lean_object* v_env_5162_, lean_object* v_d_5163_, lean_object* v_act_5164_){
_start:
{
lean_object* v___x_5166_; 
v___x_5166_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(v_cctx_5160_, v_ngen_5161_, v_env_5162_, v_d_5163_, v_act_5164_);
return v___x_5166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___boxed(lean_object* v_00_u03b1_5167_, lean_object* v_cctx_5168_, lean_object* v_ngen_5169_, lean_object* v_env_5170_, lean_object* v_d_5171_, lean_object* v_act_5172_, lean_object* v_a_5173_){
_start:
{
lean_object* v_res_5174_; 
v_res_5174_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree(v_00_u03b1_5167_, v_cctx_5168_, v_ngen_5169_, v_env_5170_, v_d_5171_, v_act_5172_);
lean_dec(v_d_5171_);
return v_res_5174_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0(lean_object* v_00_u03b1_5175_, lean_object* v_cctx_5176_, lean_object* v_env_5177_, lean_object* v_modName_5178_, lean_object* v_d_5179_, lean_object* v_val_5180_, lean_object* v_act_5181_, lean_object* v_as_5182_, size_t v_sz_5183_, size_t v_i_5184_, lean_object* v_b_5185_){
_start:
{
lean_object* v___x_5187_; 
v___x_5187_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg(v_cctx_5176_, v_env_5177_, v_modName_5178_, v_d_5179_, v_val_5180_, v_act_5181_, v_as_5182_, v_sz_5183_, v_i_5184_, v_b_5185_);
return v___x_5187_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___boxed(lean_object* v_00_u03b1_5188_, lean_object* v_cctx_5189_, lean_object* v_env_5190_, lean_object* v_modName_5191_, lean_object* v_d_5192_, lean_object* v_val_5193_, lean_object* v_act_5194_, lean_object* v_as_5195_, lean_object* v_sz_5196_, lean_object* v_i_5197_, lean_object* v_b_5198_, lean_object* v___y_5199_){
_start:
{
size_t v_sz_boxed_5200_; size_t v_i_boxed_5201_; lean_object* v_res_5202_; 
v_sz_boxed_5200_ = lean_unbox_usize(v_sz_5196_);
lean_dec(v_sz_5196_);
v_i_boxed_5201_ = lean_unbox_usize(v_i_5197_);
lean_dec(v_i_5197_);
v_res_5202_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0(v_00_u03b1_5188_, v_cctx_5189_, v_env_5190_, v_modName_5191_, v_d_5192_, v_val_5193_, v_act_5194_, v_as_5195_, v_sz_boxed_5200_, v_i_boxed_5201_, v_b_5198_);
lean_dec_ref(v_as_5195_);
lean_dec(v_val_5193_);
lean_dec(v_d_5192_);
return v_res_5202_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(lean_object* v_x_5203_, lean_object* v_x_5204_, lean_object* v___y_5205_, lean_object* v___y_5206_, lean_object* v___y_5207_, lean_object* v___y_5208_){
_start:
{
if (lean_obj_tag(v_x_5204_) == 0)
{
lean_object* v___x_5210_; 
v___x_5210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5210_, 0, v_x_5203_);
return v___x_5210_;
}
else
{
lean_object* v_head_5211_; lean_object* v_tail_5212_; lean_object* v___x_5213_; 
v_head_5211_ = lean_ctor_get(v_x_5204_, 0);
lean_inc(v_head_5211_);
v_tail_5212_ = lean_ctor_get(v_x_5204_, 1);
lean_inc(v_tail_5212_);
lean_dec_ref_known(v_x_5204_, 2);
v___x_5213_ = l_Lean_Meta_LazyDiscrTree_dropKey___redArg(v_x_5203_, v_head_5211_, v___y_5205_, v___y_5206_, v___y_5207_, v___y_5208_);
if (lean_obj_tag(v___x_5213_) == 0)
{
lean_object* v_a_5214_; 
v_a_5214_ = lean_ctor_get(v___x_5213_, 0);
lean_inc(v_a_5214_);
lean_dec_ref_known(v___x_5213_, 1);
v_x_5203_ = v_a_5214_;
v_x_5204_ = v_tail_5212_;
goto _start;
}
else
{
lean_dec(v_tail_5212_);
return v___x_5213_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg___boxed(lean_object* v_x_5216_, lean_object* v_x_5217_, lean_object* v___y_5218_, lean_object* v___y_5219_, lean_object* v___y_5220_, lean_object* v___y_5221_, lean_object* v___y_5222_){
_start:
{
lean_object* v_res_5223_; 
v_res_5223_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_x_5216_, v_x_5217_, v___y_5218_, v___y_5219_, v___y_5220_, v___y_5221_);
lean_dec(v___y_5221_);
lean_dec_ref(v___y_5220_);
lean_dec(v___y_5219_);
lean_dec_ref(v___y_5218_);
return v_res_5223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys___redArg(lean_object* v_t_5224_, lean_object* v_keys_5225_, lean_object* v_a_5226_, lean_object* v_a_5227_, lean_object* v_a_5228_, lean_object* v_a_5229_){
_start:
{
lean_object* v___x_5231_; 
v___x_5231_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_t_5224_, v_keys_5225_, v_a_5226_, v_a_5227_, v_a_5228_, v_a_5229_);
return v___x_5231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys___redArg___boxed(lean_object* v_t_5232_, lean_object* v_keys_5233_, lean_object* v_a_5234_, lean_object* v_a_5235_, lean_object* v_a_5236_, lean_object* v_a_5237_, lean_object* v_a_5238_){
_start:
{
lean_object* v_res_5239_; 
v_res_5239_ = l_Lean_Meta_LazyDiscrTree_dropKeys___redArg(v_t_5232_, v_keys_5233_, v_a_5234_, v_a_5235_, v_a_5236_, v_a_5237_);
lean_dec(v_a_5237_);
lean_dec_ref(v_a_5236_);
lean_dec(v_a_5235_);
lean_dec_ref(v_a_5234_);
return v_res_5239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys(lean_object* v_00_u03b1_5240_, lean_object* v_t_5241_, lean_object* v_keys_5242_, lean_object* v_a_5243_, lean_object* v_a_5244_, lean_object* v_a_5245_, lean_object* v_a_5246_){
_start:
{
lean_object* v___x_5248_; 
v___x_5248_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_t_5241_, v_keys_5242_, v_a_5243_, v_a_5244_, v_a_5245_, v_a_5246_);
return v___x_5248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys___boxed(lean_object* v_00_u03b1_5249_, lean_object* v_t_5250_, lean_object* v_keys_5251_, lean_object* v_a_5252_, lean_object* v_a_5253_, lean_object* v_a_5254_, lean_object* v_a_5255_, lean_object* v_a_5256_){
_start:
{
lean_object* v_res_5257_; 
v_res_5257_ = l_Lean_Meta_LazyDiscrTree_dropKeys(v_00_u03b1_5249_, v_t_5250_, v_keys_5251_, v_a_5252_, v_a_5253_, v_a_5254_, v_a_5255_);
lean_dec(v_a_5255_);
lean_dec_ref(v_a_5254_);
lean_dec(v_a_5253_);
lean_dec_ref(v_a_5252_);
return v_res_5257_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0(lean_object* v_00_u03b1_5258_, lean_object* v_x_5259_, lean_object* v_x_5260_, lean_object* v___y_5261_, lean_object* v___y_5262_, lean_object* v___y_5263_, lean_object* v___y_5264_){
_start:
{
lean_object* v___x_5266_; 
v___x_5266_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_x_5259_, v_x_5260_, v___y_5261_, v___y_5262_, v___y_5263_, v___y_5264_);
return v___x_5266_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___boxed(lean_object* v_00_u03b1_5267_, lean_object* v_x_5268_, lean_object* v_x_5269_, lean_object* v___y_5270_, lean_object* v___y_5271_, lean_object* v___y_5272_, lean_object* v___y_5273_, lean_object* v___y_5274_){
_start:
{
lean_object* v_res_5275_; 
v_res_5275_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0(v_00_u03b1_5267_, v_x_5268_, v_x_5269_, v___y_5270_, v___y_5271_, v___y_5272_, v___y_5273_);
lean_dec(v___y_5273_);
lean_dec_ref(v___y_5272_);
lean_dec(v___y_5271_);
lean_dec_ref(v___y_5270_);
return v_res_5275_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(lean_object* v_as_5276_, size_t v_sz_5277_, size_t v_i_5278_, lean_object* v_b_5279_, lean_object* v___y_5280_, lean_object* v___y_5281_, lean_object* v___y_5282_, lean_object* v___y_5283_, lean_object* v___y_5284_){
_start:
{
uint8_t v___x_5286_; 
v___x_5286_ = lean_usize_dec_lt(v_i_5278_, v_sz_5277_);
if (v___x_5286_ == 0)
{
lean_object* v___x_5287_; 
v___x_5287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5287_, 0, v_b_5279_);
return v___x_5287_;
}
else
{
lean_object* v_a_5288_; lean_object* v___x_5289_; 
v_a_5288_ = lean_array_uget_borrowed(v_as_5276_, v_i_5278_);
v___x_5289_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(v_a_5288_, v_b_5279_, v___y_5280_, v___y_5281_, v___y_5282_, v___y_5283_, v___y_5284_);
if (lean_obj_tag(v___x_5289_) == 0)
{
lean_object* v_a_5290_; lean_object* v___x_5292_; uint8_t v_isShared_5293_; uint8_t v_isSharedCheck_5302_; 
v_a_5290_ = lean_ctor_get(v___x_5289_, 0);
v_isSharedCheck_5302_ = !lean_is_exclusive(v___x_5289_);
if (v_isSharedCheck_5302_ == 0)
{
v___x_5292_ = v___x_5289_;
v_isShared_5293_ = v_isSharedCheck_5302_;
goto v_resetjp_5291_;
}
else
{
lean_inc(v_a_5290_);
lean_dec(v___x_5289_);
v___x_5292_ = lean_box(0);
v_isShared_5293_ = v_isSharedCheck_5302_;
goto v_resetjp_5291_;
}
v_resetjp_5291_:
{
if (lean_obj_tag(v_a_5290_) == 0)
{
lean_object* v_a_5294_; lean_object* v___x_5296_; 
v_a_5294_ = lean_ctor_get(v_a_5290_, 0);
lean_inc(v_a_5294_);
lean_dec_ref_known(v_a_5290_, 1);
if (v_isShared_5293_ == 0)
{
lean_ctor_set(v___x_5292_, 0, v_a_5294_);
v___x_5296_ = v___x_5292_;
goto v_reusejp_5295_;
}
else
{
lean_object* v_reuseFailAlloc_5297_; 
v_reuseFailAlloc_5297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5297_, 0, v_a_5294_);
v___x_5296_ = v_reuseFailAlloc_5297_;
goto v_reusejp_5295_;
}
v_reusejp_5295_:
{
return v___x_5296_;
}
}
else
{
lean_object* v_a_5298_; size_t v___x_5299_; size_t v___x_5300_; 
lean_del_object(v___x_5292_);
v_a_5298_ = lean_ctor_get(v_a_5290_, 0);
lean_inc(v_a_5298_);
lean_dec_ref_known(v_a_5290_, 1);
v___x_5299_ = ((size_t)1ULL);
v___x_5300_ = lean_usize_add(v_i_5278_, v___x_5299_);
v_i_5278_ = v___x_5300_;
v_b_5279_ = v_a_5298_;
goto _start;
}
}
}
else
{
lean_object* v_a_5303_; lean_object* v___x_5305_; uint8_t v_isShared_5306_; uint8_t v_isSharedCheck_5310_; 
v_a_5303_ = lean_ctor_get(v___x_5289_, 0);
v_isSharedCheck_5310_ = !lean_is_exclusive(v___x_5289_);
if (v_isSharedCheck_5310_ == 0)
{
v___x_5305_ = v___x_5289_;
v_isShared_5306_ = v_isSharedCheck_5310_;
goto v_resetjp_5304_;
}
else
{
lean_inc(v_a_5303_);
lean_dec(v___x_5289_);
v___x_5305_ = lean_box(0);
v_isShared_5306_ = v_isSharedCheck_5310_;
goto v_resetjp_5304_;
}
v_resetjp_5304_:
{
lean_object* v___x_5308_; 
if (v_isShared_5306_ == 0)
{
v___x_5308_ = v___x_5305_;
goto v_reusejp_5307_;
}
else
{
lean_object* v_reuseFailAlloc_5309_; 
v_reuseFailAlloc_5309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5309_, 0, v_a_5303_);
v___x_5308_ = v_reuseFailAlloc_5309_;
goto v_reusejp_5307_;
}
v_reusejp_5307_:
{
return v___x_5308_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(lean_object* v_next_5311_, lean_object* v_a_5312_, lean_object* v_a_5313_, lean_object* v_a_5314_, lean_object* v_a_5315_, lean_object* v_a_5316_){
_start:
{
lean_object* v___x_5318_; uint8_t v___x_5319_; 
v___x_5318_ = lean_unsigned_to_nat(0u);
v___x_5319_ = lean_nat_dec_eq(v_next_5311_, v___x_5318_);
if (v___x_5319_ == 0)
{
lean_object* v___x_5320_; 
v___x_5320_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_next_5311_, v_a_5312_, v_a_5313_, v_a_5314_, v_a_5315_, v_a_5316_);
if (lean_obj_tag(v___x_5320_) == 0)
{
lean_object* v_a_5321_; lean_object* v_snd_5322_; lean_object* v_fst_5323_; lean_object* v_fst_5324_; lean_object* v_snd_5325_; lean_object* v___x_5326_; 
v_a_5321_ = lean_ctor_get(v___x_5320_, 0);
lean_inc(v_a_5321_);
lean_dec_ref_known(v___x_5320_, 1);
v_snd_5322_ = lean_ctor_get(v_a_5321_, 1);
lean_inc(v_snd_5322_);
v_fst_5323_ = lean_ctor_get(v_a_5321_, 0);
lean_inc(v_fst_5323_);
lean_dec(v_a_5321_);
v_fst_5324_ = lean_ctor_get(v_snd_5322_, 0);
lean_inc(v_fst_5324_);
v_snd_5325_ = lean_ctor_get(v_snd_5322_, 1);
lean_inc(v_snd_5325_);
lean_dec(v_snd_5322_);
v___x_5326_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_fst_5324_, v_a_5312_, v_a_5313_, v_a_5314_, v_a_5315_, v_a_5316_);
if (lean_obj_tag(v___x_5326_) == 0)
{
lean_object* v_a_5327_; lean_object* v_buckets_5328_; lean_object* v___x_5329_; size_t v_sz_5330_; size_t v___x_5331_; lean_object* v___x_5332_; 
v_a_5327_ = lean_ctor_get(v___x_5326_, 0);
lean_inc(v_a_5327_);
lean_dec_ref_known(v___x_5326_, 1);
v_buckets_5328_ = lean_ctor_get(v_snd_5325_, 1);
v___x_5329_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v_sz_5330_ = lean_array_size(v_buckets_5328_);
v___x_5331_ = ((size_t)0ULL);
v___x_5332_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(v_buckets_5328_, v_sz_5330_, v___x_5331_, v___x_5329_, v_a_5312_, v_a_5313_, v_a_5314_, v_a_5315_, v_a_5316_);
if (lean_obj_tag(v___x_5332_) == 0)
{
lean_object* v_a_5333_; lean_object* v___x_5335_; uint8_t v_isShared_5336_; uint8_t v_isSharedCheck_5346_; 
v_a_5333_ = lean_ctor_get(v___x_5332_, 0);
v_isSharedCheck_5346_ = !lean_is_exclusive(v___x_5332_);
if (v_isSharedCheck_5346_ == 0)
{
v___x_5335_ = v___x_5332_;
v_isShared_5336_ = v_isSharedCheck_5346_;
goto v_resetjp_5334_;
}
else
{
lean_inc(v_a_5333_);
lean_dec(v___x_5332_);
v___x_5335_ = lean_box(0);
v_isShared_5336_ = v_isSharedCheck_5346_;
goto v_resetjp_5334_;
}
v_resetjp_5334_:
{
lean_object* v___x_5337_; lean_object* v___x_5338_; lean_object* v___x_5339_; lean_object* v___x_5340_; lean_object* v___x_5341_; lean_object* v___x_5342_; lean_object* v___x_5344_; 
v___x_5337_ = lean_st_ref_take(v_a_5312_);
v___x_5338_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5338_, 0, v___x_5329_);
lean_ctor_set(v___x_5338_, 1, v_fst_5324_);
lean_ctor_set(v___x_5338_, 2, v_snd_5325_);
lean_ctor_set(v___x_5338_, 3, v___x_5329_);
v___x_5339_ = lean_array_set(v___x_5337_, v_next_5311_, v___x_5338_);
v___x_5340_ = lean_st_ref_put(v_a_5312_, v___x_5339_);
v___x_5341_ = l_Array_append___redArg(v_fst_5323_, v_a_5327_);
lean_dec(v_a_5327_);
v___x_5342_ = l_Array_append___redArg(v___x_5341_, v_a_5333_);
lean_dec(v_a_5333_);
if (v_isShared_5336_ == 0)
{
lean_ctor_set(v___x_5335_, 0, v___x_5342_);
v___x_5344_ = v___x_5335_;
goto v_reusejp_5343_;
}
else
{
lean_object* v_reuseFailAlloc_5345_; 
v_reuseFailAlloc_5345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5345_, 0, v___x_5342_);
v___x_5344_ = v_reuseFailAlloc_5345_;
goto v_reusejp_5343_;
}
v_reusejp_5343_:
{
return v___x_5344_;
}
}
}
else
{
lean_dec(v_a_5327_);
lean_dec(v_snd_5325_);
lean_dec(v_fst_5324_);
lean_dec(v_fst_5323_);
return v___x_5332_;
}
}
else
{
lean_dec(v_snd_5325_);
lean_dec(v_fst_5324_);
lean_dec(v_fst_5323_);
return v___x_5326_;
}
}
else
{
lean_object* v_a_5347_; lean_object* v___x_5349_; uint8_t v_isShared_5350_; uint8_t v_isSharedCheck_5354_; 
v_a_5347_ = lean_ctor_get(v___x_5320_, 0);
v_isSharedCheck_5354_ = !lean_is_exclusive(v___x_5320_);
if (v_isSharedCheck_5354_ == 0)
{
v___x_5349_ = v___x_5320_;
v_isShared_5350_ = v_isSharedCheck_5354_;
goto v_resetjp_5348_;
}
else
{
lean_inc(v_a_5347_);
lean_dec(v___x_5320_);
v___x_5349_ = lean_box(0);
v_isShared_5350_ = v_isSharedCheck_5354_;
goto v_resetjp_5348_;
}
v_resetjp_5348_:
{
lean_object* v___x_5352_; 
if (v_isShared_5350_ == 0)
{
v___x_5352_ = v___x_5349_;
goto v_reusejp_5351_;
}
else
{
lean_object* v_reuseFailAlloc_5353_; 
v_reuseFailAlloc_5353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5353_, 0, v_a_5347_);
v___x_5352_ = v_reuseFailAlloc_5353_;
goto v_reusejp_5351_;
}
v_reusejp_5351_:
{
return v___x_5352_;
}
}
}
}
else
{
lean_object* v___x_5355_; lean_object* v___x_5356_; 
v___x_5355_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___x_5356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5356_, 0, v___x_5355_);
return v___x_5356_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(lean_object* v_a_5357_, lean_object* v_a_5358_, lean_object* v___y_5359_, lean_object* v___y_5360_, lean_object* v___y_5361_, lean_object* v___y_5362_, lean_object* v___y_5363_){
_start:
{
if (lean_obj_tag(v_a_5357_) == 0)
{
lean_object* v___x_5365_; lean_object* v___x_5366_; 
v___x_5365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5365_, 0, v_a_5358_);
v___x_5366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5366_, 0, v___x_5365_);
return v___x_5366_;
}
else
{
lean_object* v_value_5367_; lean_object* v_tail_5368_; lean_object* v___x_5369_; 
v_value_5367_ = lean_ctor_get(v_a_5357_, 1);
v_tail_5368_ = lean_ctor_get(v_a_5357_, 2);
v___x_5369_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_value_5367_, v___y_5359_, v___y_5360_, v___y_5361_, v___y_5362_, v___y_5363_);
if (lean_obj_tag(v___x_5369_) == 0)
{
lean_object* v_a_5370_; lean_object* v___x_5371_; 
v_a_5370_ = lean_ctor_get(v___x_5369_, 0);
lean_inc(v_a_5370_);
lean_dec_ref_known(v___x_5369_, 1);
v___x_5371_ = l_Array_append___redArg(v_a_5358_, v_a_5370_);
lean_dec(v_a_5370_);
v_a_5357_ = v_tail_5368_;
v_a_5358_ = v___x_5371_;
goto _start;
}
else
{
lean_object* v_a_5373_; lean_object* v___x_5375_; uint8_t v_isShared_5376_; uint8_t v_isSharedCheck_5380_; 
lean_dec_ref(v_a_5358_);
v_a_5373_ = lean_ctor_get(v___x_5369_, 0);
v_isSharedCheck_5380_ = !lean_is_exclusive(v___x_5369_);
if (v_isSharedCheck_5380_ == 0)
{
v___x_5375_ = v___x_5369_;
v_isShared_5376_ = v_isSharedCheck_5380_;
goto v_resetjp_5374_;
}
else
{
lean_inc(v_a_5373_);
lean_dec(v___x_5369_);
v___x_5375_ = lean_box(0);
v_isShared_5376_ = v_isSharedCheck_5380_;
goto v_resetjp_5374_;
}
v_resetjp_5374_:
{
lean_object* v___x_5378_; 
if (v_isShared_5376_ == 0)
{
v___x_5378_ = v___x_5375_;
goto v_reusejp_5377_;
}
else
{
lean_object* v_reuseFailAlloc_5379_; 
v_reuseFailAlloc_5379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5379_, 0, v_a_5373_);
v___x_5378_ = v_reuseFailAlloc_5379_;
goto v_reusejp_5377_;
}
v_reusejp_5377_:
{
return v___x_5378_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg___boxed(lean_object* v_a_5381_, lean_object* v_a_5382_, lean_object* v___y_5383_, lean_object* v___y_5384_, lean_object* v___y_5385_, lean_object* v___y_5386_, lean_object* v___y_5387_, lean_object* v___y_5388_){
_start:
{
lean_object* v_res_5389_; 
v_res_5389_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(v_a_5381_, v_a_5382_, v___y_5383_, v___y_5384_, v___y_5385_, v___y_5386_, v___y_5387_);
lean_dec(v___y_5387_);
lean_dec_ref(v___y_5386_);
lean_dec(v___y_5385_);
lean_dec_ref(v___y_5384_);
lean_dec(v___y_5383_);
lean_dec(v_a_5381_);
return v_res_5389_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg___boxed(lean_object* v_as_5390_, lean_object* v_sz_5391_, lean_object* v_i_5392_, lean_object* v_b_5393_, lean_object* v___y_5394_, lean_object* v___y_5395_, lean_object* v___y_5396_, lean_object* v___y_5397_, lean_object* v___y_5398_, lean_object* v___y_5399_){
_start:
{
size_t v_sz_boxed_5400_; size_t v_i_boxed_5401_; lean_object* v_res_5402_; 
v_sz_boxed_5400_ = lean_unbox_usize(v_sz_5391_);
lean_dec(v_sz_5391_);
v_i_boxed_5401_ = lean_unbox_usize(v_i_5392_);
lean_dec(v_i_5392_);
v_res_5402_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(v_as_5390_, v_sz_boxed_5400_, v_i_boxed_5401_, v_b_5393_, v___y_5394_, v___y_5395_, v___y_5396_, v___y_5397_, v___y_5398_);
lean_dec(v___y_5398_);
lean_dec_ref(v___y_5397_);
lean_dec(v___y_5396_);
lean_dec_ref(v___y_5395_);
lean_dec(v___y_5394_);
lean_dec_ref(v_as_5390_);
return v_res_5402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg___boxed(lean_object* v_next_5403_, lean_object* v_a_5404_, lean_object* v_a_5405_, lean_object* v_a_5406_, lean_object* v_a_5407_, lean_object* v_a_5408_, lean_object* v_a_5409_){
_start:
{
lean_object* v_res_5410_; 
v_res_5410_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_next_5403_, v_a_5404_, v_a_5405_, v_a_5406_, v_a_5407_, v_a_5408_);
lean_dec(v_a_5408_);
lean_dec_ref(v_a_5407_);
lean_dec(v_a_5406_);
lean_dec_ref(v_a_5405_);
lean_dec(v_a_5404_);
lean_dec(v_next_5403_);
return v_res_5410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux(lean_object* v_00_u03b1_5411_, lean_object* v_next_5412_, lean_object* v_a_5413_, lean_object* v_a_5414_, lean_object* v_a_5415_, lean_object* v_a_5416_, lean_object* v_a_5417_){
_start:
{
lean_object* v___x_5419_; 
v___x_5419_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_next_5412_, v_a_5413_, v_a_5414_, v_a_5415_, v_a_5416_, v_a_5417_);
return v___x_5419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___boxed(lean_object* v_00_u03b1_5420_, lean_object* v_next_5421_, lean_object* v_a_5422_, lean_object* v_a_5423_, lean_object* v_a_5424_, lean_object* v_a_5425_, lean_object* v_a_5426_, lean_object* v_a_5427_){
_start:
{
lean_object* v_res_5428_; 
v_res_5428_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux(v_00_u03b1_5420_, v_next_5421_, v_a_5422_, v_a_5423_, v_a_5424_, v_a_5425_, v_a_5426_);
lean_dec(v_a_5426_);
lean_dec_ref(v_a_5425_);
lean_dec(v_a_5424_);
lean_dec_ref(v_a_5423_);
lean_dec(v_a_5422_);
lean_dec(v_next_5421_);
return v_res_5428_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0(lean_object* v_00_u03b1_5429_, lean_object* v_a_5430_, lean_object* v_a_5431_, lean_object* v___y_5432_, lean_object* v___y_5433_, lean_object* v___y_5434_, lean_object* v___y_5435_, lean_object* v___y_5436_){
_start:
{
lean_object* v___x_5438_; 
v___x_5438_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(v_a_5430_, v_a_5431_, v___y_5432_, v___y_5433_, v___y_5434_, v___y_5435_, v___y_5436_);
return v___x_5438_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___boxed(lean_object* v_00_u03b1_5439_, lean_object* v_a_5440_, lean_object* v_a_5441_, lean_object* v___y_5442_, lean_object* v___y_5443_, lean_object* v___y_5444_, lean_object* v___y_5445_, lean_object* v___y_5446_, lean_object* v___y_5447_){
_start:
{
lean_object* v_res_5448_; 
v_res_5448_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0(v_00_u03b1_5439_, v_a_5440_, v_a_5441_, v___y_5442_, v___y_5443_, v___y_5444_, v___y_5445_, v___y_5446_);
lean_dec(v___y_5446_);
lean_dec_ref(v___y_5445_);
lean_dec(v___y_5444_);
lean_dec_ref(v___y_5443_);
lean_dec(v___y_5442_);
lean_dec(v_a_5440_);
return v_res_5448_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1(lean_object* v_00_u03b1_5449_, lean_object* v_as_5450_, size_t v_sz_5451_, size_t v_i_5452_, lean_object* v_b_5453_, lean_object* v___y_5454_, lean_object* v___y_5455_, lean_object* v___y_5456_, lean_object* v___y_5457_, lean_object* v___y_5458_){
_start:
{
lean_object* v___x_5460_; 
v___x_5460_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(v_as_5450_, v_sz_5451_, v_i_5452_, v_b_5453_, v___y_5454_, v___y_5455_, v___y_5456_, v___y_5457_, v___y_5458_);
return v___x_5460_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___boxed(lean_object* v_00_u03b1_5461_, lean_object* v_as_5462_, lean_object* v_sz_5463_, lean_object* v_i_5464_, lean_object* v_b_5465_, lean_object* v___y_5466_, lean_object* v___y_5467_, lean_object* v___y_5468_, lean_object* v___y_5469_, lean_object* v___y_5470_, lean_object* v___y_5471_){
_start:
{
size_t v_sz_boxed_5472_; size_t v_i_boxed_5473_; lean_object* v_res_5474_; 
v_sz_boxed_5472_ = lean_unbox_usize(v_sz_5463_);
lean_dec(v_sz_5463_);
v_i_boxed_5473_ = lean_unbox_usize(v_i_5464_);
lean_dec(v_i_5464_);
v_res_5474_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1(v_00_u03b1_5461_, v_as_5462_, v_sz_boxed_5472_, v_i_boxed_5473_, v_b_5465_, v___y_5466_, v___y_5467_, v___y_5468_, v___y_5469_, v___y_5470_);
lean_dec(v___y_5470_);
lean_dec_ref(v___y_5469_);
lean_dec(v___y_5468_);
lean_dec_ref(v___y_5467_);
lean_dec(v___y_5466_);
lean_dec_ref(v_as_5462_);
return v_res_5474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg(lean_object* v_next_5475_, lean_object* v_rest_5476_, lean_object* v_a_5477_, lean_object* v_a_5478_, lean_object* v_a_5479_, lean_object* v_a_5480_, lean_object* v_a_5481_){
_start:
{
lean_object* v___x_5483_; uint8_t v___x_5484_; 
v___x_5483_ = lean_unsigned_to_nat(0u);
v___x_5484_ = lean_nat_dec_eq(v_next_5475_, v___x_5483_);
if (v___x_5484_ == 0)
{
lean_object* v___x_5485_; 
v___x_5485_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_next_5475_, v_a_5477_, v_a_5478_, v_a_5479_, v_a_5480_, v_a_5481_);
if (lean_obj_tag(v___x_5485_) == 0)
{
lean_object* v_a_5486_; lean_object* v_snd_5487_; 
v_a_5486_ = lean_ctor_get(v___x_5485_, 0);
lean_inc(v_a_5486_);
lean_dec_ref_known(v___x_5485_, 1);
v_snd_5487_ = lean_ctor_get(v_a_5486_, 1);
lean_inc(v_snd_5487_);
lean_dec(v_a_5486_);
if (lean_obj_tag(v_rest_5476_) == 0)
{
lean_object* v___x_5488_; 
lean_dec(v_snd_5487_);
v___x_5488_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_next_5475_, v_a_5477_, v_a_5478_, v_a_5479_, v_a_5480_, v_a_5481_);
lean_dec(v_next_5475_);
return v___x_5488_;
}
else
{
lean_object* v_fst_5489_; lean_object* v_snd_5490_; lean_object* v_head_5491_; lean_object* v_tail_5492_; lean_object* v___x_5493_; uint8_t v___x_5494_; 
lean_dec(v_next_5475_);
v_fst_5489_ = lean_ctor_get(v_snd_5487_, 0);
lean_inc(v_fst_5489_);
v_snd_5490_ = lean_ctor_get(v_snd_5487_, 1);
lean_inc(v_snd_5490_);
lean_dec(v_snd_5487_);
v_head_5491_ = lean_ctor_get(v_rest_5476_, 0);
v_tail_5492_ = lean_ctor_get(v_rest_5476_, 1);
v___x_5493_ = lean_box(3);
v___x_5494_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_head_5491_, v___x_5493_);
if (v___x_5494_ == 0)
{
lean_object* v___x_5495_; 
lean_dec(v_fst_5489_);
v___x_5495_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_snd_5490_, v_head_5491_, v___x_5483_);
lean_dec(v_snd_5490_);
v_next_5475_ = v___x_5495_;
v_rest_5476_ = v_tail_5492_;
goto _start;
}
else
{
lean_dec(v_snd_5490_);
v_next_5475_ = v_fst_5489_;
v_rest_5476_ = v_tail_5492_;
goto _start;
}
}
}
else
{
lean_object* v_a_5498_; lean_object* v___x_5500_; uint8_t v_isShared_5501_; uint8_t v_isSharedCheck_5505_; 
lean_dec(v_next_5475_);
v_a_5498_ = lean_ctor_get(v___x_5485_, 0);
v_isSharedCheck_5505_ = !lean_is_exclusive(v___x_5485_);
if (v_isSharedCheck_5505_ == 0)
{
v___x_5500_ = v___x_5485_;
v_isShared_5501_ = v_isSharedCheck_5505_;
goto v_resetjp_5499_;
}
else
{
lean_inc(v_a_5498_);
lean_dec(v___x_5485_);
v___x_5500_ = lean_box(0);
v_isShared_5501_ = v_isSharedCheck_5505_;
goto v_resetjp_5499_;
}
v_resetjp_5499_:
{
lean_object* v___x_5503_; 
if (v_isShared_5501_ == 0)
{
v___x_5503_ = v___x_5500_;
goto v_reusejp_5502_;
}
else
{
lean_object* v_reuseFailAlloc_5504_; 
v_reuseFailAlloc_5504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5504_, 0, v_a_5498_);
v___x_5503_ = v_reuseFailAlloc_5504_;
goto v_reusejp_5502_;
}
v_reusejp_5502_:
{
return v___x_5503_;
}
}
}
}
else
{
lean_object* v___x_5506_; lean_object* v___x_5507_; 
lean_dec(v_next_5475_);
v___x_5506_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___x_5507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5507_, 0, v___x_5506_);
return v___x_5507_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg___boxed(lean_object* v_next_5508_, lean_object* v_rest_5509_, lean_object* v_a_5510_, lean_object* v_a_5511_, lean_object* v_a_5512_, lean_object* v_a_5513_, lean_object* v_a_5514_, lean_object* v_a_5515_){
_start:
{
lean_object* v_res_5516_; 
v_res_5516_ = l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg(v_next_5508_, v_rest_5509_, v_a_5510_, v_a_5511_, v_a_5512_, v_a_5513_, v_a_5514_);
lean_dec(v_a_5514_);
lean_dec_ref(v_a_5513_);
lean_dec(v_a_5512_);
lean_dec_ref(v_a_5511_);
lean_dec(v_a_5510_);
lean_dec(v_rest_5509_);
return v_res_5516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux(lean_object* v_00_u03b1_5517_, lean_object* v_next_5518_, lean_object* v_rest_5519_, lean_object* v_a_5520_, lean_object* v_a_5521_, lean_object* v_a_5522_, lean_object* v_a_5523_, lean_object* v_a_5524_){
_start:
{
lean_object* v___x_5526_; 
v___x_5526_ = l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg(v_next_5518_, v_rest_5519_, v_a_5520_, v_a_5521_, v_a_5522_, v_a_5523_, v_a_5524_);
return v___x_5526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux___boxed(lean_object* v_00_u03b1_5527_, lean_object* v_next_5528_, lean_object* v_rest_5529_, lean_object* v_a_5530_, lean_object* v_a_5531_, lean_object* v_a_5532_, lean_object* v_a_5533_, lean_object* v_a_5534_, lean_object* v_a_5535_){
_start:
{
lean_object* v_res_5536_; 
v_res_5536_ = l_Lean_Meta_LazyDiscrTree_extractKeyAux(v_00_u03b1_5527_, v_next_5528_, v_rest_5529_, v_a_5530_, v_a_5531_, v_a_5532_, v_a_5533_, v_a_5534_);
lean_dec(v_a_5534_);
lean_dec_ref(v_a_5533_);
lean_dec(v_a_5532_);
lean_dec_ref(v_a_5531_);
lean_dec(v_a_5530_);
lean_dec(v_rest_5529_);
return v_res_5536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey___redArg(lean_object* v_t_5537_, lean_object* v_path_5538_, lean_object* v_a_5539_, lean_object* v_a_5540_, lean_object* v_a_5541_, lean_object* v_a_5542_){
_start:
{
if (lean_obj_tag(v_path_5538_) == 0)
{
lean_object* v___x_5544_; lean_object* v___x_5545_; lean_object* v___x_5546_; 
v___x_5544_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___x_5545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5545_, 0, v___x_5544_);
lean_ctor_set(v___x_5545_, 1, v_t_5537_);
v___x_5546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5546_, 0, v___x_5545_);
return v___x_5546_;
}
else
{
lean_object* v_head_5547_; lean_object* v_tail_5548_; lean_object* v_roots_5549_; lean_object* v___x_5550_; lean_object* v_idx_5551_; lean_object* v___x_5552_; lean_object* v___x_5553_; 
v_head_5547_ = lean_ctor_get(v_path_5538_, 0);
lean_inc(v_head_5547_);
v_tail_5548_ = lean_ctor_get(v_path_5538_, 1);
lean_inc(v_tail_5548_);
lean_dec_ref_known(v_path_5538_, 2);
v_roots_5549_ = lean_ctor_get(v_t_5537_, 1);
v___x_5550_ = lean_unsigned_to_nat(0u);
v_idx_5551_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_roots_5549_, v_head_5547_, v___x_5550_);
lean_dec(v_head_5547_);
v___x_5552_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_extractKeyAux___boxed), 9, 3);
lean_closure_set(v___x_5552_, 0, lean_box(0));
lean_closure_set(v___x_5552_, 1, v_idx_5551_);
lean_closure_set(v___x_5552_, 2, v_tail_5548_);
v___x_5553_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_t_5537_, v___x_5552_, v_a_5539_, v_a_5540_, v_a_5541_, v_a_5542_);
return v___x_5553_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey___redArg___boxed(lean_object* v_t_5554_, lean_object* v_path_5555_, lean_object* v_a_5556_, lean_object* v_a_5557_, lean_object* v_a_5558_, lean_object* v_a_5559_, lean_object* v_a_5560_){
_start:
{
lean_object* v_res_5561_; 
v_res_5561_ = l_Lean_Meta_LazyDiscrTree_extractKey___redArg(v_t_5554_, v_path_5555_, v_a_5556_, v_a_5557_, v_a_5558_, v_a_5559_);
lean_dec(v_a_5559_);
lean_dec_ref(v_a_5558_);
lean_dec(v_a_5557_);
lean_dec_ref(v_a_5556_);
return v_res_5561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey(lean_object* v_00_u03b1_5562_, lean_object* v_t_5563_, lean_object* v_path_5564_, lean_object* v_a_5565_, lean_object* v_a_5566_, lean_object* v_a_5567_, lean_object* v_a_5568_){
_start:
{
lean_object* v___x_5570_; 
v___x_5570_ = l_Lean_Meta_LazyDiscrTree_extractKey___redArg(v_t_5563_, v_path_5564_, v_a_5565_, v_a_5566_, v_a_5567_, v_a_5568_);
return v___x_5570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey___boxed(lean_object* v_00_u03b1_5571_, lean_object* v_t_5572_, lean_object* v_path_5573_, lean_object* v_a_5574_, lean_object* v_a_5575_, lean_object* v_a_5576_, lean_object* v_a_5577_, lean_object* v_a_5578_){
_start:
{
lean_object* v_res_5579_; 
v_res_5579_ = l_Lean_Meta_LazyDiscrTree_extractKey(v_00_u03b1_5571_, v_t_5572_, v_path_5573_, v_a_5574_, v_a_5575_, v_a_5576_, v_a_5577_);
lean_dec(v_a_5577_);
lean_dec_ref(v_a_5576_);
lean_dec(v_a_5575_);
lean_dec_ref(v_a_5574_);
return v_res_5579_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(lean_object* v_as_x27_5580_, lean_object* v_b_5581_, lean_object* v___y_5582_, lean_object* v___y_5583_, lean_object* v___y_5584_, lean_object* v___y_5585_){
_start:
{
if (lean_obj_tag(v_as_x27_5580_) == 0)
{
lean_object* v___x_5587_; 
v___x_5587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5587_, 0, v_b_5581_);
return v___x_5587_;
}
else
{
lean_object* v_head_5588_; lean_object* v_tail_5589_; lean_object* v_fst_5590_; lean_object* v_snd_5591_; lean_object* v___x_5592_; 
v_head_5588_ = lean_ctor_get(v_as_x27_5580_, 0);
v_tail_5589_ = lean_ctor_get(v_as_x27_5580_, 1);
v_fst_5590_ = lean_ctor_get(v_b_5581_, 0);
lean_inc(v_fst_5590_);
v_snd_5591_ = lean_ctor_get(v_b_5581_, 1);
lean_inc(v_snd_5591_);
lean_dec_ref(v_b_5581_);
lean_inc(v_head_5588_);
v___x_5592_ = l_Lean_Meta_LazyDiscrTree_extractKey___redArg(v_snd_5591_, v_head_5588_, v___y_5582_, v___y_5583_, v___y_5584_, v___y_5585_);
if (lean_obj_tag(v___x_5592_) == 0)
{
lean_object* v_a_5593_; lean_object* v_fst_5594_; lean_object* v_snd_5595_; lean_object* v___x_5597_; uint8_t v_isShared_5598_; uint8_t v_isSharedCheck_5604_; 
v_a_5593_ = lean_ctor_get(v___x_5592_, 0);
lean_inc(v_a_5593_);
lean_dec_ref_known(v___x_5592_, 1);
v_fst_5594_ = lean_ctor_get(v_a_5593_, 0);
v_snd_5595_ = lean_ctor_get(v_a_5593_, 1);
v_isSharedCheck_5604_ = !lean_is_exclusive(v_a_5593_);
if (v_isSharedCheck_5604_ == 0)
{
v___x_5597_ = v_a_5593_;
v_isShared_5598_ = v_isSharedCheck_5604_;
goto v_resetjp_5596_;
}
else
{
lean_inc(v_snd_5595_);
lean_inc(v_fst_5594_);
lean_dec(v_a_5593_);
v___x_5597_ = lean_box(0);
v_isShared_5598_ = v_isSharedCheck_5604_;
goto v_resetjp_5596_;
}
v_resetjp_5596_:
{
lean_object* v___x_5599_; lean_object* v___x_5601_; 
v___x_5599_ = l_Array_append___redArg(v_fst_5590_, v_fst_5594_);
lean_dec(v_fst_5594_);
if (v_isShared_5598_ == 0)
{
lean_ctor_set(v___x_5597_, 0, v___x_5599_);
v___x_5601_ = v___x_5597_;
goto v_reusejp_5600_;
}
else
{
lean_object* v_reuseFailAlloc_5603_; 
v_reuseFailAlloc_5603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5603_, 0, v___x_5599_);
lean_ctor_set(v_reuseFailAlloc_5603_, 1, v_snd_5595_);
v___x_5601_ = v_reuseFailAlloc_5603_;
goto v_reusejp_5600_;
}
v_reusejp_5600_:
{
v_as_x27_5580_ = v_tail_5589_;
v_b_5581_ = v___x_5601_;
goto _start;
}
}
}
else
{
lean_dec(v_fst_5590_);
return v___x_5592_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg___boxed(lean_object* v_as_x27_5605_, lean_object* v_b_5606_, lean_object* v___y_5607_, lean_object* v___y_5608_, lean_object* v___y_5609_, lean_object* v___y_5610_, lean_object* v___y_5611_){
_start:
{
lean_object* v_res_5612_; 
v_res_5612_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(v_as_x27_5605_, v_b_5606_, v___y_5607_, v___y_5608_, v___y_5609_, v___y_5610_);
lean_dec(v___y_5610_);
lean_dec_ref(v___y_5609_);
lean_dec(v___y_5608_);
lean_dec_ref(v___y_5607_);
lean_dec(v_as_x27_5605_);
return v_res_5612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(lean_object* v_t_5613_, lean_object* v_keys_5614_, lean_object* v_a_5615_, lean_object* v_a_5616_, lean_object* v_a_5617_, lean_object* v_a_5618_){
_start:
{
lean_object* v_allExtracted_5620_; lean_object* v___x_5621_; lean_object* v___x_5622_; 
v_allExtracted_5620_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___x_5621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5621_, 0, v_allExtracted_5620_);
lean_ctor_set(v___x_5621_, 1, v_t_5613_);
v___x_5622_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(v_keys_5614_, v___x_5621_, v_a_5615_, v_a_5616_, v_a_5617_, v_a_5618_);
if (lean_obj_tag(v___x_5622_) == 0)
{
lean_object* v_a_5623_; lean_object* v___x_5625_; uint8_t v_isShared_5626_; uint8_t v_isSharedCheck_5639_; 
v_a_5623_ = lean_ctor_get(v___x_5622_, 0);
v_isSharedCheck_5639_ = !lean_is_exclusive(v___x_5622_);
if (v_isSharedCheck_5639_ == 0)
{
v___x_5625_ = v___x_5622_;
v_isShared_5626_ = v_isSharedCheck_5639_;
goto v_resetjp_5624_;
}
else
{
lean_inc(v_a_5623_);
lean_dec(v___x_5622_);
v___x_5625_ = lean_box(0);
v_isShared_5626_ = v_isSharedCheck_5639_;
goto v_resetjp_5624_;
}
v_resetjp_5624_:
{
lean_object* v_fst_5627_; lean_object* v_snd_5628_; lean_object* v___x_5630_; uint8_t v_isShared_5631_; uint8_t v_isSharedCheck_5638_; 
v_fst_5627_ = lean_ctor_get(v_a_5623_, 0);
v_snd_5628_ = lean_ctor_get(v_a_5623_, 1);
v_isSharedCheck_5638_ = !lean_is_exclusive(v_a_5623_);
if (v_isSharedCheck_5638_ == 0)
{
v___x_5630_ = v_a_5623_;
v_isShared_5631_ = v_isSharedCheck_5638_;
goto v_resetjp_5629_;
}
else
{
lean_inc(v_snd_5628_);
lean_inc(v_fst_5627_);
lean_dec(v_a_5623_);
v___x_5630_ = lean_box(0);
v_isShared_5631_ = v_isSharedCheck_5638_;
goto v_resetjp_5629_;
}
v_resetjp_5629_:
{
lean_object* v___x_5633_; 
if (v_isShared_5631_ == 0)
{
v___x_5633_ = v___x_5630_;
goto v_reusejp_5632_;
}
else
{
lean_object* v_reuseFailAlloc_5637_; 
v_reuseFailAlloc_5637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5637_, 0, v_fst_5627_);
lean_ctor_set(v_reuseFailAlloc_5637_, 1, v_snd_5628_);
v___x_5633_ = v_reuseFailAlloc_5637_;
goto v_reusejp_5632_;
}
v_reusejp_5632_:
{
lean_object* v___x_5635_; 
if (v_isShared_5626_ == 0)
{
lean_ctor_set(v___x_5625_, 0, v___x_5633_);
v___x_5635_ = v___x_5625_;
goto v_reusejp_5634_;
}
else
{
lean_object* v_reuseFailAlloc_5636_; 
v_reuseFailAlloc_5636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5636_, 0, v___x_5633_);
v___x_5635_ = v_reuseFailAlloc_5636_;
goto v_reusejp_5634_;
}
v_reusejp_5634_:
{
return v___x_5635_;
}
}
}
}
}
else
{
return v___x_5622_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys___redArg___boxed(lean_object* v_t_5640_, lean_object* v_keys_5641_, lean_object* v_a_5642_, lean_object* v_a_5643_, lean_object* v_a_5644_, lean_object* v_a_5645_, lean_object* v_a_5646_){
_start:
{
lean_object* v_res_5647_; 
v_res_5647_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_t_5640_, v_keys_5641_, v_a_5642_, v_a_5643_, v_a_5644_, v_a_5645_);
lean_dec(v_a_5645_);
lean_dec_ref(v_a_5644_);
lean_dec(v_a_5643_);
lean_dec_ref(v_a_5642_);
lean_dec(v_keys_5641_);
return v_res_5647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys(lean_object* v_00_u03b1_5648_, lean_object* v_t_5649_, lean_object* v_keys_5650_, lean_object* v_a_5651_, lean_object* v_a_5652_, lean_object* v_a_5653_, lean_object* v_a_5654_){
_start:
{
lean_object* v___x_5656_; 
v___x_5656_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_t_5649_, v_keys_5650_, v_a_5651_, v_a_5652_, v_a_5653_, v_a_5654_);
return v___x_5656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys___boxed(lean_object* v_00_u03b1_5657_, lean_object* v_t_5658_, lean_object* v_keys_5659_, lean_object* v_a_5660_, lean_object* v_a_5661_, lean_object* v_a_5662_, lean_object* v_a_5663_, lean_object* v_a_5664_){
_start:
{
lean_object* v_res_5665_; 
v_res_5665_ = l_Lean_Meta_LazyDiscrTree_extractKeys(v_00_u03b1_5657_, v_t_5658_, v_keys_5659_, v_a_5660_, v_a_5661_, v_a_5662_, v_a_5663_);
lean_dec(v_a_5663_);
lean_dec_ref(v_a_5662_);
lean_dec(v_a_5661_);
lean_dec_ref(v_a_5660_);
lean_dec(v_keys_5659_);
return v_res_5665_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0(lean_object* v_00_u03b1_5666_, lean_object* v_as_5667_, lean_object* v_as_x27_5668_, lean_object* v_b_5669_, lean_object* v_a_5670_, lean_object* v___y_5671_, lean_object* v___y_5672_, lean_object* v___y_5673_, lean_object* v___y_5674_){
_start:
{
lean_object* v___x_5676_; 
v___x_5676_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(v_as_x27_5668_, v_b_5669_, v___y_5671_, v___y_5672_, v___y_5673_, v___y_5674_);
return v___x_5676_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___boxed(lean_object* v_00_u03b1_5677_, lean_object* v_as_5678_, lean_object* v_as_x27_5679_, lean_object* v_b_5680_, lean_object* v_a_5681_, lean_object* v___y_5682_, lean_object* v___y_5683_, lean_object* v___y_5684_, lean_object* v___y_5685_, lean_object* v___y_5686_){
_start:
{
lean_object* v_res_5687_; 
v_res_5687_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0(v_00_u03b1_5677_, v_as_5678_, v_as_x27_5679_, v_b_5680_, v_a_5681_, v___y_5682_, v___y_5683_, v___y_5684_, v___y_5685_);
lean_dec(v___y_5685_);
lean_dec_ref(v___y_5684_);
lean_dec(v___y_5683_);
lean_dec_ref(v___y_5682_);
lean_dec(v_as_x27_5679_);
lean_dec(v_as_5678_);
return v_res_5687_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1(void){
_start:
{
lean_object* v___x_5689_; lean_object* v___x_5690_; 
v___x_5689_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__0));
v___x_5690_ = l_Lean_stringToMessageData(v___x_5689_);
return v___x_5690_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3(void){
_start:
{
lean_object* v___x_5692_; lean_object* v___x_5693_; 
v___x_5692_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__2));
v___x_5693_ = l_Lean_stringToMessageData(v___x_5692_);
return v___x_5693_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5(void){
_start:
{
lean_object* v___x_5695_; lean_object* v___x_5696_; 
v___x_5695_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__4));
v___x_5696_ = l_Lean_stringToMessageData(v___x_5695_);
return v___x_5696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg(lean_object* v_inst_5697_, lean_object* v_inst_5698_, lean_object* v_inst_5699_, lean_object* v_inst_5700_, lean_object* v_f_5701_){
_start:
{
lean_object* v_module_5702_; lean_object* v_const_5703_; lean_object* v_exception_5704_; lean_object* v___x_5705_; lean_object* v___x_5706_; lean_object* v___x_5707_; lean_object* v___x_5708_; lean_object* v___x_5709_; lean_object* v___x_5710_; lean_object* v___x_5711_; lean_object* v___x_5712_; lean_object* v___x_5713_; lean_object* v___x_5714_; lean_object* v___x_5715_; lean_object* v___x_5716_; 
v_module_5702_ = lean_ctor_get(v_f_5701_, 0);
lean_inc(v_module_5702_);
v_const_5703_ = lean_ctor_get(v_f_5701_, 1);
lean_inc(v_const_5703_);
v_exception_5704_ = lean_ctor_get(v_f_5701_, 2);
lean_inc_ref(v_exception_5704_);
lean_dec_ref(v_f_5701_);
v___x_5705_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1);
v___x_5706_ = l_Lean_MessageData_ofName(v_const_5703_);
v___x_5707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5707_, 0, v___x_5705_);
lean_ctor_set(v___x_5707_, 1, v___x_5706_);
v___x_5708_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3);
v___x_5709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5709_, 0, v___x_5707_);
lean_ctor_set(v___x_5709_, 1, v___x_5708_);
v___x_5710_ = l_Lean_MessageData_ofName(v_module_5702_);
v___x_5711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5711_, 0, v___x_5709_);
lean_ctor_set(v___x_5711_, 1, v___x_5710_);
v___x_5712_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5);
v___x_5713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5713_, 0, v___x_5711_);
lean_ctor_set(v___x_5713_, 1, v___x_5712_);
v___x_5714_ = l_Lean_Exception_toMessageData(v_exception_5704_);
v___x_5715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5715_, 0, v___x_5713_);
lean_ctor_set(v___x_5715_, 1, v___x_5714_);
v___x_5716_ = l_Lean_logError___redArg(v_inst_5697_, v_inst_5698_, v_inst_5699_, v_inst_5700_, v___x_5715_);
return v___x_5716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure(lean_object* v_m_5717_, lean_object* v_inst_5718_, lean_object* v_inst_5719_, lean_object* v_inst_5720_, lean_object* v_inst_5721_, lean_object* v_f_5722_){
_start:
{
lean_object* v___x_5723_; 
v___x_5723_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg(v_inst_5718_, v_inst_5719_, v_inst_5720_, v_inst_5721_, v_f_5722_);
return v___x_5723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__0(lean_object* v_tasks_5724_, lean_object* v_toPure_5725_, lean_object* v_t_5726_){
_start:
{
lean_object* v___x_5727_; lean_object* v___x_5728_; 
v___x_5727_ = lean_array_push(v_tasks_5724_, v_t_5726_);
v___x_5728_ = lean_apply_2(v_toPure_5725_, lean_box(0), v___x_5727_);
return v___x_5728_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(lean_object* v_inst_5729_, lean_object* v_inst_5730_, lean_object* v_cctx_5731_, lean_object* v_env_5732_, lean_object* v_act_5733_, lean_object* v_constantsPerTask_5734_, lean_object* v_n_5735_, lean_object* v_ngen_5736_, lean_object* v_tasks_5737_, lean_object* v_start_5738_, lean_object* v_cnt_5739_, lean_object* v_idx_5740_){
_start:
{
lean_object* v___x_5741_; lean_object* v_toApplicative_5742_; lean_object* v_moduleData_5743_; lean_object* v_toBind_5744_; lean_object* v_toPure_5745_; lean_object* v___x_5746_; uint8_t v___x_5747_; 
v___x_5741_ = l_Lean_Environment_header(v_env_5732_);
v_toApplicative_5742_ = lean_ctor_get(v_inst_5729_, 0);
v_moduleData_5743_ = lean_ctor_get(v___x_5741_, 7);
lean_inc_ref(v_moduleData_5743_);
lean_dec_ref(v___x_5741_);
v_toBind_5744_ = lean_ctor_get(v_inst_5729_, 1);
v_toPure_5745_ = lean_ctor_get(v_toApplicative_5742_, 1);
v___x_5746_ = lean_array_get_size(v_moduleData_5743_);
v___x_5747_ = lean_nat_dec_lt(v_idx_5740_, v___x_5746_);
if (v___x_5747_ == 0)
{
uint8_t v___x_5748_; 
lean_inc(v_toPure_5745_);
lean_inc(v_toBind_5744_);
lean_dec_ref(v_moduleData_5743_);
lean_dec(v_idx_5740_);
lean_dec(v_cnt_5739_);
lean_dec(v_constantsPerTask_5734_);
lean_dec_ref(v_inst_5729_);
v___x_5748_ = lean_nat_dec_lt(v_start_5738_, v_n_5735_);
if (v___x_5748_ == 0)
{
lean_object* v___x_5749_; 
lean_dec(v_toBind_5744_);
lean_dec(v_start_5738_);
lean_dec_ref(v_ngen_5736_);
lean_dec(v_n_5735_);
lean_dec_ref(v_act_5733_);
lean_dec_ref(v_env_5732_);
lean_dec_ref(v_cctx_5731_);
lean_dec(v_inst_5730_);
v___x_5749_ = lean_apply_2(v_toPure_5745_, lean_box(0), v_tasks_5737_);
return v___x_5749_;
}
else
{
lean_object* v_namePrefix_5750_; lean_object* v_idx_5751_; lean_object* v___x_5753_; uint8_t v_isShared_5754_; uint8_t v_isSharedCheck_5766_; 
v_namePrefix_5750_ = lean_ctor_get(v_ngen_5736_, 0);
v_idx_5751_ = lean_ctor_get(v_ngen_5736_, 1);
v_isSharedCheck_5766_ = !lean_is_exclusive(v_ngen_5736_);
if (v_isSharedCheck_5766_ == 0)
{
v___x_5753_ = v_ngen_5736_;
v_isShared_5754_ = v_isSharedCheck_5766_;
goto v_resetjp_5752_;
}
else
{
lean_inc(v_idx_5751_);
lean_inc(v_namePrefix_5750_);
lean_dec(v_ngen_5736_);
v___x_5753_ = lean_box(0);
v_isShared_5754_ = v_isSharedCheck_5766_;
goto v_resetjp_5752_;
}
v_resetjp_5752_:
{
lean_object* v___f_5755_; lean_object* v___x_5756_; lean_object* v___x_5757_; lean_object* v___x_5759_; 
v___f_5755_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5755_, 0, v_tasks_5737_);
lean_closure_set(v___f_5755_, 1, v_toPure_5745_);
v___x_5756_ = l_Lean_Name_num___override(v_namePrefix_5750_, v_idx_5751_);
v___x_5757_ = lean_unsigned_to_nat(1u);
if (v_isShared_5754_ == 0)
{
lean_ctor_set(v___x_5753_, 1, v___x_5757_);
lean_ctor_set(v___x_5753_, 0, v___x_5756_);
v___x_5759_ = v___x_5753_;
goto v_reusejp_5758_;
}
else
{
lean_object* v_reuseFailAlloc_5765_; 
v_reuseFailAlloc_5765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5765_, 0, v___x_5756_);
lean_ctor_set(v_reuseFailAlloc_5765_, 1, v___x_5757_);
v___x_5759_ = v_reuseFailAlloc_5765_;
goto v_reusejp_5758_;
}
v_reusejp_5758_:
{
lean_object* v___x_5760_; lean_object* v___x_5761_; lean_object* v___x_5762_; lean_object* v___x_5763_; lean_object* v___x_5764_; 
v___x_5760_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_5760_, 0, lean_box(0));
lean_closure_set(v___x_5760_, 1, v_cctx_5731_);
lean_closure_set(v___x_5760_, 2, v___x_5759_);
lean_closure_set(v___x_5760_, 3, v_env_5732_);
lean_closure_set(v___x_5760_, 4, v_act_5733_);
lean_closure_set(v___x_5760_, 5, v_start_5738_);
lean_closure_set(v___x_5760_, 6, v_n_5735_);
v___x_5761_ = lean_unsigned_to_nat(0u);
v___x_5762_ = lean_alloc_closure((void*)(l_BaseIO_asTask___boxed), 4, 3);
lean_closure_set(v___x_5762_, 0, lean_box(0));
lean_closure_set(v___x_5762_, 1, v___x_5760_);
lean_closure_set(v___x_5762_, 2, v___x_5761_);
v___x_5763_ = lean_apply_2(v_inst_5730_, lean_box(0), v___x_5762_);
v___x_5764_ = lean_apply_4(v_toBind_5744_, lean_box(0), lean_box(0), v___x_5763_, v___f_5755_);
return v___x_5764_;
}
}
}
}
else
{
lean_object* v_mdata_5767_; lean_object* v_constants_5768_; lean_object* v___x_5769_; lean_object* v_cnt_5770_; uint8_t v___x_5771_; 
v_mdata_5767_ = lean_array_fget(v_moduleData_5743_, v_idx_5740_);
lean_dec_ref(v_moduleData_5743_);
v_constants_5768_ = lean_ctor_get(v_mdata_5767_, 2);
lean_inc_ref(v_constants_5768_);
lean_dec(v_mdata_5767_);
v___x_5769_ = lean_array_get_size(v_constants_5768_);
lean_dec_ref(v_constants_5768_);
v_cnt_5770_ = lean_nat_add(v_cnt_5739_, v___x_5769_);
lean_dec(v_cnt_5739_);
v___x_5771_ = lean_nat_dec_lt(v_constantsPerTask_5734_, v_cnt_5770_);
if (v___x_5771_ == 0)
{
lean_object* v___x_5772_; lean_object* v___x_5773_; 
v___x_5772_ = lean_unsigned_to_nat(1u);
v___x_5773_ = lean_nat_add(v_idx_5740_, v___x_5772_);
lean_dec(v_idx_5740_);
v_cnt_5739_ = v_cnt_5770_;
v_idx_5740_ = v___x_5773_;
goto _start;
}
else
{
lean_object* v_namePrefix_5775_; lean_object* v_idx_5776_; lean_object* v___x_5778_; uint8_t v_isShared_5779_; uint8_t v_isSharedCheck_5794_; 
lean_inc(v_toBind_5744_);
lean_dec(v_cnt_5770_);
v_namePrefix_5775_ = lean_ctor_get(v_ngen_5736_, 0);
v_idx_5776_ = lean_ctor_get(v_ngen_5736_, 1);
v_isSharedCheck_5794_ = !lean_is_exclusive(v_ngen_5736_);
if (v_isSharedCheck_5794_ == 0)
{
v___x_5778_ = v_ngen_5736_;
v_isShared_5779_ = v_isSharedCheck_5794_;
goto v_resetjp_5777_;
}
else
{
lean_inc(v_idx_5776_);
lean_inc(v_namePrefix_5775_);
lean_dec(v_ngen_5736_);
v___x_5778_ = lean_box(0);
v_isShared_5779_ = v_isSharedCheck_5794_;
goto v_resetjp_5777_;
}
v_resetjp_5777_:
{
lean_object* v___x_5780_; lean_object* v___x_5781_; lean_object* v___x_5783_; 
lean_inc(v_idx_5776_);
lean_inc(v_namePrefix_5775_);
v___x_5780_ = l_Lean_Name_num___override(v_namePrefix_5775_, v_idx_5776_);
v___x_5781_ = lean_unsigned_to_nat(1u);
if (v_isShared_5779_ == 0)
{
lean_ctor_set(v___x_5778_, 1, v___x_5781_);
lean_ctor_set(v___x_5778_, 0, v___x_5780_);
v___x_5783_ = v___x_5778_;
goto v_reusejp_5782_;
}
else
{
lean_object* v_reuseFailAlloc_5793_; 
v_reuseFailAlloc_5793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5793_, 0, v___x_5780_);
lean_ctor_set(v_reuseFailAlloc_5793_, 1, v___x_5781_);
v___x_5783_ = v_reuseFailAlloc_5793_;
goto v_reusejp_5782_;
}
v_reusejp_5782_:
{
lean_object* v___x_5784_; lean_object* v___x_5785_; lean_object* v___x_5786_; lean_object* v___f_5787_; lean_object* v___x_5788_; lean_object* v___x_5789_; lean_object* v___x_5790_; lean_object* v___x_5791_; lean_object* v___x_5792_; 
v___x_5784_ = lean_nat_add(v_idx_5776_, v___x_5781_);
lean_dec(v_idx_5776_);
v___x_5785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5785_, 0, v_namePrefix_5775_);
lean_ctor_set(v___x_5785_, 1, v___x_5784_);
v___x_5786_ = lean_nat_add(v_idx_5740_, v___x_5781_);
lean_dec(v_idx_5740_);
lean_inc(v___x_5786_);
lean_inc_ref(v_act_5733_);
lean_inc_ref(v_env_5732_);
lean_inc_ref(v_cctx_5731_);
lean_inc(v_inst_5730_);
v___f_5787_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__1), 11, 10);
lean_closure_set(v___f_5787_, 0, v_tasks_5737_);
lean_closure_set(v___f_5787_, 1, v_inst_5729_);
lean_closure_set(v___f_5787_, 2, v_inst_5730_);
lean_closure_set(v___f_5787_, 3, v_cctx_5731_);
lean_closure_set(v___f_5787_, 4, v_env_5732_);
lean_closure_set(v___f_5787_, 5, v_act_5733_);
lean_closure_set(v___f_5787_, 6, v_constantsPerTask_5734_);
lean_closure_set(v___f_5787_, 7, v_n_5735_);
lean_closure_set(v___f_5787_, 8, v___x_5785_);
lean_closure_set(v___f_5787_, 9, v___x_5786_);
v___x_5788_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_5788_, 0, lean_box(0));
lean_closure_set(v___x_5788_, 1, v_cctx_5731_);
lean_closure_set(v___x_5788_, 2, v___x_5783_);
lean_closure_set(v___x_5788_, 3, v_env_5732_);
lean_closure_set(v___x_5788_, 4, v_act_5733_);
lean_closure_set(v___x_5788_, 5, v_start_5738_);
lean_closure_set(v___x_5788_, 6, v___x_5786_);
v___x_5789_ = lean_unsigned_to_nat(0u);
v___x_5790_ = lean_alloc_closure((void*)(l_BaseIO_asTask___boxed), 4, 3);
lean_closure_set(v___x_5790_, 0, lean_box(0));
lean_closure_set(v___x_5790_, 1, v___x_5788_);
lean_closure_set(v___x_5790_, 2, v___x_5789_);
v___x_5791_ = lean_apply_2(v_inst_5730_, lean_box(0), v___x_5790_);
v___x_5792_ = lean_apply_4(v_toBind_5744_, lean_box(0), lean_box(0), v___x_5791_, v___f_5787_);
return v___x_5792_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__1(lean_object* v_tasks_5795_, lean_object* v_inst_5796_, lean_object* v_inst_5797_, lean_object* v_cctx_5798_, lean_object* v_env_5799_, lean_object* v_act_5800_, lean_object* v_constantsPerTask_5801_, lean_object* v_n_5802_, lean_object* v___x_5803_, lean_object* v___x_5804_, lean_object* v_t_5805_){
_start:
{
lean_object* v___x_5806_; lean_object* v___x_5807_; lean_object* v___x_5808_; 
v___x_5806_ = lean_array_push(v_tasks_5795_, v_t_5805_);
v___x_5807_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_5804_);
v___x_5808_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(v_inst_5796_, v_inst_5797_, v_cctx_5798_, v_env_5799_, v_act_5800_, v_constantsPerTask_5801_, v_n_5802_, v___x_5803_, v___x_5806_, v___x_5804_, v___x_5807_, v___x_5804_);
return v___x_5808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go(lean_object* v_m_5809_, lean_object* v_00_u03b1_5810_, lean_object* v_inst_5811_, lean_object* v_inst_5812_, lean_object* v_cctx_5813_, lean_object* v_env_5814_, lean_object* v_act_5815_, lean_object* v_constantsPerTask_5816_, lean_object* v_n_5817_, lean_object* v_ngen_5818_, lean_object* v_tasks_5819_, lean_object* v_start_5820_, lean_object* v_cnt_5821_, lean_object* v_idx_5822_){
_start:
{
lean_object* v___x_5823_; 
v___x_5823_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(v_inst_5811_, v_inst_5812_, v_cctx_5813_, v_env_5814_, v_act_5815_, v_constantsPerTask_5816_, v_n_5817_, v_ngen_5818_, v_tasks_5819_, v_start_5820_, v_cnt_5821_, v_idx_5822_);
return v___x_5823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_getChildNgen_match__1_splitter___redArg(lean_object* v_x_5824_, lean_object* v_h__1_5825_){
_start:
{
lean_object* v_fst_5826_; lean_object* v_snd_5827_; lean_object* v___x_5828_; 
v_fst_5826_ = lean_ctor_get(v_x_5824_, 0);
lean_inc(v_fst_5826_);
v_snd_5827_ = lean_ctor_get(v_x_5824_, 1);
lean_inc(v_snd_5827_);
lean_dec_ref(v_x_5824_);
v___x_5828_ = lean_apply_2(v_h__1_5825_, v_fst_5826_, v_snd_5827_);
return v___x_5828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_getChildNgen_match__1_splitter(lean_object* v_motive_5829_, lean_object* v_x_5830_, lean_object* v_h__1_5831_){
_start:
{
lean_object* v_fst_5832_; lean_object* v_snd_5833_; lean_object* v___x_5834_; 
v_fst_5832_ = lean_ctor_get(v_x_5830_, 0);
lean_inc(v_fst_5832_);
v_snd_5833_ = lean_ctor_get(v_x_5830_, 1);
lean_inc(v_snd_5833_);
lean_dec_ref(v_x_5830_);
v___x_5834_ = lean_apply_2(v_h__1_5831_, v_fst_5832_, v_snd_5833_);
return v___x_5834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__0(lean_object* v_inst_5835_, lean_object* v_inst_5836_, lean_object* v_inst_5837_, lean_object* v_inst_5838_, lean_object* v_x_5839_, lean_object* v___y_5840_){
_start:
{
lean_object* v___x_5841_; 
v___x_5841_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg(v_inst_5835_, v_inst_5836_, v_inst_5837_, v_inst_5838_, v___y_5840_);
return v___x_5841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__1(lean_object* v_tree_5842_, lean_object* v_toPure_5843_, lean_object* v_____r_5844_){
_start:
{
lean_object* v___x_5845_; lean_object* v___x_5846_; 
v___x_5845_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_tree_5842_);
v___x_5846_ = lean_apply_2(v_toPure_5843_, lean_box(0), v___x_5845_);
return v___x_5846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__2(lean_object* v___x_5847_, lean_object* v___x_5848_, lean_object* v_toPure_5849_, lean_object* v_toBind_5850_, lean_object* v_inst_5851_, lean_object* v___f_5852_, lean_object* v_tasks_5853_){
_start:
{
lean_object* v___x_5854_; lean_object* v___x_5855_; lean_object* v___x_5856_; lean_object* v___x_5857_; lean_object* v___x_5858_; lean_object* v_r_5859_; lean_object* v_tree_5860_; lean_object* v_errors_5861_; lean_object* v___f_5862_; lean_object* v___x_5863_; lean_object* v___x_5864_; uint8_t v___x_5865_; 
v___x_5854_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__1);
lean_inc(v___x_5847_);
v___x_5855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5855_, 0, v___x_5847_);
lean_ctor_set(v___x_5855_, 1, v___x_5854_);
v___x_5856_ = lean_mk_empty_array_with_capacity(v___x_5847_);
lean_inc_ref(v___x_5856_);
v___x_5857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5857_, 0, v___x_5855_);
lean_ctor_set(v___x_5857_, 1, v___x_5856_);
v___x_5858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5858_, 0, v___x_5857_);
lean_ctor_set(v___x_5858_, 1, v___x_5856_);
v_r_5859_ = l_Lean_Meta_LazyDiscrTree_combineGet___redArg(v___x_5848_, v___x_5858_, v_tasks_5853_);
v_tree_5860_ = lean_ctor_get(v_r_5859_, 0);
lean_inc_ref(v_tree_5860_);
v_errors_5861_ = lean_ctor_get(v_r_5859_, 1);
lean_inc_ref(v_errors_5861_);
lean_dec(v_r_5859_);
lean_inc(v_toPure_5849_);
v___f_5862_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__1), 3, 2);
lean_closure_set(v___f_5862_, 0, v_tree_5860_);
lean_closure_set(v___f_5862_, 1, v_toPure_5849_);
v___x_5863_ = lean_array_get_size(v_errors_5861_);
v___x_5864_ = lean_box(0);
v___x_5865_ = lean_nat_dec_lt(v___x_5847_, v___x_5863_);
lean_dec(v___x_5847_);
if (v___x_5865_ == 0)
{
lean_object* v___x_5866_; lean_object* v___x_5867_; 
lean_dec_ref(v_errors_5861_);
lean_dec(v___f_5852_);
lean_dec_ref(v_inst_5851_);
v___x_5866_ = lean_apply_2(v_toPure_5849_, lean_box(0), v___x_5864_);
v___x_5867_ = lean_apply_4(v_toBind_5850_, lean_box(0), lean_box(0), v___x_5866_, v___f_5862_);
return v___x_5867_;
}
else
{
size_t v___x_5868_; size_t v___x_5869_; lean_object* v___x_5870_; lean_object* v___x_5871_; 
lean_dec(v_toPure_5849_);
v___x_5868_ = ((size_t)0ULL);
v___x_5869_ = lean_usize_of_nat(v___x_5863_);
v___x_5870_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_5851_, v___f_5852_, v_errors_5861_, v___x_5868_, v___x_5869_, v___x_5864_);
v___x_5871_ = lean_apply_4(v_toBind_5850_, lean_box(0), lean_box(0), v___x_5870_, v___f_5862_);
return v___x_5871_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg(lean_object* v_inst_5874_, lean_object* v_inst_5875_, lean_object* v_inst_5876_, lean_object* v_inst_5877_, lean_object* v_inst_5878_, lean_object* v_cctx_5879_, lean_object* v_ngen_5880_, lean_object* v_env_5881_, lean_object* v_act_5882_, lean_object* v_constantsPerTask_5883_){
_start:
{
lean_object* v___x_5884_; lean_object* v_moduleData_5885_; lean_object* v_toApplicative_5886_; lean_object* v_toBind_5887_; lean_object* v_n_5888_; lean_object* v___x_5889_; lean_object* v___x_5890_; lean_object* v___x_5891_; lean_object* v_toPure_5892_; lean_object* v___f_5893_; lean_object* v___x_5894_; lean_object* v___f_5895_; lean_object* v___x_5896_; 
v___x_5884_ = l_Lean_Environment_header(v_env_5881_);
v_moduleData_5885_ = lean_ctor_get(v___x_5884_, 7);
lean_inc_ref(v_moduleData_5885_);
lean_dec_ref(v___x_5884_);
v_toApplicative_5886_ = lean_ctor_get(v_inst_5874_, 0);
v_toBind_5887_ = lean_ctor_get(v_inst_5874_, 1);
lean_inc_n(v_toBind_5887_, 2);
v_n_5888_ = lean_array_get_size(v_moduleData_5885_);
lean_dec_ref(v_moduleData_5885_);
v___x_5889_ = lean_unsigned_to_nat(0u);
v___x_5890_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
lean_inc_ref_n(v_inst_5874_, 2);
v___x_5891_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(v_inst_5874_, v_inst_5878_, v_cctx_5879_, v_env_5881_, v_act_5882_, v_constantsPerTask_5883_, v_n_5888_, v_ngen_5880_, v___x_5890_, v___x_5889_, v___x_5889_, v___x_5889_);
v_toPure_5892_ = lean_ctor_get(v_toApplicative_5886_, 1);
lean_inc(v_toPure_5892_);
v___f_5893_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__0), 6, 4);
lean_closure_set(v___f_5893_, 0, v_inst_5874_);
lean_closure_set(v___f_5893_, 1, v_inst_5875_);
lean_closure_set(v___f_5893_, 2, v_inst_5876_);
lean_closure_set(v___f_5893_, 3, v_inst_5877_);
v___x_5894_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___redArg___closed__0));
v___f_5895_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__2), 7, 6);
lean_closure_set(v___f_5895_, 0, v___x_5889_);
lean_closure_set(v___f_5895_, 1, v___x_5894_);
lean_closure_set(v___f_5895_, 2, v_toPure_5892_);
lean_closure_set(v___f_5895_, 3, v_toBind_5887_);
lean_closure_set(v___f_5895_, 4, v_inst_5874_);
lean_closure_set(v___f_5895_, 5, v___f_5893_);
v___x_5896_ = lean_apply_4(v_toBind_5887_, lean_box(0), lean_box(0), v___x_5891_, v___f_5895_);
return v___x_5896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree(lean_object* v_m_5897_, lean_object* v_00_u03b1_5898_, lean_object* v_inst_5899_, lean_object* v_inst_5900_, lean_object* v_inst_5901_, lean_object* v_inst_5902_, lean_object* v_inst_5903_, lean_object* v_cctx_5904_, lean_object* v_ngen_5905_, lean_object* v_env_5906_, lean_object* v_act_5907_, lean_object* v_constantsPerTask_5908_){
_start:
{
lean_object* v___x_5909_; 
v___x_5909_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg(v_inst_5899_, v_inst_5900_, v_inst_5901_, v_inst_5902_, v_inst_5903_, v_cctx_5904_, v_ngen_5905_, v_env_5906_, v_act_5907_, v_constantsPerTask_5908_);
return v___x_5909_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0(void){
_start:
{
lean_object* v___x_5910_; lean_object* v___x_5911_; lean_object* v___x_5912_; 
v___x_5910_ = lean_box(0);
v___x_5911_ = lean_unsigned_to_nat(16u);
v___x_5912_ = lean_mk_array(v___x_5911_, v___x_5910_);
return v___x_5912_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1(void){
_start:
{
lean_object* v___x_5913_; lean_object* v___x_5914_; lean_object* v___x_5915_; 
v___x_5913_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0, &l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0);
v___x_5914_ = lean_unsigned_to_nat(0u);
v___x_5915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5915_, 0, v___x_5914_);
lean_ctor_set(v___x_5915_, 1, v___x_5913_);
return v___x_5915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createTreeCtx(lean_object* v_ctx_5916_){
_start:
{
lean_object* v_toCold_5917_; lean_object* v_ref_5918_; lean_object* v___x_5920_; uint8_t v_isShared_5921_; uint8_t v_isSharedCheck_5952_; 
v_toCold_5917_ = lean_ctor_get(v_ctx_5916_, 0);
v_ref_5918_ = lean_ctor_get(v_ctx_5916_, 2);
v_isSharedCheck_5952_ = !lean_is_exclusive(v_ctx_5916_);
if (v_isSharedCheck_5952_ == 0)
{
lean_object* v_unused_5953_; 
v_unused_5953_ = lean_ctor_get(v_ctx_5916_, 1);
lean_dec(v_unused_5953_);
v___x_5920_ = v_ctx_5916_;
v_isShared_5921_ = v_isSharedCheck_5952_;
goto v_resetjp_5919_;
}
else
{
lean_inc(v_ref_5918_);
lean_inc(v_toCold_5917_);
lean_dec(v_ctx_5916_);
v___x_5920_ = lean_box(0);
v_isShared_5921_ = v_isSharedCheck_5952_;
goto v_resetjp_5919_;
}
v_resetjp_5919_:
{
lean_object* v_fileName_5922_; lean_object* v_fileMap_5923_; lean_object* v_options_5924_; lean_object* v_maxRecDepth_5925_; lean_object* v___x_5927_; uint8_t v_isShared_5928_; uint8_t v_isSharedCheck_5943_; 
v_fileName_5922_ = lean_ctor_get(v_toCold_5917_, 0);
v_fileMap_5923_ = lean_ctor_get(v_toCold_5917_, 1);
v_options_5924_ = lean_ctor_get(v_toCold_5917_, 2);
v_maxRecDepth_5925_ = lean_ctor_get(v_toCold_5917_, 3);
v_isSharedCheck_5943_ = !lean_is_exclusive(v_toCold_5917_);
if (v_isSharedCheck_5943_ == 0)
{
lean_object* v_unused_5944_; lean_object* v_unused_5945_; lean_object* v_unused_5946_; lean_object* v_unused_5947_; lean_object* v_unused_5948_; lean_object* v_unused_5949_; lean_object* v_unused_5950_; lean_object* v_unused_5951_; 
v_unused_5944_ = lean_ctor_get(v_toCold_5917_, 11);
lean_dec(v_unused_5944_);
v_unused_5945_ = lean_ctor_get(v_toCold_5917_, 10);
lean_dec(v_unused_5945_);
v_unused_5946_ = lean_ctor_get(v_toCold_5917_, 9);
lean_dec(v_unused_5946_);
v_unused_5947_ = lean_ctor_get(v_toCold_5917_, 8);
lean_dec(v_unused_5947_);
v_unused_5948_ = lean_ctor_get(v_toCold_5917_, 7);
lean_dec(v_unused_5948_);
v_unused_5949_ = lean_ctor_get(v_toCold_5917_, 6);
lean_dec(v_unused_5949_);
v_unused_5950_ = lean_ctor_get(v_toCold_5917_, 5);
lean_dec(v_unused_5950_);
v_unused_5951_ = lean_ctor_get(v_toCold_5917_, 4);
lean_dec(v_unused_5951_);
v___x_5927_ = v_toCold_5917_;
v_isShared_5928_ = v_isSharedCheck_5943_;
goto v_resetjp_5926_;
}
else
{
lean_inc(v_maxRecDepth_5925_);
lean_inc(v_options_5924_);
lean_inc(v_fileMap_5923_);
lean_inc(v_fileName_5922_);
lean_dec(v_toCold_5917_);
v___x_5927_ = lean_box(0);
v_isShared_5928_ = v_isSharedCheck_5943_;
goto v_resetjp_5926_;
}
v_resetjp_5926_:
{
lean_object* v___x_5929_; lean_object* v___x_5930_; lean_object* v___x_5931_; lean_object* v___x_5932_; lean_object* v___x_5933_; lean_object* v___x_5934_; lean_object* v___x_5936_; 
v___x_5929_ = lean_box(0);
v___x_5930_ = lean_box(0);
v___x_5931_ = lean_unsigned_to_nat(0u);
v___x_5932_ = l_Lean_firstFrontendMacroScope;
v___x_5933_ = lean_box(0);
v___x_5934_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1, &l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1);
lean_inc_ref(v_options_5924_);
if (v_isShared_5928_ == 0)
{
lean_ctor_set(v___x_5927_, 11, v___x_5934_);
lean_ctor_set(v___x_5927_, 10, v___x_5933_);
lean_ctor_set(v___x_5927_, 9, v___x_5932_);
lean_ctor_set(v___x_5927_, 8, v___x_5929_);
lean_ctor_set(v___x_5927_, 7, v___x_5931_);
lean_ctor_set(v___x_5927_, 6, v___x_5931_);
lean_ctor_set(v___x_5927_, 5, v___x_5930_);
lean_ctor_set(v___x_5927_, 4, v___x_5929_);
v___x_5936_ = v___x_5927_;
goto v_reusejp_5935_;
}
else
{
lean_object* v_reuseFailAlloc_5942_; 
v_reuseFailAlloc_5942_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_5942_, 0, v_fileName_5922_);
lean_ctor_set(v_reuseFailAlloc_5942_, 1, v_fileMap_5923_);
lean_ctor_set(v_reuseFailAlloc_5942_, 2, v_options_5924_);
lean_ctor_set(v_reuseFailAlloc_5942_, 3, v_maxRecDepth_5925_);
lean_ctor_set(v_reuseFailAlloc_5942_, 4, v___x_5929_);
lean_ctor_set(v_reuseFailAlloc_5942_, 5, v___x_5930_);
lean_ctor_set(v_reuseFailAlloc_5942_, 6, v___x_5931_);
lean_ctor_set(v_reuseFailAlloc_5942_, 7, v___x_5931_);
lean_ctor_set(v_reuseFailAlloc_5942_, 8, v___x_5929_);
lean_ctor_set(v_reuseFailAlloc_5942_, 9, v___x_5932_);
lean_ctor_set(v_reuseFailAlloc_5942_, 10, v___x_5933_);
lean_ctor_set(v_reuseFailAlloc_5942_, 11, v___x_5934_);
v___x_5936_ = v_reuseFailAlloc_5942_;
goto v_reusejp_5935_;
}
v_reusejp_5935_:
{
uint16_t v___x_5937_; uint8_t v___x_5938_; lean_object* v___x_5940_; 
v___x_5937_ = l_Lean_OptionFlags_ofOptions(v_options_5924_);
lean_dec_ref(v_options_5924_);
v___x_5938_ = 0;
if (v_isShared_5921_ == 0)
{
lean_ctor_set(v___x_5920_, 1, v___x_5931_);
lean_ctor_set(v___x_5920_, 0, v___x_5936_);
v___x_5940_ = v___x_5920_;
goto v_reusejp_5939_;
}
else
{
lean_object* v_reuseFailAlloc_5941_; 
v_reuseFailAlloc_5941_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v_reuseFailAlloc_5941_, 0, v___x_5936_);
lean_ctor_set(v_reuseFailAlloc_5941_, 1, v___x_5931_);
lean_ctor_set(v_reuseFailAlloc_5941_, 2, v_ref_5918_);
v___x_5940_ = v_reuseFailAlloc_5941_;
goto v_reusejp_5939_;
}
v_reusejp_5939_:
{
lean_ctor_set_uint16(v___x_5940_, sizeof(void*)*3, v___x_5937_);
lean_ctor_set_uint8(v___x_5940_, sizeof(void*)*3 + 2, v___x_5938_);
lean_ctor_set_uint8(v___x_5940_, sizeof(void*)*3 + 3, v___x_5938_);
return v___x_5940_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(lean_object* v_category_5954_, lean_object* v_opts_5955_, lean_object* v_act_5956_, lean_object* v_decl_5957_, lean_object* v___y_5958_, lean_object* v___y_5959_, lean_object* v___y_5960_, lean_object* v___y_5961_){
_start:
{
lean_object* v___x_5963_; lean_object* v___x_5964_; 
lean_inc(v___y_5961_);
lean_inc_ref(v___y_5960_);
lean_inc(v___y_5959_);
lean_inc_ref(v___y_5958_);
v___x_5963_ = lean_apply_4(v_act_5956_, v___y_5958_, v___y_5959_, v___y_5960_, v___y_5961_);
v___x_5964_ = l_Lean_profileitIOUnsafe___redArg(v_category_5954_, v_opts_5955_, v___x_5963_, v_decl_5957_);
return v___x_5964_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg___boxed(lean_object* v_category_5965_, lean_object* v_opts_5966_, lean_object* v_act_5967_, lean_object* v_decl_5968_, lean_object* v___y_5969_, lean_object* v___y_5970_, lean_object* v___y_5971_, lean_object* v___y_5972_, lean_object* v___y_5973_){
_start:
{
lean_object* v_res_5974_; 
v_res_5974_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v_category_5965_, v_opts_5966_, v_act_5967_, v_decl_5968_, v___y_5969_, v___y_5970_, v___y_5971_, v___y_5972_);
lean_dec(v___y_5972_);
lean_dec_ref(v___y_5971_);
lean_dec(v___y_5970_);
lean_dec_ref(v___y_5969_);
lean_dec_ref(v_opts_5966_);
lean_dec_ref(v_category_5965_);
return v_res_5974_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1(lean_object* v_00_u03b1_5975_, lean_object* v_category_5976_, lean_object* v_opts_5977_, lean_object* v_act_5978_, lean_object* v_decl_5979_, lean_object* v___y_5980_, lean_object* v___y_5981_, lean_object* v___y_5982_, lean_object* v___y_5983_){
_start:
{
lean_object* v___x_5985_; 
v___x_5985_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v_category_5976_, v_opts_5977_, v_act_5978_, v_decl_5979_, v___y_5980_, v___y_5981_, v___y_5982_, v___y_5983_);
return v___x_5985_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___boxed(lean_object* v_00_u03b1_5986_, lean_object* v_category_5987_, lean_object* v_opts_5988_, lean_object* v_act_5989_, lean_object* v_decl_5990_, lean_object* v___y_5991_, lean_object* v___y_5992_, lean_object* v___y_5993_, lean_object* v___y_5994_, lean_object* v___y_5995_){
_start:
{
lean_object* v_res_5996_; 
v_res_5996_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1(v_00_u03b1_5986_, v_category_5987_, v_opts_5988_, v_act_5989_, v_decl_5990_, v___y_5991_, v___y_5992_, v___y_5993_, v___y_5994_);
lean_dec(v___y_5994_);
lean_dec_ref(v___y_5993_);
lean_dec(v___y_5992_);
lean_dec_ref(v___y_5991_);
lean_dec_ref(v_opts_5988_);
lean_dec_ref(v_category_5987_);
return v_res_5996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(lean_object* v_cctx_5997_, lean_object* v_env_5998_, lean_object* v_act_5999_, lean_object* v_constantsPerTask_6000_, lean_object* v_n_6001_, lean_object* v_ngen_6002_, lean_object* v_tasks_6003_, lean_object* v_start_6004_, lean_object* v_cnt_6005_, lean_object* v_idx_6006_){
_start:
{
lean_object* v___x_6008_; lean_object* v_moduleData_6009_; lean_object* v___x_6010_; uint8_t v___x_6011_; 
v___x_6008_ = l_Lean_Environment_header(v_env_5998_);
v_moduleData_6009_ = lean_ctor_get(v___x_6008_, 7);
lean_inc_ref(v_moduleData_6009_);
lean_dec_ref(v___x_6008_);
v___x_6010_ = lean_array_get_size(v_moduleData_6009_);
v___x_6011_ = lean_nat_dec_lt(v_idx_6006_, v___x_6010_);
if (v___x_6011_ == 0)
{
uint8_t v___x_6012_; 
lean_dec_ref(v_moduleData_6009_);
lean_dec(v_idx_6006_);
lean_dec(v_cnt_6005_);
v___x_6012_ = lean_nat_dec_lt(v_start_6004_, v_n_6001_);
if (v___x_6012_ == 0)
{
lean_object* v___x_6013_; 
lean_dec(v_start_6004_);
lean_dec_ref(v_ngen_6002_);
lean_dec(v_n_6001_);
lean_dec_ref(v_act_5999_);
lean_dec_ref(v_env_5998_);
lean_dec_ref(v_cctx_5997_);
v___x_6013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6013_, 0, v_tasks_6003_);
return v___x_6013_;
}
else
{
lean_object* v_namePrefix_6014_; lean_object* v_idx_6015_; lean_object* v___x_6017_; uint8_t v_isShared_6018_; uint8_t v_isSharedCheck_6029_; 
v_namePrefix_6014_ = lean_ctor_get(v_ngen_6002_, 0);
v_idx_6015_ = lean_ctor_get(v_ngen_6002_, 1);
v_isSharedCheck_6029_ = !lean_is_exclusive(v_ngen_6002_);
if (v_isSharedCheck_6029_ == 0)
{
v___x_6017_ = v_ngen_6002_;
v_isShared_6018_ = v_isSharedCheck_6029_;
goto v_resetjp_6016_;
}
else
{
lean_inc(v_idx_6015_);
lean_inc(v_namePrefix_6014_);
lean_dec(v_ngen_6002_);
v___x_6017_ = lean_box(0);
v_isShared_6018_ = v_isSharedCheck_6029_;
goto v_resetjp_6016_;
}
v_resetjp_6016_:
{
lean_object* v___x_6019_; lean_object* v___x_6020_; lean_object* v___x_6022_; 
v___x_6019_ = l_Lean_Name_num___override(v_namePrefix_6014_, v_idx_6015_);
v___x_6020_ = lean_unsigned_to_nat(1u);
if (v_isShared_6018_ == 0)
{
lean_ctor_set(v___x_6017_, 1, v___x_6020_);
lean_ctor_set(v___x_6017_, 0, v___x_6019_);
v___x_6022_ = v___x_6017_;
goto v_reusejp_6021_;
}
else
{
lean_object* v_reuseFailAlloc_6028_; 
v_reuseFailAlloc_6028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6028_, 0, v___x_6019_);
lean_ctor_set(v_reuseFailAlloc_6028_, 1, v___x_6020_);
v___x_6022_ = v_reuseFailAlloc_6028_;
goto v_reusejp_6021_;
}
v_reusejp_6021_:
{
lean_object* v___x_6023_; lean_object* v___x_6024_; lean_object* v___x_6025_; lean_object* v___x_6026_; lean_object* v___x_6027_; 
v___x_6023_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_6023_, 0, lean_box(0));
lean_closure_set(v___x_6023_, 1, v_cctx_5997_);
lean_closure_set(v___x_6023_, 2, v___x_6022_);
lean_closure_set(v___x_6023_, 3, v_env_5998_);
lean_closure_set(v___x_6023_, 4, v_act_5999_);
lean_closure_set(v___x_6023_, 5, v_start_6004_);
lean_closure_set(v___x_6023_, 6, v_n_6001_);
v___x_6024_ = lean_unsigned_to_nat(0u);
v___x_6025_ = lean_io_as_task(v___x_6023_, v___x_6024_);
v___x_6026_ = lean_array_push(v_tasks_6003_, v___x_6025_);
v___x_6027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6027_, 0, v___x_6026_);
return v___x_6027_;
}
}
}
}
else
{
lean_object* v_mdata_6030_; lean_object* v_constants_6031_; lean_object* v___x_6032_; lean_object* v_cnt_6033_; uint8_t v___x_6034_; 
v_mdata_6030_ = lean_array_fget(v_moduleData_6009_, v_idx_6006_);
lean_dec_ref(v_moduleData_6009_);
v_constants_6031_ = lean_ctor_get(v_mdata_6030_, 2);
lean_inc_ref(v_constants_6031_);
lean_dec(v_mdata_6030_);
v___x_6032_ = lean_array_get_size(v_constants_6031_);
lean_dec_ref(v_constants_6031_);
v_cnt_6033_ = lean_nat_add(v_cnt_6005_, v___x_6032_);
lean_dec(v_cnt_6005_);
v___x_6034_ = lean_nat_dec_lt(v_constantsPerTask_6000_, v_cnt_6033_);
if (v___x_6034_ == 0)
{
lean_object* v___x_6035_; lean_object* v___x_6036_; 
v___x_6035_ = lean_unsigned_to_nat(1u);
v___x_6036_ = lean_nat_add(v_idx_6006_, v___x_6035_);
lean_dec(v_idx_6006_);
v_cnt_6005_ = v_cnt_6033_;
v_idx_6006_ = v___x_6036_;
goto _start;
}
else
{
lean_object* v_namePrefix_6038_; lean_object* v_idx_6039_; lean_object* v___x_6041_; uint8_t v_isShared_6042_; uint8_t v_isSharedCheck_6056_; 
lean_dec(v_cnt_6033_);
v_namePrefix_6038_ = lean_ctor_get(v_ngen_6002_, 0);
v_idx_6039_ = lean_ctor_get(v_ngen_6002_, 1);
v_isSharedCheck_6056_ = !lean_is_exclusive(v_ngen_6002_);
if (v_isSharedCheck_6056_ == 0)
{
v___x_6041_ = v_ngen_6002_;
v_isShared_6042_ = v_isSharedCheck_6056_;
goto v_resetjp_6040_;
}
else
{
lean_inc(v_idx_6039_);
lean_inc(v_namePrefix_6038_);
lean_dec(v_ngen_6002_);
v___x_6041_ = lean_box(0);
v_isShared_6042_ = v_isSharedCheck_6056_;
goto v_resetjp_6040_;
}
v_resetjp_6040_:
{
lean_object* v___x_6043_; lean_object* v___x_6044_; lean_object* v___x_6046_; 
lean_inc(v_idx_6039_);
lean_inc(v_namePrefix_6038_);
v___x_6043_ = l_Lean_Name_num___override(v_namePrefix_6038_, v_idx_6039_);
v___x_6044_ = lean_unsigned_to_nat(1u);
if (v_isShared_6042_ == 0)
{
lean_ctor_set(v___x_6041_, 1, v___x_6044_);
lean_ctor_set(v___x_6041_, 0, v___x_6043_);
v___x_6046_ = v___x_6041_;
goto v_reusejp_6045_;
}
else
{
lean_object* v_reuseFailAlloc_6055_; 
v_reuseFailAlloc_6055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6055_, 0, v___x_6043_);
lean_ctor_set(v_reuseFailAlloc_6055_, 1, v___x_6044_);
v___x_6046_ = v_reuseFailAlloc_6055_;
goto v_reusejp_6045_;
}
v_reusejp_6045_:
{
lean_object* v___x_6047_; lean_object* v___x_6048_; lean_object* v___x_6049_; lean_object* v___x_6050_; lean_object* v___x_6051_; lean_object* v___x_6052_; lean_object* v___x_6053_; 
v___x_6047_ = lean_nat_add(v_idx_6039_, v___x_6044_);
lean_dec(v_idx_6039_);
v___x_6048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6048_, 0, v_namePrefix_6038_);
lean_ctor_set(v___x_6048_, 1, v___x_6047_);
v___x_6049_ = lean_nat_add(v_idx_6006_, v___x_6044_);
lean_dec(v_idx_6006_);
lean_inc_n(v___x_6049_, 2);
lean_inc_ref(v_act_5999_);
lean_inc_ref(v_env_5998_);
lean_inc_ref(v_cctx_5997_);
v___x_6050_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_6050_, 0, lean_box(0));
lean_closure_set(v___x_6050_, 1, v_cctx_5997_);
lean_closure_set(v___x_6050_, 2, v___x_6046_);
lean_closure_set(v___x_6050_, 3, v_env_5998_);
lean_closure_set(v___x_6050_, 4, v_act_5999_);
lean_closure_set(v___x_6050_, 5, v_start_6004_);
lean_closure_set(v___x_6050_, 6, v___x_6049_);
v___x_6051_ = lean_unsigned_to_nat(0u);
v___x_6052_ = lean_io_as_task(v___x_6050_, v___x_6051_);
v___x_6053_ = lean_array_push(v_tasks_6003_, v___x_6052_);
v_ngen_6002_ = v___x_6048_;
v_tasks_6003_ = v___x_6053_;
v_start_6004_ = v___x_6049_;
v_cnt_6005_ = v___x_6051_;
v_idx_6006_ = v___x_6049_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg___boxed(lean_object* v_cctx_6057_, lean_object* v_env_6058_, lean_object* v_act_6059_, lean_object* v_constantsPerTask_6060_, lean_object* v_n_6061_, lean_object* v_ngen_6062_, lean_object* v_tasks_6063_, lean_object* v_start_6064_, lean_object* v_cnt_6065_, lean_object* v_idx_6066_, lean_object* v___y_6067_){
_start:
{
lean_object* v_res_6068_; 
v_res_6068_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(v_cctx_6057_, v_env_6058_, v_act_6059_, v_constantsPerTask_6060_, v_n_6061_, v_ngen_6062_, v_tasks_6063_, v_start_6064_, v_cnt_6065_, v_idx_6066_);
lean_dec(v_constantsPerTask_6060_);
return v_res_6068_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0(uint8_t v_suppressElabErrors_6077_, lean_object* v_x_6078_){
_start:
{
if (lean_obj_tag(v_x_6078_) == 1)
{
lean_object* v_pre_6079_; 
v_pre_6079_ = lean_ctor_get(v_x_6078_, 0);
switch(lean_obj_tag(v_pre_6079_))
{
case 1:
{
lean_object* v_pre_6080_; 
v_pre_6080_ = lean_ctor_get(v_pre_6079_, 0);
switch(lean_obj_tag(v_pre_6080_))
{
case 0:
{
lean_object* v_str_6081_; lean_object* v_str_6082_; lean_object* v___x_6083_; uint8_t v___x_6084_; 
v_str_6081_ = lean_ctor_get(v_x_6078_, 1);
v_str_6082_ = lean_ctor_get(v_pre_6079_, 1);
v___x_6083_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__0));
v___x_6084_ = lean_string_dec_eq(v_str_6082_, v___x_6083_);
if (v___x_6084_ == 0)
{
lean_object* v___x_6085_; uint8_t v___x_6086_; 
v___x_6085_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__1));
v___x_6086_ = lean_string_dec_eq(v_str_6082_, v___x_6085_);
if (v___x_6086_ == 0)
{
return v___x_6086_;
}
else
{
lean_object* v___x_6087_; uint8_t v___x_6088_; 
v___x_6087_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__2));
v___x_6088_ = lean_string_dec_eq(v_str_6081_, v___x_6087_);
if (v___x_6088_ == 0)
{
return v___x_6088_;
}
else
{
return v_suppressElabErrors_6077_;
}
}
}
else
{
lean_object* v___x_6089_; uint8_t v___x_6090_; 
v___x_6089_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__3));
v___x_6090_ = lean_string_dec_eq(v_str_6081_, v___x_6089_);
if (v___x_6090_ == 0)
{
return v___x_6090_;
}
else
{
return v_suppressElabErrors_6077_;
}
}
}
case 1:
{
lean_object* v_pre_6091_; 
v_pre_6091_ = lean_ctor_get(v_pre_6080_, 0);
if (lean_obj_tag(v_pre_6091_) == 0)
{
lean_object* v_str_6092_; lean_object* v_str_6093_; lean_object* v_str_6094_; lean_object* v___x_6095_; uint8_t v___x_6096_; 
v_str_6092_ = lean_ctor_get(v_x_6078_, 1);
v_str_6093_ = lean_ctor_get(v_pre_6079_, 1);
v_str_6094_ = lean_ctor_get(v_pre_6080_, 1);
v___x_6095_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__4));
v___x_6096_ = lean_string_dec_eq(v_str_6094_, v___x_6095_);
if (v___x_6096_ == 0)
{
return v___x_6096_;
}
else
{
lean_object* v___x_6097_; uint8_t v___x_6098_; 
v___x_6097_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__5));
v___x_6098_ = lean_string_dec_eq(v_str_6093_, v___x_6097_);
if (v___x_6098_ == 0)
{
return v___x_6098_;
}
else
{
lean_object* v___x_6099_; uint8_t v___x_6100_; 
v___x_6099_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__6));
v___x_6100_ = lean_string_dec_eq(v_str_6092_, v___x_6099_);
if (v___x_6100_ == 0)
{
return v___x_6100_;
}
else
{
return v_suppressElabErrors_6077_;
}
}
}
}
else
{
uint8_t v___x_6101_; 
v___x_6101_ = 0;
return v___x_6101_;
}
}
default: 
{
uint8_t v___x_6102_; 
v___x_6102_ = 0;
return v___x_6102_;
}
}
}
case 0:
{
lean_object* v_str_6103_; lean_object* v___x_6104_; uint8_t v___x_6105_; 
v_str_6103_ = lean_ctor_get(v_x_6078_, 1);
v___x_6104_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__7));
v___x_6105_ = lean_string_dec_eq(v_str_6103_, v___x_6104_);
if (v___x_6105_ == 0)
{
return v___x_6105_;
}
else
{
return v_suppressElabErrors_6077_;
}
}
default: 
{
uint8_t v___x_6106_; 
v___x_6106_ = 0;
return v___x_6106_;
}
}
}
else
{
uint8_t v___x_6107_; 
v___x_6107_ = 0;
return v___x_6107_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___boxed(lean_object* v_suppressElabErrors_6108_, lean_object* v_x_6109_){
_start:
{
uint8_t v_suppressElabErrors_boxed_6110_; uint8_t v_res_6111_; lean_object* v_r_6112_; 
v_suppressElabErrors_boxed_6110_ = lean_unbox(v_suppressElabErrors_6108_);
v_res_6111_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0(v_suppressElabErrors_boxed_6110_, v_x_6109_);
lean_dec(v_x_6109_);
v_r_6112_ = lean_box(v_res_6111_);
return v_r_6112_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7_spec__9(lean_object* v_opts_6113_, lean_object* v_opt_6114_){
_start:
{
lean_object* v_name_6115_; lean_object* v_defValue_6116_; lean_object* v_map_6117_; lean_object* v___x_6118_; 
v_name_6115_ = lean_ctor_get(v_opt_6114_, 0);
v_defValue_6116_ = lean_ctor_get(v_opt_6114_, 1);
v_map_6117_ = lean_ctor_get(v_opts_6113_, 0);
v___x_6118_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_6117_, v_name_6115_);
if (lean_obj_tag(v___x_6118_) == 0)
{
uint8_t v___x_6119_; 
v___x_6119_ = lean_unbox(v_defValue_6116_);
return v___x_6119_;
}
else
{
lean_object* v_val_6120_; 
v_val_6120_ = lean_ctor_get(v___x_6118_, 0);
lean_inc(v_val_6120_);
lean_dec_ref_known(v___x_6118_, 1);
if (lean_obj_tag(v_val_6120_) == 1)
{
uint8_t v_v_6121_; 
v_v_6121_ = lean_ctor_get_uint8(v_val_6120_, 0);
lean_dec_ref_known(v_val_6120_, 0);
return v_v_6121_;
}
else
{
uint8_t v___x_6122_; 
lean_dec(v_val_6120_);
v___x_6122_ = lean_unbox(v_defValue_6116_);
return v___x_6122_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7_spec__9___boxed(lean_object* v_opts_6123_, lean_object* v_opt_6124_){
_start:
{
uint8_t v_res_6125_; lean_object* v_r_6126_; 
v_res_6125_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7_spec__9(v_opts_6123_, v_opt_6124_);
lean_dec_ref(v_opt_6124_);
lean_dec_ref(v_opts_6123_);
v_r_6126_ = lean_box(v_res_6125_);
return v_r_6126_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7(lean_object* v_ref_6128_, lean_object* v_msgData_6129_, uint8_t v_severity_6130_, uint8_t v_isSilent_6131_, lean_object* v___y_6132_, lean_object* v___y_6133_, lean_object* v___y_6134_, lean_object* v___y_6135_){
_start:
{
lean_object* v___y_6138_; lean_object* v___y_6139_; uint8_t v___y_6140_; lean_object* v___y_6141_; lean_object* v___y_6142_; lean_object* v___y_6143_; uint8_t v___y_6144_; lean_object* v_toCold_6145_; lean_object* v___y_6146_; lean_object* v___y_6175_; lean_object* v___y_6176_; uint8_t v___y_6177_; uint8_t v___y_6178_; lean_object* v___y_6179_; uint8_t v___y_6180_; lean_object* v___y_6181_; lean_object* v___y_6182_; lean_object* v___y_6202_; uint8_t v___y_6203_; lean_object* v___y_6204_; lean_object* v___y_6205_; uint8_t v___y_6206_; uint8_t v___y_6207_; lean_object* v___y_6208_; uint8_t v___y_6212_; uint8_t v___y_6213_; uint8_t v___x_6223_; uint8_t v___y_6225_; uint8_t v___x_6231_; 
v___x_6223_ = 2;
v___x_6231_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6130_, v___x_6223_);
if (v___x_6231_ == 0)
{
v___y_6225_ = v___x_6231_;
goto v___jp_6224_;
}
else
{
uint8_t v___x_6232_; 
lean_inc_ref(v_msgData_6129_);
v___x_6232_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_6129_);
if (v___x_6232_ == 0)
{
v___y_6225_ = v___x_6232_;
goto v___jp_6224_;
}
else
{
lean_object* v___x_6233_; lean_object* v___x_6234_; 
lean_dec_ref(v_msgData_6129_);
v___x_6233_ = lean_box(0);
v___x_6234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6234_, 0, v___x_6233_);
return v___x_6234_;
}
}
v___jp_6137_:
{
lean_object* v_currNamespace_6147_; lean_object* v_openDecls_6148_; lean_object* v___x_6149_; lean_object* v___x_6150_; lean_object* v___x_6151_; lean_object* v___x_6152_; lean_object* v_env_6153_; lean_object* v_nextMacroScope_6154_; lean_object* v_ngen_6155_; lean_object* v_auxDeclNGen_6156_; lean_object* v_traceState_6157_; lean_object* v_cache_6158_; lean_object* v_recordedDeps_6159_; lean_object* v_messages_6160_; lean_object* v_infoState_6161_; lean_object* v_snapshotTasks_6162_; lean_object* v___x_6164_; uint8_t v_isShared_6165_; uint8_t v_isSharedCheck_6173_; 
v_currNamespace_6147_ = lean_ctor_get(v_toCold_6145_, 4);
v_openDecls_6148_ = lean_ctor_get(v_toCold_6145_, 5);
lean_inc(v_openDecls_6148_);
lean_inc(v_currNamespace_6147_);
v___x_6149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6149_, 0, v_currNamespace_6147_);
lean_ctor_set(v___x_6149_, 1, v_openDecls_6148_);
v___x_6150_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6150_, 0, v___x_6149_);
lean_ctor_set(v___x_6150_, 1, v___y_6139_);
lean_inc_ref(v___y_6143_);
lean_inc_ref(v___y_6138_);
v___x_6151_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_6151_, 0, v___y_6138_);
lean_ctor_set(v___x_6151_, 1, v___y_6141_);
lean_ctor_set(v___x_6151_, 2, v___y_6142_);
lean_ctor_set(v___x_6151_, 3, v___y_6143_);
lean_ctor_set(v___x_6151_, 4, v___x_6150_);
lean_ctor_set_uint8(v___x_6151_, sizeof(void*)*5, v___y_6140_);
lean_ctor_set_uint8(v___x_6151_, sizeof(void*)*5 + 1, v___y_6144_);
lean_ctor_set_uint8(v___x_6151_, sizeof(void*)*5 + 2, v_isSilent_6131_);
v___x_6152_ = lean_st_ref_take(v___y_6146_);
v_env_6153_ = lean_ctor_get(v___x_6152_, 0);
v_nextMacroScope_6154_ = lean_ctor_get(v___x_6152_, 1);
v_ngen_6155_ = lean_ctor_get(v___x_6152_, 2);
v_auxDeclNGen_6156_ = lean_ctor_get(v___x_6152_, 3);
v_traceState_6157_ = lean_ctor_get(v___x_6152_, 4);
v_cache_6158_ = lean_ctor_get(v___x_6152_, 5);
v_recordedDeps_6159_ = lean_ctor_get(v___x_6152_, 6);
v_messages_6160_ = lean_ctor_get(v___x_6152_, 7);
v_infoState_6161_ = lean_ctor_get(v___x_6152_, 8);
v_snapshotTasks_6162_ = lean_ctor_get(v___x_6152_, 9);
v_isSharedCheck_6173_ = !lean_is_exclusive(v___x_6152_);
if (v_isSharedCheck_6173_ == 0)
{
v___x_6164_ = v___x_6152_;
v_isShared_6165_ = v_isSharedCheck_6173_;
goto v_resetjp_6163_;
}
else
{
lean_inc(v_snapshotTasks_6162_);
lean_inc(v_infoState_6161_);
lean_inc(v_messages_6160_);
lean_inc(v_recordedDeps_6159_);
lean_inc(v_cache_6158_);
lean_inc(v_traceState_6157_);
lean_inc(v_auxDeclNGen_6156_);
lean_inc(v_ngen_6155_);
lean_inc(v_nextMacroScope_6154_);
lean_inc(v_env_6153_);
lean_dec(v___x_6152_);
v___x_6164_ = lean_box(0);
v_isShared_6165_ = v_isSharedCheck_6173_;
goto v_resetjp_6163_;
}
v_resetjp_6163_:
{
lean_object* v___x_6166_; lean_object* v___x_6167_; lean_object* v___x_6169_; 
v___x_6166_ = lean_box(0);
v___x_6167_ = l_Lean_MessageLog_add(v___x_6151_, v_messages_6160_);
if (v_isShared_6165_ == 0)
{
lean_ctor_set(v___x_6164_, 7, v___x_6167_);
v___x_6169_ = v___x_6164_;
goto v_reusejp_6168_;
}
else
{
lean_object* v_reuseFailAlloc_6172_; 
v_reuseFailAlloc_6172_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6172_, 0, v_env_6153_);
lean_ctor_set(v_reuseFailAlloc_6172_, 1, v_nextMacroScope_6154_);
lean_ctor_set(v_reuseFailAlloc_6172_, 2, v_ngen_6155_);
lean_ctor_set(v_reuseFailAlloc_6172_, 3, v_auxDeclNGen_6156_);
lean_ctor_set(v_reuseFailAlloc_6172_, 4, v_traceState_6157_);
lean_ctor_set(v_reuseFailAlloc_6172_, 5, v_cache_6158_);
lean_ctor_set(v_reuseFailAlloc_6172_, 6, v_recordedDeps_6159_);
lean_ctor_set(v_reuseFailAlloc_6172_, 7, v___x_6167_);
lean_ctor_set(v_reuseFailAlloc_6172_, 8, v_infoState_6161_);
lean_ctor_set(v_reuseFailAlloc_6172_, 9, v_snapshotTasks_6162_);
v___x_6169_ = v_reuseFailAlloc_6172_;
goto v_reusejp_6168_;
}
v_reusejp_6168_:
{
lean_object* v___x_6170_; lean_object* v___x_6171_; 
v___x_6170_ = lean_st_ref_put(v___y_6146_, v___x_6169_);
v___x_6171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6171_, 0, v___x_6166_);
return v___x_6171_;
}
}
}
v___jp_6174_:
{
lean_object* v_fileName_6183_; lean_object* v_fileMap_6184_; lean_object* v___x_6185_; lean_object* v___x_6186_; lean_object* v_a_6187_; lean_object* v___x_6189_; uint8_t v_isShared_6190_; uint8_t v_isSharedCheck_6200_; 
v_fileName_6183_ = lean_ctor_get(v___y_6181_, 0);
v_fileMap_6184_ = lean_ctor_get(v___y_6181_, 1);
v___x_6185_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_6129_);
v___x_6186_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(v___x_6185_, v___y_6132_, v___y_6133_, v___y_6134_, v___y_6135_);
v_a_6187_ = lean_ctor_get(v___x_6186_, 0);
v_isSharedCheck_6200_ = !lean_is_exclusive(v___x_6186_);
if (v_isSharedCheck_6200_ == 0)
{
v___x_6189_ = v___x_6186_;
v_isShared_6190_ = v_isSharedCheck_6200_;
goto v_resetjp_6188_;
}
else
{
lean_inc(v_a_6187_);
lean_dec(v___x_6186_);
v___x_6189_ = lean_box(0);
v_isShared_6190_ = v_isSharedCheck_6200_;
goto v_resetjp_6188_;
}
v_resetjp_6188_:
{
lean_object* v___x_6191_; lean_object* v___x_6192_; lean_object* v___x_6193_; lean_object* v___x_6194_; 
lean_inc_ref_n(v_fileMap_6184_, 2);
v___x_6191_ = l_Lean_FileMap_toPosition(v_fileMap_6184_, v___y_6179_);
lean_dec(v___y_6179_);
v___x_6192_ = l_Lean_FileMap_toPosition(v_fileMap_6184_, v___y_6182_);
lean_dec(v___y_6182_);
v___x_6193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6193_, 0, v___x_6192_);
v___x_6194_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___closed__0));
if (v___y_6178_ == 0)
{
lean_del_object(v___x_6189_);
lean_dec_ref(v___y_6175_);
v___y_6138_ = v_fileName_6183_;
v___y_6139_ = v_a_6187_;
v___y_6140_ = v___y_6177_;
v___y_6141_ = v___x_6191_;
v___y_6142_ = v___x_6193_;
v___y_6143_ = v___x_6194_;
v___y_6144_ = v___y_6180_;
v_toCold_6145_ = v___y_6176_;
v___y_6146_ = v___y_6135_;
goto v___jp_6137_;
}
else
{
uint8_t v___x_6195_; 
lean_inc(v_a_6187_);
v___x_6195_ = l_Lean_MessageData_hasTag(v___y_6175_, v_a_6187_);
if (v___x_6195_ == 0)
{
lean_object* v___x_6196_; lean_object* v___x_6198_; 
lean_dec_ref_known(v___x_6193_, 1);
lean_dec_ref(v___x_6191_);
lean_dec(v_a_6187_);
v___x_6196_ = lean_box(0);
if (v_isShared_6190_ == 0)
{
lean_ctor_set(v___x_6189_, 0, v___x_6196_);
v___x_6198_ = v___x_6189_;
goto v_reusejp_6197_;
}
else
{
lean_object* v_reuseFailAlloc_6199_; 
v_reuseFailAlloc_6199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6199_, 0, v___x_6196_);
v___x_6198_ = v_reuseFailAlloc_6199_;
goto v_reusejp_6197_;
}
v_reusejp_6197_:
{
return v___x_6198_;
}
}
else
{
lean_del_object(v___x_6189_);
v___y_6138_ = v_fileName_6183_;
v___y_6139_ = v_a_6187_;
v___y_6140_ = v___y_6177_;
v___y_6141_ = v___x_6191_;
v___y_6142_ = v___x_6193_;
v___y_6143_ = v___x_6194_;
v___y_6144_ = v___y_6180_;
v_toCold_6145_ = v___y_6176_;
v___y_6146_ = v___y_6135_;
goto v___jp_6137_;
}
}
}
}
v___jp_6201_:
{
lean_object* v___x_6209_; 
v___x_6209_ = l_Lean_Syntax_getTailPos_x3f(v___y_6205_, v___y_6206_);
lean_dec(v___y_6205_);
if (lean_obj_tag(v___x_6209_) == 0)
{
lean_inc(v___y_6208_);
v___y_6175_ = v___y_6202_;
v___y_6176_ = v___y_6204_;
v___y_6177_ = v___y_6206_;
v___y_6178_ = v___y_6203_;
v___y_6179_ = v___y_6208_;
v___y_6180_ = v___y_6207_;
v___y_6181_ = v___y_6204_;
v___y_6182_ = v___y_6208_;
goto v___jp_6174_;
}
else
{
lean_object* v_val_6210_; 
v_val_6210_ = lean_ctor_get(v___x_6209_, 0);
lean_inc(v_val_6210_);
lean_dec_ref_known(v___x_6209_, 1);
v___y_6175_ = v___y_6202_;
v___y_6176_ = v___y_6204_;
v___y_6177_ = v___y_6206_;
v___y_6178_ = v___y_6203_;
v___y_6179_ = v___y_6208_;
v___y_6180_ = v___y_6207_;
v___y_6181_ = v___y_6204_;
v___y_6182_ = v_val_6210_;
goto v___jp_6174_;
}
}
v___jp_6211_:
{
lean_object* v_toCold_6214_; lean_object* v_ref_6215_; uint8_t v_suppressElabErrors_6216_; lean_object* v___x_6217_; lean_object* v___f_6218_; lean_object* v_ref_6219_; lean_object* v___x_6220_; 
v_toCold_6214_ = lean_ctor_get(v___y_6134_, 0);
v_ref_6215_ = lean_ctor_get(v___y_6134_, 2);
v_suppressElabErrors_6216_ = lean_ctor_get_uint8(v___y_6134_, sizeof(void*)*3 + 2);
v___x_6217_ = lean_box(v_suppressElabErrors_6216_);
v___f_6218_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___boxed), 2, 1);
lean_closure_set(v___f_6218_, 0, v___x_6217_);
v_ref_6219_ = l_Lean_replaceRef(v_ref_6128_, v_ref_6215_);
v___x_6220_ = l_Lean_Syntax_getPos_x3f(v_ref_6219_, v___y_6212_);
if (lean_obj_tag(v___x_6220_) == 0)
{
lean_object* v___x_6221_; 
v___x_6221_ = lean_unsigned_to_nat(0u);
v___y_6202_ = v___f_6218_;
v___y_6203_ = v_suppressElabErrors_6216_;
v___y_6204_ = v_toCold_6214_;
v___y_6205_ = v_ref_6219_;
v___y_6206_ = v___y_6212_;
v___y_6207_ = v___y_6213_;
v___y_6208_ = v___x_6221_;
goto v___jp_6201_;
}
else
{
lean_object* v_val_6222_; 
v_val_6222_ = lean_ctor_get(v___x_6220_, 0);
lean_inc(v_val_6222_);
lean_dec_ref_known(v___x_6220_, 1);
v___y_6202_ = v___f_6218_;
v___y_6203_ = v_suppressElabErrors_6216_;
v___y_6204_ = v_toCold_6214_;
v___y_6205_ = v_ref_6219_;
v___y_6206_ = v___y_6212_;
v___y_6207_ = v___y_6213_;
v___y_6208_ = v_val_6222_;
goto v___jp_6201_;
}
}
v___jp_6224_:
{
uint8_t v___x_6226_; uint8_t v___x_6227_; 
v___x_6226_ = 1;
v___x_6227_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6130_, v___x_6226_);
if (v___x_6227_ == 0)
{
v___y_6212_ = v___y_6225_;
v___y_6213_ = v_severity_6130_;
goto v___jp_6211_;
}
else
{
lean_object* v___x_6228_; lean_object* v___x_6229_; uint8_t v___x_6230_; 
v___x_6228_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_6134_);
v___x_6229_ = l_Lean_warningAsError;
v___x_6230_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7_spec__9(v___x_6228_, v___x_6229_);
lean_dec_ref(v___x_6228_);
if (v___x_6230_ == 0)
{
v___y_6212_ = v___y_6225_;
v___y_6213_ = v_severity_6130_;
goto v___jp_6211_;
}
else
{
v___y_6212_ = v___y_6225_;
v___y_6213_ = v___x_6223_;
goto v___jp_6211_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___boxed(lean_object* v_ref_6235_, lean_object* v_msgData_6236_, lean_object* v_severity_6237_, lean_object* v_isSilent_6238_, lean_object* v___y_6239_, lean_object* v___y_6240_, lean_object* v___y_6241_, lean_object* v___y_6242_, lean_object* v___y_6243_){
_start:
{
uint8_t v_severity_boxed_6244_; uint8_t v_isSilent_boxed_6245_; lean_object* v_res_6246_; 
v_severity_boxed_6244_ = lean_unbox(v_severity_6237_);
v_isSilent_boxed_6245_ = lean_unbox(v_isSilent_6238_);
v_res_6246_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7(v_ref_6235_, v_msgData_6236_, v_severity_boxed_6244_, v_isSilent_boxed_6245_, v___y_6239_, v___y_6240_, v___y_6241_, v___y_6242_);
lean_dec(v___y_6242_);
lean_dec_ref(v___y_6241_);
lean_dec(v___y_6240_);
lean_dec_ref(v___y_6239_);
lean_dec(v_ref_6235_);
return v_res_6246_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3(lean_object* v_msgData_6247_, uint8_t v_severity_6248_, uint8_t v_isSilent_6249_, lean_object* v___y_6250_, lean_object* v___y_6251_, lean_object* v___y_6252_, lean_object* v___y_6253_){
_start:
{
lean_object* v_ref_6255_; lean_object* v___x_6256_; 
v_ref_6255_ = lean_ctor_get(v___y_6252_, 2);
v___x_6256_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7(v_ref_6255_, v_msgData_6247_, v_severity_6248_, v_isSilent_6249_, v___y_6250_, v___y_6251_, v___y_6252_, v___y_6253_);
return v___x_6256_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_msgData_6257_, lean_object* v_severity_6258_, lean_object* v_isSilent_6259_, lean_object* v___y_6260_, lean_object* v___y_6261_, lean_object* v___y_6262_, lean_object* v___y_6263_, lean_object* v___y_6264_){
_start:
{
uint8_t v_severity_boxed_6265_; uint8_t v_isSilent_boxed_6266_; lean_object* v_res_6267_; 
v_severity_boxed_6265_ = lean_unbox(v_severity_6258_);
v_isSilent_boxed_6266_ = lean_unbox(v_isSilent_6259_);
v_res_6267_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3(v_msgData_6257_, v_severity_boxed_6265_, v_isSilent_boxed_6266_, v___y_6260_, v___y_6261_, v___y_6262_, v___y_6263_);
lean_dec(v___y_6263_);
lean_dec_ref(v___y_6262_);
lean_dec(v___y_6261_);
lean_dec_ref(v___y_6260_);
return v_res_6267_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2(lean_object* v_msgData_6268_, lean_object* v___y_6269_, lean_object* v___y_6270_, lean_object* v___y_6271_, lean_object* v___y_6272_){
_start:
{
uint8_t v___x_6274_; uint8_t v___x_6275_; lean_object* v___x_6276_; 
v___x_6274_ = 2;
v___x_6275_ = 0;
v___x_6276_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3(v_msgData_6268_, v___x_6274_, v___x_6275_, v___y_6269_, v___y_6270_, v___y_6271_, v___y_6272_);
return v___x_6276_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_6277_, lean_object* v___y_6278_, lean_object* v___y_6279_, lean_object* v___y_6280_, lean_object* v___y_6281_, lean_object* v___y_6282_){
_start:
{
lean_object* v_res_6283_; 
v_res_6283_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2(v_msgData_6277_, v___y_6278_, v___y_6279_, v___y_6280_, v___y_6281_);
lean_dec(v___y_6281_);
lean_dec_ref(v___y_6280_);
lean_dec(v___y_6279_);
lean_dec_ref(v___y_6278_);
return v_res_6283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0(lean_object* v_f_6284_, lean_object* v___y_6285_, lean_object* v___y_6286_, lean_object* v___y_6287_, lean_object* v___y_6288_){
_start:
{
lean_object* v_module_6290_; lean_object* v_const_6291_; lean_object* v_exception_6292_; lean_object* v___x_6293_; lean_object* v___x_6294_; lean_object* v___x_6295_; lean_object* v___x_6296_; lean_object* v___x_6297_; lean_object* v___x_6298_; lean_object* v___x_6299_; lean_object* v___x_6300_; lean_object* v___x_6301_; lean_object* v___x_6302_; lean_object* v___x_6303_; lean_object* v___x_6304_; 
v_module_6290_ = lean_ctor_get(v_f_6284_, 0);
lean_inc(v_module_6290_);
v_const_6291_ = lean_ctor_get(v_f_6284_, 1);
lean_inc(v_const_6291_);
v_exception_6292_ = lean_ctor_get(v_f_6284_, 2);
lean_inc_ref(v_exception_6292_);
lean_dec_ref(v_f_6284_);
v___x_6293_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1);
v___x_6294_ = l_Lean_MessageData_ofName(v_const_6291_);
v___x_6295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6295_, 0, v___x_6293_);
lean_ctor_set(v___x_6295_, 1, v___x_6294_);
v___x_6296_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3);
v___x_6297_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6297_, 0, v___x_6295_);
lean_ctor_set(v___x_6297_, 1, v___x_6296_);
v___x_6298_ = l_Lean_MessageData_ofName(v_module_6290_);
v___x_6299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6299_, 0, v___x_6297_);
lean_ctor_set(v___x_6299_, 1, v___x_6298_);
v___x_6300_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5);
v___x_6301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6301_, 0, v___x_6299_);
lean_ctor_set(v___x_6301_, 1, v___x_6300_);
v___x_6302_ = l_Lean_Exception_toMessageData(v_exception_6292_);
v___x_6303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6303_, 0, v___x_6301_);
lean_ctor_set(v___x_6303_, 1, v___x_6302_);
v___x_6304_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2(v___x_6303_, v___y_6285_, v___y_6286_, v___y_6287_, v___y_6288_);
return v___x_6304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0___boxed(lean_object* v_f_6305_, lean_object* v___y_6306_, lean_object* v___y_6307_, lean_object* v___y_6308_, lean_object* v___y_6309_, lean_object* v___y_6310_){
_start:
{
lean_object* v_res_6311_; 
v_res_6311_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0(v_f_6305_, v___y_6306_, v___y_6307_, v___y_6308_, v___y_6309_);
lean_dec(v___y_6309_);
lean_dec_ref(v___y_6308_);
lean_dec(v___y_6307_);
lean_dec_ref(v___y_6306_);
return v_res_6311_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3(lean_object* v_as_6312_, size_t v_i_6313_, size_t v_stop_6314_, lean_object* v_b_6315_, lean_object* v___y_6316_, lean_object* v___y_6317_, lean_object* v___y_6318_, lean_object* v___y_6319_){
_start:
{
uint8_t v___x_6321_; 
v___x_6321_ = lean_usize_dec_eq(v_i_6313_, v_stop_6314_);
if (v___x_6321_ == 0)
{
lean_object* v___x_6322_; lean_object* v___x_6323_; 
v___x_6322_ = lean_array_uget_borrowed(v_as_6312_, v_i_6313_);
lean_inc(v___x_6322_);
v___x_6323_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0(v___x_6322_, v___y_6316_, v___y_6317_, v___y_6318_, v___y_6319_);
if (lean_obj_tag(v___x_6323_) == 0)
{
lean_object* v_a_6324_; size_t v___x_6325_; size_t v___x_6326_; 
v_a_6324_ = lean_ctor_get(v___x_6323_, 0);
lean_inc(v_a_6324_);
lean_dec_ref_known(v___x_6323_, 1);
v___x_6325_ = ((size_t)1ULL);
v___x_6326_ = lean_usize_add(v_i_6313_, v___x_6325_);
v_i_6313_ = v___x_6326_;
v_b_6315_ = v_a_6324_;
goto _start;
}
else
{
return v___x_6323_;
}
}
else
{
lean_object* v___x_6328_; 
v___x_6328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6328_, 0, v_b_6315_);
return v___x_6328_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3___boxed(lean_object* v_as_6329_, lean_object* v_i_6330_, lean_object* v_stop_6331_, lean_object* v_b_6332_, lean_object* v___y_6333_, lean_object* v___y_6334_, lean_object* v___y_6335_, lean_object* v___y_6336_, lean_object* v___y_6337_){
_start:
{
size_t v_i_boxed_6338_; size_t v_stop_boxed_6339_; lean_object* v_res_6340_; 
v_i_boxed_6338_ = lean_unbox_usize(v_i_6330_);
lean_dec(v_i_6330_);
v_stop_boxed_6339_ = lean_unbox_usize(v_stop_6331_);
lean_dec(v_stop_6331_);
v_res_6340_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3(v_as_6329_, v_i_boxed_6338_, v_stop_boxed_6339_, v_b_6332_, v___y_6333_, v___y_6334_, v___y_6335_, v___y_6336_);
lean_dec(v___y_6336_);
lean_dec_ref(v___y_6335_);
lean_dec(v___y_6334_);
lean_dec_ref(v___y_6333_);
lean_dec_ref(v_as_6329_);
return v_res_6340_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(lean_object* v_as_6341_, size_t v_i_6342_, size_t v_stop_6343_, lean_object* v_b_6344_){
_start:
{
uint8_t v___x_6345_; 
v___x_6345_ = lean_usize_dec_eq(v_i_6342_, v_stop_6343_);
if (v___x_6345_ == 0)
{
lean_object* v___x_6346_; lean_object* v___x_6347_; lean_object* v___x_6348_; size_t v___x_6349_; size_t v___x_6350_; 
v___x_6346_ = lean_array_uget_borrowed(v_as_6341_, v_i_6342_);
lean_inc(v___x_6346_);
v___x_6347_ = lean_task_get_own(v___x_6346_);
v___x_6348_ = l_Lean_Meta_LazyDiscrTree_InitResults_append___redArg(v_b_6344_, v___x_6347_);
v___x_6349_ = ((size_t)1ULL);
v___x_6350_ = lean_usize_add(v_i_6342_, v___x_6349_);
v_i_6342_ = v___x_6350_;
v_b_6344_ = v___x_6348_;
goto _start;
}
else
{
return v_b_6344_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_as_6352_, lean_object* v_i_6353_, lean_object* v_stop_6354_, lean_object* v_b_6355_){
_start:
{
size_t v_i_boxed_6356_; size_t v_stop_boxed_6357_; lean_object* v_res_6358_; 
v_i_boxed_6356_ = lean_unbox_usize(v_i_6353_);
lean_dec(v_i_6353_);
v_stop_boxed_6357_ = lean_unbox_usize(v_stop_6354_);
lean_dec(v_stop_6354_);
v_res_6358_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(v_as_6352_, v_i_boxed_6356_, v_stop_boxed_6357_, v_b_6355_);
lean_dec_ref(v_as_6352_);
return v_res_6358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(lean_object* v_z_6359_, lean_object* v_tasks_6360_){
_start:
{
lean_object* v___x_6361_; lean_object* v___x_6362_; uint8_t v___x_6363_; 
v___x_6361_ = lean_unsigned_to_nat(0u);
v___x_6362_ = lean_array_get_size(v_tasks_6360_);
v___x_6363_ = lean_nat_dec_lt(v___x_6361_, v___x_6362_);
if (v___x_6363_ == 0)
{
return v_z_6359_;
}
else
{
size_t v___x_6364_; size_t v___x_6365_; lean_object* v___x_6366_; 
v___x_6364_ = ((size_t)0ULL);
v___x_6365_ = lean_usize_of_nat(v___x_6362_);
v___x_6366_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(v_tasks_6360_, v___x_6364_, v___x_6365_, v_z_6359_);
return v___x_6366_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg___boxed(lean_object* v_z_6367_, lean_object* v_tasks_6368_){
_start:
{
lean_object* v_res_6369_; 
v_res_6369_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(v_z_6367_, v_tasks_6368_);
lean_dec_ref(v_tasks_6368_);
return v_res_6369_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_6370_; lean_object* v___x_6371_; lean_object* v___x_6372_; 
v___x_6370_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
v___x_6371_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___redArg___closed__2);
v___x_6372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6372_, 0, v___x_6371_);
lean_ctor_set(v___x_6372_, 1, v___x_6370_);
return v___x_6372_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_6373_; lean_object* v___x_6374_; lean_object* v___x_6375_; 
v___x_6373_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
v___x_6374_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0);
v___x_6375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6375_, 0, v___x_6374_);
lean_ctor_set(v___x_6375_, 1, v___x_6373_);
return v___x_6375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(lean_object* v_cctx_6376_, lean_object* v_ngen_6377_, lean_object* v_env_6378_, lean_object* v_act_6379_, lean_object* v_constantsPerTask_6380_, lean_object* v___y_6381_, lean_object* v___y_6382_, lean_object* v___y_6383_, lean_object* v___y_6384_){
_start:
{
lean_object* v___x_6386_; lean_object* v_moduleData_6387_; lean_object* v_n_6388_; lean_object* v___x_6389_; lean_object* v___x_6390_; lean_object* v___x_6391_; lean_object* v_a_6392_; lean_object* v___x_6394_; uint8_t v_isShared_6395_; uint8_t v_isSharedCheck_6427_; 
v___x_6386_ = l_Lean_Environment_header(v_env_6378_);
v_moduleData_6387_ = lean_ctor_get(v___x_6386_, 7);
lean_inc_ref(v_moduleData_6387_);
lean_dec_ref(v___x_6386_);
v_n_6388_ = lean_array_get_size(v_moduleData_6387_);
lean_dec_ref(v_moduleData_6387_);
v___x_6389_ = lean_unsigned_to_nat(0u);
v___x_6390_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
v___x_6391_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(v_cctx_6376_, v_env_6378_, v_act_6379_, v_constantsPerTask_6380_, v_n_6388_, v_ngen_6377_, v___x_6390_, v___x_6389_, v___x_6389_, v___x_6389_);
v_a_6392_ = lean_ctor_get(v___x_6391_, 0);
v_isSharedCheck_6427_ = !lean_is_exclusive(v___x_6391_);
if (v_isSharedCheck_6427_ == 0)
{
v___x_6394_ = v___x_6391_;
v_isShared_6395_ = v_isSharedCheck_6427_;
goto v_resetjp_6393_;
}
else
{
lean_inc(v_a_6392_);
lean_dec(v___x_6391_);
v___x_6394_ = lean_box(0);
v_isShared_6395_ = v_isSharedCheck_6427_;
goto v_resetjp_6393_;
}
v_resetjp_6393_:
{
lean_object* v___x_6396_; lean_object* v_r_6397_; lean_object* v_tree_6398_; lean_object* v_errors_6399_; lean_object* v___x_6400_; uint8_t v___x_6401_; 
v___x_6396_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1);
v_r_6397_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(v___x_6396_, v_a_6392_);
lean_dec(v_a_6392_);
v_tree_6398_ = lean_ctor_get(v_r_6397_, 0);
lean_inc_ref(v_tree_6398_);
v_errors_6399_ = lean_ctor_get(v_r_6397_, 1);
lean_inc_ref(v_errors_6399_);
lean_dec_ref(v_r_6397_);
v___x_6400_ = lean_array_get_size(v_errors_6399_);
v___x_6401_ = lean_nat_dec_lt(v___x_6389_, v___x_6400_);
if (v___x_6401_ == 0)
{
lean_object* v___x_6402_; lean_object* v___x_6404_; 
lean_dec_ref(v_errors_6399_);
v___x_6402_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_tree_6398_);
if (v_isShared_6395_ == 0)
{
lean_ctor_set(v___x_6394_, 0, v___x_6402_);
v___x_6404_ = v___x_6394_;
goto v_reusejp_6403_;
}
else
{
lean_object* v_reuseFailAlloc_6405_; 
v_reuseFailAlloc_6405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6405_, 0, v___x_6402_);
v___x_6404_ = v_reuseFailAlloc_6405_;
goto v_reusejp_6403_;
}
v_reusejp_6403_:
{
return v___x_6404_;
}
}
else
{
lean_object* v___x_6406_; size_t v___x_6407_; size_t v___x_6408_; lean_object* v___x_6409_; 
lean_del_object(v___x_6394_);
v___x_6406_ = lean_box(0);
v___x_6407_ = ((size_t)0ULL);
v___x_6408_ = lean_usize_of_nat(v___x_6400_);
v___x_6409_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3(v_errors_6399_, v___x_6407_, v___x_6408_, v___x_6406_, v___y_6381_, v___y_6382_, v___y_6383_, v___y_6384_);
lean_dec_ref(v_errors_6399_);
if (lean_obj_tag(v___x_6409_) == 0)
{
lean_object* v___x_6411_; uint8_t v_isShared_6412_; uint8_t v_isSharedCheck_6417_; 
v_isSharedCheck_6417_ = !lean_is_exclusive(v___x_6409_);
if (v_isSharedCheck_6417_ == 0)
{
lean_object* v_unused_6418_; 
v_unused_6418_ = lean_ctor_get(v___x_6409_, 0);
lean_dec(v_unused_6418_);
v___x_6411_ = v___x_6409_;
v_isShared_6412_ = v_isSharedCheck_6417_;
goto v_resetjp_6410_;
}
else
{
lean_dec(v___x_6409_);
v___x_6411_ = lean_box(0);
v_isShared_6412_ = v_isSharedCheck_6417_;
goto v_resetjp_6410_;
}
v_resetjp_6410_:
{
lean_object* v___x_6413_; lean_object* v___x_6415_; 
v___x_6413_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_tree_6398_);
if (v_isShared_6412_ == 0)
{
lean_ctor_set(v___x_6411_, 0, v___x_6413_);
v___x_6415_ = v___x_6411_;
goto v_reusejp_6414_;
}
else
{
lean_object* v_reuseFailAlloc_6416_; 
v_reuseFailAlloc_6416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6416_, 0, v___x_6413_);
v___x_6415_ = v_reuseFailAlloc_6416_;
goto v_reusejp_6414_;
}
v_reusejp_6414_:
{
return v___x_6415_;
}
}
}
else
{
lean_object* v_a_6419_; lean_object* v___x_6421_; uint8_t v_isShared_6422_; uint8_t v_isSharedCheck_6426_; 
lean_dec_ref(v_tree_6398_);
v_a_6419_ = lean_ctor_get(v___x_6409_, 0);
v_isSharedCheck_6426_ = !lean_is_exclusive(v___x_6409_);
if (v_isSharedCheck_6426_ == 0)
{
v___x_6421_ = v___x_6409_;
v_isShared_6422_ = v_isSharedCheck_6426_;
goto v_resetjp_6420_;
}
else
{
lean_inc(v_a_6419_);
lean_dec(v___x_6409_);
v___x_6421_ = lean_box(0);
v_isShared_6422_ = v_isSharedCheck_6426_;
goto v_resetjp_6420_;
}
v_resetjp_6420_:
{
lean_object* v___x_6424_; 
if (v_isShared_6422_ == 0)
{
v___x_6424_ = v___x_6421_;
goto v_reusejp_6423_;
}
else
{
lean_object* v_reuseFailAlloc_6425_; 
v_reuseFailAlloc_6425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6425_, 0, v_a_6419_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___boxed(lean_object* v_cctx_6428_, lean_object* v_ngen_6429_, lean_object* v_env_6430_, lean_object* v_act_6431_, lean_object* v_constantsPerTask_6432_, lean_object* v___y_6433_, lean_object* v___y_6434_, lean_object* v___y_6435_, lean_object* v___y_6436_, lean_object* v___y_6437_){
_start:
{
lean_object* v_res_6438_; 
v_res_6438_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(v_cctx_6428_, v_ngen_6429_, v_env_6430_, v_act_6431_, v_constantsPerTask_6432_, v___y_6433_, v___y_6434_, v___y_6435_, v___y_6436_);
lean_dec(v___y_6436_);
lean_dec_ref(v___y_6435_);
lean_dec(v___y_6434_);
lean_dec_ref(v___y_6433_);
lean_dec(v_constantsPerTask_6432_);
return v_res_6438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0(lean_object* v_a_6439_, lean_object* v___x_6440_, lean_object* v_addEntry_6441_, lean_object* v_constantsPerTask_6442_, lean_object* v_droppedEntriesRef_6443_, lean_object* v_droppedKeys_6444_, lean_object* v___y_6445_, lean_object* v___y_6446_, lean_object* v___y_6447_, lean_object* v___y_6448_){
_start:
{
lean_object* v___x_6450_; lean_object* v_env_6451_; lean_object* v___x_6452_; lean_object* v___x_6453_; 
v___x_6450_ = lean_st_ref_get(v___y_6448_);
v_env_6451_ = lean_ctor_get(v___x_6450_, 0);
lean_inc_ref(v_env_6451_);
lean_dec(v___x_6450_);
lean_inc_ref(v_a_6439_);
v___x_6452_ = l_Lean_Meta_LazyDiscrTree_createTreeCtx(v_a_6439_);
v___x_6453_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(v___x_6452_, v___x_6440_, v_env_6451_, v_addEntry_6441_, v_constantsPerTask_6442_, v___y_6445_, v___y_6446_, v___y_6447_, v___y_6448_);
if (lean_obj_tag(v___x_6453_) == 0)
{
if (lean_obj_tag(v_droppedEntriesRef_6443_) == 1)
{
lean_object* v_a_6454_; lean_object* v_val_6455_; lean_object* v___x_6457_; uint8_t v_isShared_6458_; uint8_t v_isSharedCheck_6488_; 
v_a_6454_ = lean_ctor_get(v___x_6453_, 0);
lean_inc(v_a_6454_);
lean_dec_ref_known(v___x_6453_, 1);
v_val_6455_ = lean_ctor_get(v_droppedEntriesRef_6443_, 0);
v_isSharedCheck_6488_ = !lean_is_exclusive(v_droppedEntriesRef_6443_);
if (v_isSharedCheck_6488_ == 0)
{
v___x_6457_ = v_droppedEntriesRef_6443_;
v_isShared_6458_ = v_isSharedCheck_6488_;
goto v_resetjp_6456_;
}
else
{
lean_inc(v_val_6455_);
lean_dec(v_droppedEntriesRef_6443_);
v___x_6457_ = lean_box(0);
v_isShared_6458_ = v_isSharedCheck_6488_;
goto v_resetjp_6456_;
}
v_resetjp_6456_:
{
lean_object* v___x_6459_; 
v___x_6459_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_a_6454_, v_droppedKeys_6444_, v___y_6445_, v___y_6446_, v___y_6447_, v___y_6448_);
lean_dec(v_droppedKeys_6444_);
if (lean_obj_tag(v___x_6459_) == 0)
{
lean_object* v_a_6460_; lean_object* v___x_6462_; uint8_t v_isShared_6463_; uint8_t v_isSharedCheck_6479_; 
v_a_6460_ = lean_ctor_get(v___x_6459_, 0);
v_isSharedCheck_6479_ = !lean_is_exclusive(v___x_6459_);
if (v_isSharedCheck_6479_ == 0)
{
v___x_6462_ = v___x_6459_;
v_isShared_6463_ = v_isSharedCheck_6479_;
goto v_resetjp_6461_;
}
else
{
lean_inc(v_a_6460_);
lean_dec(v___x_6459_);
v___x_6462_ = lean_box(0);
v_isShared_6463_ = v_isSharedCheck_6479_;
goto v_resetjp_6461_;
}
v_resetjp_6461_:
{
lean_object* v_fst_6464_; lean_object* v_snd_6465_; lean_object* v___x_6466_; lean_object* v___y_6468_; 
v_fst_6464_ = lean_ctor_get(v_a_6460_, 0);
lean_inc(v_fst_6464_);
v_snd_6465_ = lean_ctor_get(v_a_6460_, 1);
lean_inc(v_snd_6465_);
lean_dec(v_a_6460_);
v___x_6466_ = lean_st_ref_get(v_val_6455_);
if (lean_obj_tag(v___x_6466_) == 0)
{
lean_object* v___x_6477_; 
v___x_6477_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___y_6468_ = v___x_6477_;
goto v___jp_6467_;
}
else
{
lean_object* v_val_6478_; 
v_val_6478_ = lean_ctor_get(v___x_6466_, 0);
lean_inc(v_val_6478_);
lean_dec_ref_known(v___x_6466_, 1);
v___y_6468_ = v_val_6478_;
goto v___jp_6467_;
}
v___jp_6467_:
{
lean_object* v___x_6469_; lean_object* v___x_6471_; 
v___x_6469_ = l_Array_append___redArg(v___y_6468_, v_fst_6464_);
lean_dec(v_fst_6464_);
if (v_isShared_6458_ == 0)
{
lean_ctor_set(v___x_6457_, 0, v___x_6469_);
v___x_6471_ = v___x_6457_;
goto v_reusejp_6470_;
}
else
{
lean_object* v_reuseFailAlloc_6476_; 
v_reuseFailAlloc_6476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6476_, 0, v___x_6469_);
v___x_6471_ = v_reuseFailAlloc_6476_;
goto v_reusejp_6470_;
}
v_reusejp_6470_:
{
lean_object* v___x_6472_; lean_object* v___x_6474_; 
v___x_6472_ = lean_st_ref_swap(v_val_6455_, v___x_6471_);
lean_dec(v_val_6455_);
lean_dec(v___x_6472_);
if (v_isShared_6463_ == 0)
{
lean_ctor_set(v___x_6462_, 0, v_snd_6465_);
v___x_6474_ = v___x_6462_;
goto v_reusejp_6473_;
}
else
{
lean_object* v_reuseFailAlloc_6475_; 
v_reuseFailAlloc_6475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6475_, 0, v_snd_6465_);
v___x_6474_ = v_reuseFailAlloc_6475_;
goto v_reusejp_6473_;
}
v_reusejp_6473_:
{
return v___x_6474_;
}
}
}
}
}
else
{
lean_object* v_a_6480_; lean_object* v___x_6482_; uint8_t v_isShared_6483_; uint8_t v_isSharedCheck_6487_; 
lean_del_object(v___x_6457_);
lean_dec(v_val_6455_);
v_a_6480_ = lean_ctor_get(v___x_6459_, 0);
v_isSharedCheck_6487_ = !lean_is_exclusive(v___x_6459_);
if (v_isSharedCheck_6487_ == 0)
{
v___x_6482_ = v___x_6459_;
v_isShared_6483_ = v_isSharedCheck_6487_;
goto v_resetjp_6481_;
}
else
{
lean_inc(v_a_6480_);
lean_dec(v___x_6459_);
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
}
else
{
lean_object* v_a_6489_; lean_object* v___x_6490_; 
lean_dec(v_droppedEntriesRef_6443_);
v_a_6489_ = lean_ctor_get(v___x_6453_, 0);
lean_inc(v_a_6489_);
lean_dec_ref_known(v___x_6453_, 1);
v___x_6490_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_a_6489_, v_droppedKeys_6444_, v___y_6445_, v___y_6446_, v___y_6447_, v___y_6448_);
return v___x_6490_;
}
}
else
{
lean_dec(v_droppedKeys_6444_);
lean_dec(v_droppedEntriesRef_6443_);
return v___x_6453_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0___boxed(lean_object* v_a_6491_, lean_object* v___x_6492_, lean_object* v_addEntry_6493_, lean_object* v_constantsPerTask_6494_, lean_object* v_droppedEntriesRef_6495_, lean_object* v_droppedKeys_6496_, lean_object* v___y_6497_, lean_object* v___y_6498_, lean_object* v___y_6499_, lean_object* v___y_6500_, lean_object* v___y_6501_){
_start:
{
lean_object* v_res_6502_; 
v_res_6502_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0(v_a_6491_, v___x_6492_, v_addEntry_6493_, v_constantsPerTask_6494_, v_droppedEntriesRef_6495_, v_droppedKeys_6496_, v___y_6497_, v___y_6498_, v___y_6499_, v___y_6500_);
lean_dec(v___y_6500_);
lean_dec_ref(v___y_6499_);
lean_dec(v___y_6498_);
lean_dec_ref(v___y_6497_);
lean_dec(v_constantsPerTask_6494_);
lean_dec_ref(v_a_6491_);
return v_res_6502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(lean_object* v_ref_6504_, lean_object* v_addEntry_6505_, lean_object* v_droppedKeys_6506_, lean_object* v_constantsPerTask_6507_, lean_object* v_droppedEntriesRef_6508_, lean_object* v_ty_6509_, lean_object* v_a_6510_, lean_object* v_a_6511_, lean_object* v_a_6512_, lean_object* v_a_6513_){
_start:
{
lean_object* v_a_6516_; lean_object* v___x_6538_; lean_object* v_ngen_6539_; lean_object* v_namePrefix_6540_; lean_object* v_idx_6541_; lean_object* v___x_6543_; uint8_t v_isShared_6544_; uint8_t v_isSharedCheck_6587_; 
v___x_6538_ = lean_st_ref_get(v_a_6513_);
v_ngen_6539_ = lean_ctor_get(v___x_6538_, 2);
lean_inc_ref(v_ngen_6539_);
lean_dec(v___x_6538_);
v_namePrefix_6540_ = lean_ctor_get(v_ngen_6539_, 0);
v_idx_6541_ = lean_ctor_get(v_ngen_6539_, 1);
v_isSharedCheck_6587_ = !lean_is_exclusive(v_ngen_6539_);
if (v_isSharedCheck_6587_ == 0)
{
v___x_6543_ = v_ngen_6539_;
v_isShared_6544_ = v_isSharedCheck_6587_;
goto v_resetjp_6542_;
}
else
{
lean_inc(v_idx_6541_);
lean_inc(v_namePrefix_6540_);
lean_dec(v_ngen_6539_);
v___x_6543_ = lean_box(0);
v_isShared_6544_ = v_isSharedCheck_6587_;
goto v_resetjp_6542_;
}
v___jp_6515_:
{
lean_object* v___x_6517_; 
v___x_6517_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v_a_6516_, v_ty_6509_, v_a_6510_, v_a_6511_, v_a_6512_, v_a_6513_);
if (lean_obj_tag(v___x_6517_) == 0)
{
lean_object* v_a_6518_; lean_object* v___x_6520_; uint8_t v_isShared_6521_; uint8_t v_isSharedCheck_6529_; 
v_a_6518_ = lean_ctor_get(v___x_6517_, 0);
v_isSharedCheck_6529_ = !lean_is_exclusive(v___x_6517_);
if (v_isSharedCheck_6529_ == 0)
{
v___x_6520_ = v___x_6517_;
v_isShared_6521_ = v_isSharedCheck_6529_;
goto v_resetjp_6519_;
}
else
{
lean_inc(v_a_6518_);
lean_dec(v___x_6517_);
v___x_6520_ = lean_box(0);
v_isShared_6521_ = v_isSharedCheck_6529_;
goto v_resetjp_6519_;
}
v_resetjp_6519_:
{
lean_object* v_fst_6522_; lean_object* v_snd_6523_; lean_object* v___x_6524_; lean_object* v___x_6525_; lean_object* v___x_6527_; 
v_fst_6522_ = lean_ctor_get(v_a_6518_, 0);
lean_inc(v_fst_6522_);
v_snd_6523_ = lean_ctor_get(v_a_6518_, 1);
lean_inc(v_snd_6523_);
lean_dec(v_a_6518_);
v___x_6524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6524_, 0, v_snd_6523_);
v___x_6525_ = lean_st_ref_swap(v_ref_6504_, v___x_6524_);
lean_dec(v___x_6525_);
if (v_isShared_6521_ == 0)
{
lean_ctor_set(v___x_6520_, 0, v_fst_6522_);
v___x_6527_ = v___x_6520_;
goto v_reusejp_6526_;
}
else
{
lean_object* v_reuseFailAlloc_6528_; 
v_reuseFailAlloc_6528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6528_, 0, v_fst_6522_);
v___x_6527_ = v_reuseFailAlloc_6528_;
goto v_reusejp_6526_;
}
v_reusejp_6526_:
{
return v___x_6527_;
}
}
}
else
{
lean_object* v_a_6530_; lean_object* v___x_6532_; uint8_t v_isShared_6533_; uint8_t v_isSharedCheck_6537_; 
v_a_6530_ = lean_ctor_get(v___x_6517_, 0);
v_isSharedCheck_6537_ = !lean_is_exclusive(v___x_6517_);
if (v_isSharedCheck_6537_ == 0)
{
v___x_6532_ = v___x_6517_;
v_isShared_6533_ = v_isSharedCheck_6537_;
goto v_resetjp_6531_;
}
else
{
lean_inc(v_a_6530_);
lean_dec(v___x_6517_);
v___x_6532_ = lean_box(0);
v_isShared_6533_ = v_isSharedCheck_6537_;
goto v_resetjp_6531_;
}
v_resetjp_6531_:
{
lean_object* v___x_6535_; 
if (v_isShared_6533_ == 0)
{
v___x_6535_ = v___x_6532_;
goto v_reusejp_6534_;
}
else
{
lean_object* v_reuseFailAlloc_6536_; 
v_reuseFailAlloc_6536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6536_, 0, v_a_6530_);
v___x_6535_ = v_reuseFailAlloc_6536_;
goto v_reusejp_6534_;
}
v_reusejp_6534_:
{
return v___x_6535_;
}
}
}
}
v_resetjp_6542_:
{
lean_object* v___x_6545_; lean_object* v___x_6546_; lean_object* v___x_6548_; 
lean_inc(v_idx_6541_);
lean_inc(v_namePrefix_6540_);
v___x_6545_ = l_Lean_Name_num___override(v_namePrefix_6540_, v_idx_6541_);
v___x_6546_ = lean_unsigned_to_nat(1u);
if (v_isShared_6544_ == 0)
{
lean_ctor_set(v___x_6543_, 1, v___x_6546_);
lean_ctor_set(v___x_6543_, 0, v___x_6545_);
v___x_6548_ = v___x_6543_;
goto v_reusejp_6547_;
}
else
{
lean_object* v_reuseFailAlloc_6586_; 
v_reuseFailAlloc_6586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6586_, 0, v___x_6545_);
lean_ctor_set(v_reuseFailAlloc_6586_, 1, v___x_6546_);
v___x_6548_ = v_reuseFailAlloc_6586_;
goto v_reusejp_6547_;
}
v_reusejp_6547_:
{
lean_object* v___f_6549_; lean_object* v___x_6550_; lean_object* v___x_6551_; lean_object* v___x_6552_; lean_object* v_env_6553_; lean_object* v_nextMacroScope_6554_; lean_object* v_auxDeclNGen_6555_; lean_object* v_traceState_6556_; lean_object* v_cache_6557_; lean_object* v_recordedDeps_6558_; lean_object* v_messages_6559_; lean_object* v_infoState_6560_; lean_object* v_snapshotTasks_6561_; lean_object* v___x_6563_; uint8_t v_isShared_6564_; uint8_t v_isSharedCheck_6584_; 
lean_inc_ref(v_a_6512_);
v___f_6549_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_6549_, 0, v_a_6512_);
lean_closure_set(v___f_6549_, 1, v___x_6548_);
lean_closure_set(v___f_6549_, 2, v_addEntry_6505_);
lean_closure_set(v___f_6549_, 3, v_constantsPerTask_6507_);
lean_closure_set(v___f_6549_, 4, v_droppedEntriesRef_6508_);
lean_closure_set(v___f_6549_, 5, v_droppedKeys_6506_);
v___x_6550_ = lean_nat_add(v_idx_6541_, v___x_6546_);
lean_dec(v_idx_6541_);
v___x_6551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6551_, 0, v_namePrefix_6540_);
lean_ctor_set(v___x_6551_, 1, v___x_6550_);
v___x_6552_ = lean_st_ref_take(v_a_6513_);
v_env_6553_ = lean_ctor_get(v___x_6552_, 0);
v_nextMacroScope_6554_ = lean_ctor_get(v___x_6552_, 1);
v_auxDeclNGen_6555_ = lean_ctor_get(v___x_6552_, 3);
v_traceState_6556_ = lean_ctor_get(v___x_6552_, 4);
v_cache_6557_ = lean_ctor_get(v___x_6552_, 5);
v_recordedDeps_6558_ = lean_ctor_get(v___x_6552_, 6);
v_messages_6559_ = lean_ctor_get(v___x_6552_, 7);
v_infoState_6560_ = lean_ctor_get(v___x_6552_, 8);
v_snapshotTasks_6561_ = lean_ctor_get(v___x_6552_, 9);
v_isSharedCheck_6584_ = !lean_is_exclusive(v___x_6552_);
if (v_isSharedCheck_6584_ == 0)
{
lean_object* v_unused_6585_; 
v_unused_6585_ = lean_ctor_get(v___x_6552_, 2);
lean_dec(v_unused_6585_);
v___x_6563_ = v___x_6552_;
v_isShared_6564_ = v_isSharedCheck_6584_;
goto v_resetjp_6562_;
}
else
{
lean_inc(v_snapshotTasks_6561_);
lean_inc(v_infoState_6560_);
lean_inc(v_messages_6559_);
lean_inc(v_recordedDeps_6558_);
lean_inc(v_cache_6557_);
lean_inc(v_traceState_6556_);
lean_inc(v_auxDeclNGen_6555_);
lean_inc(v_nextMacroScope_6554_);
lean_inc(v_env_6553_);
lean_dec(v___x_6552_);
v___x_6563_ = lean_box(0);
v_isShared_6564_ = v_isSharedCheck_6584_;
goto v_resetjp_6562_;
}
v_resetjp_6562_:
{
lean_object* v___x_6566_; 
if (v_isShared_6564_ == 0)
{
lean_ctor_set(v___x_6563_, 2, v___x_6551_);
v___x_6566_ = v___x_6563_;
goto v_reusejp_6565_;
}
else
{
lean_object* v_reuseFailAlloc_6583_; 
v_reuseFailAlloc_6583_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6583_, 0, v_env_6553_);
lean_ctor_set(v_reuseFailAlloc_6583_, 1, v_nextMacroScope_6554_);
lean_ctor_set(v_reuseFailAlloc_6583_, 2, v___x_6551_);
lean_ctor_set(v_reuseFailAlloc_6583_, 3, v_auxDeclNGen_6555_);
lean_ctor_set(v_reuseFailAlloc_6583_, 4, v_traceState_6556_);
lean_ctor_set(v_reuseFailAlloc_6583_, 5, v_cache_6557_);
lean_ctor_set(v_reuseFailAlloc_6583_, 6, v_recordedDeps_6558_);
lean_ctor_set(v_reuseFailAlloc_6583_, 7, v_messages_6559_);
lean_ctor_set(v_reuseFailAlloc_6583_, 8, v_infoState_6560_);
lean_ctor_set(v_reuseFailAlloc_6583_, 9, v_snapshotTasks_6561_);
v___x_6566_ = v_reuseFailAlloc_6583_;
goto v_reusejp_6565_;
}
v_reusejp_6565_:
{
lean_object* v___x_6567_; lean_object* v___x_6568_; 
v___x_6567_ = lean_st_ref_put(v_a_6513_, v___x_6566_);
v___x_6568_ = lean_st_ref_get(v_ref_6504_);
if (lean_obj_tag(v___x_6568_) == 0)
{
lean_object* v___x_6569_; lean_object* v___x_6570_; lean_object* v___x_6571_; lean_object* v___x_6572_; 
v___x_6569_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_6512_);
v___x_6570_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___closed__0));
v___x_6571_ = lean_box(0);
v___x_6572_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v___x_6570_, v___x_6569_, v___f_6549_, v___x_6571_, v_a_6510_, v_a_6511_, v_a_6512_, v_a_6513_);
lean_dec_ref(v___x_6569_);
if (lean_obj_tag(v___x_6572_) == 0)
{
lean_object* v_a_6573_; 
v_a_6573_ = lean_ctor_get(v___x_6572_, 0);
lean_inc(v_a_6573_);
lean_dec_ref_known(v___x_6572_, 1);
v_a_6516_ = v_a_6573_;
goto v___jp_6515_;
}
else
{
lean_object* v_a_6574_; lean_object* v___x_6576_; uint8_t v_isShared_6577_; uint8_t v_isSharedCheck_6581_; 
lean_dec_ref(v_ty_6509_);
v_a_6574_ = lean_ctor_get(v___x_6572_, 0);
v_isSharedCheck_6581_ = !lean_is_exclusive(v___x_6572_);
if (v_isSharedCheck_6581_ == 0)
{
v___x_6576_ = v___x_6572_;
v_isShared_6577_ = v_isSharedCheck_6581_;
goto v_resetjp_6575_;
}
else
{
lean_inc(v_a_6574_);
lean_dec(v___x_6572_);
v___x_6576_ = lean_box(0);
v_isShared_6577_ = v_isSharedCheck_6581_;
goto v_resetjp_6575_;
}
v_resetjp_6575_:
{
lean_object* v___x_6579_; 
if (v_isShared_6577_ == 0)
{
v___x_6579_ = v___x_6576_;
goto v_reusejp_6578_;
}
else
{
lean_object* v_reuseFailAlloc_6580_; 
v_reuseFailAlloc_6580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6580_, 0, v_a_6574_);
v___x_6579_ = v_reuseFailAlloc_6580_;
goto v_reusejp_6578_;
}
v_reusejp_6578_:
{
return v___x_6579_;
}
}
}
}
else
{
lean_object* v_val_6582_; 
lean_dec_ref(v___f_6549_);
v_val_6582_ = lean_ctor_get(v___x_6568_, 0);
lean_inc(v_val_6582_);
lean_dec_ref_known(v___x_6568_, 1);
v_a_6516_ = v_val_6582_;
goto v___jp_6515_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___boxed(lean_object* v_ref_6588_, lean_object* v_addEntry_6589_, lean_object* v_droppedKeys_6590_, lean_object* v_constantsPerTask_6591_, lean_object* v_droppedEntriesRef_6592_, lean_object* v_ty_6593_, lean_object* v_a_6594_, lean_object* v_a_6595_, lean_object* v_a_6596_, lean_object* v_a_6597_, lean_object* v_a_6598_){
_start:
{
lean_object* v_res_6599_; 
v_res_6599_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(v_ref_6588_, v_addEntry_6589_, v_droppedKeys_6590_, v_constantsPerTask_6591_, v_droppedEntriesRef_6592_, v_ty_6593_, v_a_6594_, v_a_6595_, v_a_6596_, v_a_6597_);
lean_dec(v_a_6597_);
lean_dec_ref(v_a_6596_);
lean_dec(v_a_6595_);
lean_dec_ref(v_a_6594_);
lean_dec(v_ref_6588_);
return v_res_6599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches(lean_object* v_00_u03b1_6600_, lean_object* v_ref_6601_, lean_object* v_addEntry_6602_, lean_object* v_droppedKeys_6603_, lean_object* v_constantsPerTask_6604_, lean_object* v_droppedEntriesRef_6605_, lean_object* v_ty_6606_, lean_object* v_a_6607_, lean_object* v_a_6608_, lean_object* v_a_6609_, lean_object* v_a_6610_){
_start:
{
lean_object* v___x_6612_; 
v___x_6612_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(v_ref_6601_, v_addEntry_6602_, v_droppedKeys_6603_, v_constantsPerTask_6604_, v_droppedEntriesRef_6605_, v_ty_6606_, v_a_6607_, v_a_6608_, v_a_6609_, v_a_6610_);
return v___x_6612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___boxed(lean_object* v_00_u03b1_6613_, lean_object* v_ref_6614_, lean_object* v_addEntry_6615_, lean_object* v_droppedKeys_6616_, lean_object* v_constantsPerTask_6617_, lean_object* v_droppedEntriesRef_6618_, lean_object* v_ty_6619_, lean_object* v_a_6620_, lean_object* v_a_6621_, lean_object* v_a_6622_, lean_object* v_a_6623_, lean_object* v_a_6624_){
_start:
{
lean_object* v_res_6625_; 
v_res_6625_ = l_Lean_Meta_LazyDiscrTree_findImportMatches(v_00_u03b1_6613_, v_ref_6614_, v_addEntry_6615_, v_droppedKeys_6616_, v_constantsPerTask_6617_, v_droppedEntriesRef_6618_, v_ty_6619_, v_a_6620_, v_a_6621_, v_a_6622_, v_a_6623_);
lean_dec(v_a_6623_);
lean_dec_ref(v_a_6622_);
lean_dec(v_a_6621_);
lean_dec_ref(v_a_6620_);
lean_dec(v_ref_6614_);
return v_res_6625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0(lean_object* v_00_u03b1_6626_, lean_object* v_cctx_6627_, lean_object* v_ngen_6628_, lean_object* v_env_6629_, lean_object* v_act_6630_, lean_object* v_constantsPerTask_6631_, lean_object* v___y_6632_, lean_object* v___y_6633_, lean_object* v___y_6634_, lean_object* v___y_6635_){
_start:
{
lean_object* v___x_6637_; 
v___x_6637_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(v_cctx_6627_, v_ngen_6628_, v_env_6629_, v_act_6630_, v_constantsPerTask_6631_, v___y_6632_, v___y_6633_, v___y_6634_, v___y_6635_);
return v___x_6637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___boxed(lean_object* v_00_u03b1_6638_, lean_object* v_cctx_6639_, lean_object* v_ngen_6640_, lean_object* v_env_6641_, lean_object* v_act_6642_, lean_object* v_constantsPerTask_6643_, lean_object* v___y_6644_, lean_object* v___y_6645_, lean_object* v___y_6646_, lean_object* v___y_6647_, lean_object* v___y_6648_){
_start:
{
lean_object* v_res_6649_; 
v_res_6649_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0(v_00_u03b1_6638_, v_cctx_6639_, v_ngen_6640_, v_env_6641_, v_act_6642_, v_constantsPerTask_6643_, v___y_6644_, v___y_6645_, v___y_6646_, v___y_6647_);
lean_dec(v___y_6647_);
lean_dec_ref(v___y_6646_);
lean_dec(v___y_6645_);
lean_dec_ref(v___y_6644_);
lean_dec(v_constantsPerTask_6643_);
return v_res_6649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1(lean_object* v_00_u03b1_6650_, lean_object* v_cctx_6651_, lean_object* v_env_6652_, lean_object* v_act_6653_, lean_object* v_constantsPerTask_6654_, lean_object* v_n_6655_, lean_object* v_ngen_6656_, lean_object* v_tasks_6657_, lean_object* v_start_6658_, lean_object* v_cnt_6659_, lean_object* v_idx_6660_, lean_object* v___y_6661_, lean_object* v___y_6662_, lean_object* v___y_6663_, lean_object* v___y_6664_){
_start:
{
lean_object* v___x_6666_; 
v___x_6666_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(v_cctx_6651_, v_env_6652_, v_act_6653_, v_constantsPerTask_6654_, v_n_6655_, v_ngen_6656_, v_tasks_6657_, v_start_6658_, v_cnt_6659_, v_idx_6660_);
return v___x_6666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___boxed(lean_object* v_00_u03b1_6667_, lean_object* v_cctx_6668_, lean_object* v_env_6669_, lean_object* v_act_6670_, lean_object* v_constantsPerTask_6671_, lean_object* v_n_6672_, lean_object* v_ngen_6673_, lean_object* v_tasks_6674_, lean_object* v_start_6675_, lean_object* v_cnt_6676_, lean_object* v_idx_6677_, lean_object* v___y_6678_, lean_object* v___y_6679_, lean_object* v___y_6680_, lean_object* v___y_6681_, lean_object* v___y_6682_){
_start:
{
lean_object* v_res_6683_; 
v_res_6683_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1(v_00_u03b1_6667_, v_cctx_6668_, v_env_6669_, v_act_6670_, v_constantsPerTask_6671_, v_n_6672_, v_ngen_6673_, v_tasks_6674_, v_start_6675_, v_cnt_6676_, v_idx_6677_, v___y_6678_, v___y_6679_, v___y_6680_, v___y_6681_);
lean_dec(v___y_6681_);
lean_dec_ref(v___y_6680_);
lean_dec(v___y_6679_);
lean_dec_ref(v___y_6678_);
lean_dec(v_constantsPerTask_6671_);
return v_res_6683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2(lean_object* v_00_u03b1_6684_, lean_object* v_z_6685_, lean_object* v_tasks_6686_){
_start:
{
lean_object* v___x_6687_; 
v___x_6687_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(v_z_6685_, v_tasks_6686_);
return v___x_6687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___boxed(lean_object* v_00_u03b1_6688_, lean_object* v_z_6689_, lean_object* v_tasks_6690_){
_start:
{
lean_object* v_res_6691_; 
v_res_6691_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2(v_00_u03b1_6688_, v_z_6689_, v_tasks_6690_);
lean_dec_ref(v_tasks_6690_);
return v_res_6691_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5(lean_object* v_00_u03b1_6692_, lean_object* v_as_6693_, size_t v_i_6694_, size_t v_stop_6695_, lean_object* v_b_6696_){
_start:
{
lean_object* v___x_6697_; 
v___x_6697_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(v_as_6693_, v_i_6694_, v_stop_6695_, v_b_6696_);
return v___x_6697_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b1_6698_, lean_object* v_as_6699_, lean_object* v_i_6700_, lean_object* v_stop_6701_, lean_object* v_b_6702_){
_start:
{
size_t v_i_boxed_6703_; size_t v_stop_boxed_6704_; lean_object* v_res_6705_; 
v_i_boxed_6703_ = lean_unbox_usize(v_i_6700_);
lean_dec(v_i_6700_);
v_stop_boxed_6704_ = lean_unbox_usize(v_stop_6701_);
lean_dec(v_stop_6701_);
v_res_6705_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5(v_00_u03b1_6698_, v_as_6699_, v_i_boxed_6703_, v_stop_boxed_6704_, v_b_6702_);
lean_dec_ref(v_as_6699_);
return v_res_6705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(lean_object* v___y_6706_){
_start:
{
lean_object* v___x_6708_; lean_object* v_ngen_6709_; lean_object* v_namePrefix_6710_; lean_object* v_idx_6711_; lean_object* v___x_6713_; uint8_t v_isShared_6714_; uint8_t v_isSharedCheck_6742_; 
v___x_6708_ = lean_st_ref_get(v___y_6706_);
v_ngen_6709_ = lean_ctor_get(v___x_6708_, 2);
lean_inc_ref(v_ngen_6709_);
lean_dec(v___x_6708_);
v_namePrefix_6710_ = lean_ctor_get(v_ngen_6709_, 0);
v_idx_6711_ = lean_ctor_get(v_ngen_6709_, 1);
v_isSharedCheck_6742_ = !lean_is_exclusive(v_ngen_6709_);
if (v_isSharedCheck_6742_ == 0)
{
v___x_6713_ = v_ngen_6709_;
v_isShared_6714_ = v_isSharedCheck_6742_;
goto v_resetjp_6712_;
}
else
{
lean_inc(v_idx_6711_);
lean_inc(v_namePrefix_6710_);
lean_dec(v_ngen_6709_);
v___x_6713_ = lean_box(0);
v_isShared_6714_ = v_isSharedCheck_6742_;
goto v_resetjp_6712_;
}
v_resetjp_6712_:
{
lean_object* v___x_6715_; lean_object* v___x_6716_; lean_object* v___x_6718_; 
lean_inc(v_idx_6711_);
lean_inc(v_namePrefix_6710_);
v___x_6715_ = l_Lean_Name_num___override(v_namePrefix_6710_, v_idx_6711_);
v___x_6716_ = lean_unsigned_to_nat(1u);
if (v_isShared_6714_ == 0)
{
lean_ctor_set(v___x_6713_, 1, v___x_6716_);
lean_ctor_set(v___x_6713_, 0, v___x_6715_);
v___x_6718_ = v___x_6713_;
goto v_reusejp_6717_;
}
else
{
lean_object* v_reuseFailAlloc_6741_; 
v_reuseFailAlloc_6741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6741_, 0, v___x_6715_);
lean_ctor_set(v_reuseFailAlloc_6741_, 1, v___x_6716_);
v___x_6718_ = v_reuseFailAlloc_6741_;
goto v_reusejp_6717_;
}
v_reusejp_6717_:
{
lean_object* v___x_6719_; lean_object* v___x_6720_; lean_object* v___x_6721_; lean_object* v_env_6722_; lean_object* v_nextMacroScope_6723_; lean_object* v_auxDeclNGen_6724_; lean_object* v_traceState_6725_; lean_object* v_cache_6726_; lean_object* v_recordedDeps_6727_; lean_object* v_messages_6728_; lean_object* v_infoState_6729_; lean_object* v_snapshotTasks_6730_; lean_object* v___x_6732_; uint8_t v_isShared_6733_; uint8_t v_isSharedCheck_6739_; 
v___x_6719_ = lean_nat_add(v_idx_6711_, v___x_6716_);
lean_dec(v_idx_6711_);
v___x_6720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6720_, 0, v_namePrefix_6710_);
lean_ctor_set(v___x_6720_, 1, v___x_6719_);
v___x_6721_ = lean_st_ref_take(v___y_6706_);
v_env_6722_ = lean_ctor_get(v___x_6721_, 0);
v_nextMacroScope_6723_ = lean_ctor_get(v___x_6721_, 1);
v_auxDeclNGen_6724_ = lean_ctor_get(v___x_6721_, 3);
v_traceState_6725_ = lean_ctor_get(v___x_6721_, 4);
v_cache_6726_ = lean_ctor_get(v___x_6721_, 5);
v_recordedDeps_6727_ = lean_ctor_get(v___x_6721_, 6);
v_messages_6728_ = lean_ctor_get(v___x_6721_, 7);
v_infoState_6729_ = lean_ctor_get(v___x_6721_, 8);
v_snapshotTasks_6730_ = lean_ctor_get(v___x_6721_, 9);
v_isSharedCheck_6739_ = !lean_is_exclusive(v___x_6721_);
if (v_isSharedCheck_6739_ == 0)
{
lean_object* v_unused_6740_; 
v_unused_6740_ = lean_ctor_get(v___x_6721_, 2);
lean_dec(v_unused_6740_);
v___x_6732_ = v___x_6721_;
v_isShared_6733_ = v_isSharedCheck_6739_;
goto v_resetjp_6731_;
}
else
{
lean_inc(v_snapshotTasks_6730_);
lean_inc(v_infoState_6729_);
lean_inc(v_messages_6728_);
lean_inc(v_recordedDeps_6727_);
lean_inc(v_cache_6726_);
lean_inc(v_traceState_6725_);
lean_inc(v_auxDeclNGen_6724_);
lean_inc(v_nextMacroScope_6723_);
lean_inc(v_env_6722_);
lean_dec(v___x_6721_);
v___x_6732_ = lean_box(0);
v_isShared_6733_ = v_isSharedCheck_6739_;
goto v_resetjp_6731_;
}
v_resetjp_6731_:
{
lean_object* v___x_6735_; 
if (v_isShared_6733_ == 0)
{
lean_ctor_set(v___x_6732_, 2, v___x_6720_);
v___x_6735_ = v___x_6732_;
goto v_reusejp_6734_;
}
else
{
lean_object* v_reuseFailAlloc_6738_; 
v_reuseFailAlloc_6738_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6738_, 0, v_env_6722_);
lean_ctor_set(v_reuseFailAlloc_6738_, 1, v_nextMacroScope_6723_);
lean_ctor_set(v_reuseFailAlloc_6738_, 2, v___x_6720_);
lean_ctor_set(v_reuseFailAlloc_6738_, 3, v_auxDeclNGen_6724_);
lean_ctor_set(v_reuseFailAlloc_6738_, 4, v_traceState_6725_);
lean_ctor_set(v_reuseFailAlloc_6738_, 5, v_cache_6726_);
lean_ctor_set(v_reuseFailAlloc_6738_, 6, v_recordedDeps_6727_);
lean_ctor_set(v_reuseFailAlloc_6738_, 7, v_messages_6728_);
lean_ctor_set(v_reuseFailAlloc_6738_, 8, v_infoState_6729_);
lean_ctor_set(v_reuseFailAlloc_6738_, 9, v_snapshotTasks_6730_);
v___x_6735_ = v_reuseFailAlloc_6738_;
goto v_reusejp_6734_;
}
v_reusejp_6734_:
{
lean_object* v___x_6736_; lean_object* v___x_6737_; 
v___x_6736_ = lean_st_ref_put(v___y_6706_, v___x_6735_);
v___x_6737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6737_, 0, v___x_6718_);
return v___x_6737_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg___boxed(lean_object* v___y_6743_, lean_object* v___y_6744_){
_start:
{
lean_object* v_res_6745_; 
v_res_6745_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(v___y_6743_);
lean_dec(v___y_6743_);
return v_res_6745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1(lean_object* v___y_6746_, lean_object* v___y_6747_){
_start:
{
lean_object* v___x_6749_; 
v___x_6749_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(v___y_6747_);
return v___x_6749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___boxed(lean_object* v___y_6750_, lean_object* v___y_6751_, lean_object* v___y_6752_){
_start:
{
lean_object* v_res_6753_; 
v_res_6753_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1(v___y_6750_, v___y_6751_);
lean_dec(v___y_6751_);
lean_dec_ref(v___y_6750_);
return v_res_6753_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0(void){
_start:
{
lean_object* v___x_6754_; lean_object* v___x_6755_; lean_object* v___x_6756_; 
v___x_6754_ = lean_unsigned_to_nat(32u);
v___x_6755_ = lean_mk_empty_array_with_capacity(v___x_6754_);
v___x_6756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6756_, 0, v___x_6755_);
return v___x_6756_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1(void){
_start:
{
size_t v___x_6757_; lean_object* v___x_6758_; lean_object* v___x_6759_; lean_object* v___x_6760_; lean_object* v___x_6761_; lean_object* v___x_6762_; 
v___x_6757_ = ((size_t)5ULL);
v___x_6758_ = lean_unsigned_to_nat(0u);
v___x_6759_ = lean_unsigned_to_nat(32u);
v___x_6760_ = lean_mk_empty_array_with_capacity(v___x_6759_);
v___x_6761_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0);
v___x_6762_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_6762_, 0, v___x_6761_);
lean_ctor_set(v___x_6762_, 1, v___x_6760_);
lean_ctor_set(v___x_6762_, 2, v___x_6758_);
lean_ctor_set(v___x_6762_, 3, v___x_6758_);
lean_ctor_set_usize(v___x_6762_, 4, v___x_6757_);
return v___x_6762_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2(void){
_start:
{
lean_object* v___x_6763_; lean_object* v___x_6764_; lean_object* v___x_6765_; lean_object* v___x_6766_; 
v___x_6763_ = lean_box(1);
v___x_6764_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1);
v___x_6765_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0);
v___x_6766_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6766_, 0, v___x_6765_);
lean_ctor_set(v___x_6766_, 1, v___x_6764_);
lean_ctor_set(v___x_6766_, 2, v___x_6763_);
return v___x_6766_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_msgData_6767_, lean_object* v___y_6768_, lean_object* v___y_6769_){
_start:
{
lean_object* v___x_6771_; lean_object* v_toCold_6772_; lean_object* v_env_6773_; lean_object* v_options_6774_; uint8_t v___x_6775_; lean_object* v_env_6776_; lean_object* v___x_6777_; lean_object* v___x_6778_; lean_object* v___x_6779_; lean_object* v___x_6780_; lean_object* v___x_6781_; 
v___x_6771_ = lean_st_ref_get(v___y_6769_);
v_toCold_6772_ = lean_ctor_get(v___y_6768_, 0);
v_env_6773_ = lean_ctor_get(v___x_6771_, 0);
lean_inc_ref(v_env_6773_);
lean_dec(v___x_6771_);
v_options_6774_ = lean_ctor_get(v_toCold_6772_, 2);
v___x_6775_ = 0;
v_env_6776_ = l_Lean_Environment_setRecordingDeps(v_env_6773_, v___x_6775_);
v___x_6777_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_6778_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2);
lean_inc_ref(v_options_6774_);
v___x_6779_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6779_, 0, v_env_6776_);
lean_ctor_set(v___x_6779_, 1, v___x_6777_);
lean_ctor_set(v___x_6779_, 2, v___x_6778_);
lean_ctor_set(v___x_6779_, 3, v_options_6774_);
v___x_6780_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_6780_, 0, v___x_6779_);
lean_ctor_set(v___x_6780_, 1, v_msgData_6767_);
v___x_6781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6781_, 0, v___x_6780_);
return v___x_6781_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(lean_object* v_msgData_6782_, lean_object* v___y_6783_, lean_object* v___y_6784_, lean_object* v___y_6785_){
_start:
{
lean_object* v_res_6786_; 
v_res_6786_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5(v_msgData_6782_, v___y_6783_, v___y_6784_);
lean_dec(v___y_6784_);
lean_dec_ref(v___y_6783_);
return v_res_6786_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4(lean_object* v_ref_6787_, lean_object* v_msgData_6788_, uint8_t v_severity_6789_, uint8_t v_isSilent_6790_, lean_object* v___y_6791_, lean_object* v___y_6792_){
_start:
{
lean_object* v___y_6795_; lean_object* v___y_6796_; lean_object* v___y_6797_; uint8_t v___y_6798_; lean_object* v___y_6799_; lean_object* v___y_6800_; uint8_t v___y_6801_; lean_object* v_toCold_6802_; lean_object* v___y_6803_; lean_object* v___y_6832_; lean_object* v___y_6833_; uint8_t v___y_6834_; lean_object* v___y_6835_; uint8_t v___y_6836_; uint8_t v___y_6837_; lean_object* v___y_6838_; lean_object* v___y_6839_; uint8_t v___y_6859_; lean_object* v___y_6860_; lean_object* v___y_6861_; lean_object* v___y_6862_; uint8_t v___y_6863_; uint8_t v___y_6864_; lean_object* v___y_6865_; uint8_t v___y_6869_; uint8_t v___y_6870_; uint8_t v___x_6880_; uint8_t v___y_6882_; uint8_t v___x_6888_; 
v___x_6880_ = 2;
v___x_6888_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6789_, v___x_6880_);
if (v___x_6888_ == 0)
{
v___y_6882_ = v___x_6888_;
goto v___jp_6881_;
}
else
{
uint8_t v___x_6889_; 
lean_inc_ref(v_msgData_6788_);
v___x_6889_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_6788_);
if (v___x_6889_ == 0)
{
v___y_6882_ = v___x_6889_;
goto v___jp_6881_;
}
else
{
lean_object* v___x_6890_; lean_object* v___x_6891_; 
lean_dec_ref(v_msgData_6788_);
v___x_6890_ = lean_box(0);
v___x_6891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6891_, 0, v___x_6890_);
return v___x_6891_;
}
}
v___jp_6794_:
{
lean_object* v_currNamespace_6804_; lean_object* v_openDecls_6805_; lean_object* v___x_6806_; lean_object* v___x_6807_; lean_object* v___x_6808_; lean_object* v___x_6809_; lean_object* v_env_6810_; lean_object* v_nextMacroScope_6811_; lean_object* v_ngen_6812_; lean_object* v_auxDeclNGen_6813_; lean_object* v_traceState_6814_; lean_object* v_cache_6815_; lean_object* v_recordedDeps_6816_; lean_object* v_messages_6817_; lean_object* v_infoState_6818_; lean_object* v_snapshotTasks_6819_; lean_object* v___x_6821_; uint8_t v_isShared_6822_; uint8_t v_isSharedCheck_6830_; 
v_currNamespace_6804_ = lean_ctor_get(v_toCold_6802_, 4);
v_openDecls_6805_ = lean_ctor_get(v_toCold_6802_, 5);
lean_inc(v_openDecls_6805_);
lean_inc(v_currNamespace_6804_);
v___x_6806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6806_, 0, v_currNamespace_6804_);
lean_ctor_set(v___x_6806_, 1, v_openDecls_6805_);
v___x_6807_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6807_, 0, v___x_6806_);
lean_ctor_set(v___x_6807_, 1, v___y_6799_);
lean_inc_ref(v___y_6797_);
lean_inc_ref(v___y_6795_);
v___x_6808_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_6808_, 0, v___y_6795_);
lean_ctor_set(v___x_6808_, 1, v___y_6796_);
lean_ctor_set(v___x_6808_, 2, v___y_6800_);
lean_ctor_set(v___x_6808_, 3, v___y_6797_);
lean_ctor_set(v___x_6808_, 4, v___x_6807_);
lean_ctor_set_uint8(v___x_6808_, sizeof(void*)*5, v___y_6798_);
lean_ctor_set_uint8(v___x_6808_, sizeof(void*)*5 + 1, v___y_6801_);
lean_ctor_set_uint8(v___x_6808_, sizeof(void*)*5 + 2, v_isSilent_6790_);
v___x_6809_ = lean_st_ref_take(v___y_6803_);
v_env_6810_ = lean_ctor_get(v___x_6809_, 0);
v_nextMacroScope_6811_ = lean_ctor_get(v___x_6809_, 1);
v_ngen_6812_ = lean_ctor_get(v___x_6809_, 2);
v_auxDeclNGen_6813_ = lean_ctor_get(v___x_6809_, 3);
v_traceState_6814_ = lean_ctor_get(v___x_6809_, 4);
v_cache_6815_ = lean_ctor_get(v___x_6809_, 5);
v_recordedDeps_6816_ = lean_ctor_get(v___x_6809_, 6);
v_messages_6817_ = lean_ctor_get(v___x_6809_, 7);
v_infoState_6818_ = lean_ctor_get(v___x_6809_, 8);
v_snapshotTasks_6819_ = lean_ctor_get(v___x_6809_, 9);
v_isSharedCheck_6830_ = !lean_is_exclusive(v___x_6809_);
if (v_isSharedCheck_6830_ == 0)
{
v___x_6821_ = v___x_6809_;
v_isShared_6822_ = v_isSharedCheck_6830_;
goto v_resetjp_6820_;
}
else
{
lean_inc(v_snapshotTasks_6819_);
lean_inc(v_infoState_6818_);
lean_inc(v_messages_6817_);
lean_inc(v_recordedDeps_6816_);
lean_inc(v_cache_6815_);
lean_inc(v_traceState_6814_);
lean_inc(v_auxDeclNGen_6813_);
lean_inc(v_ngen_6812_);
lean_inc(v_nextMacroScope_6811_);
lean_inc(v_env_6810_);
lean_dec(v___x_6809_);
v___x_6821_ = lean_box(0);
v_isShared_6822_ = v_isSharedCheck_6830_;
goto v_resetjp_6820_;
}
v_resetjp_6820_:
{
lean_object* v___x_6823_; lean_object* v___x_6824_; lean_object* v___x_6826_; 
v___x_6823_ = lean_box(0);
v___x_6824_ = l_Lean_MessageLog_add(v___x_6808_, v_messages_6817_);
if (v_isShared_6822_ == 0)
{
lean_ctor_set(v___x_6821_, 7, v___x_6824_);
v___x_6826_ = v___x_6821_;
goto v_reusejp_6825_;
}
else
{
lean_object* v_reuseFailAlloc_6829_; 
v_reuseFailAlloc_6829_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6829_, 0, v_env_6810_);
lean_ctor_set(v_reuseFailAlloc_6829_, 1, v_nextMacroScope_6811_);
lean_ctor_set(v_reuseFailAlloc_6829_, 2, v_ngen_6812_);
lean_ctor_set(v_reuseFailAlloc_6829_, 3, v_auxDeclNGen_6813_);
lean_ctor_set(v_reuseFailAlloc_6829_, 4, v_traceState_6814_);
lean_ctor_set(v_reuseFailAlloc_6829_, 5, v_cache_6815_);
lean_ctor_set(v_reuseFailAlloc_6829_, 6, v_recordedDeps_6816_);
lean_ctor_set(v_reuseFailAlloc_6829_, 7, v___x_6824_);
lean_ctor_set(v_reuseFailAlloc_6829_, 8, v_infoState_6818_);
lean_ctor_set(v_reuseFailAlloc_6829_, 9, v_snapshotTasks_6819_);
v___x_6826_ = v_reuseFailAlloc_6829_;
goto v_reusejp_6825_;
}
v_reusejp_6825_:
{
lean_object* v___x_6827_; lean_object* v___x_6828_; 
v___x_6827_ = lean_st_ref_put(v___y_6803_, v___x_6826_);
v___x_6828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6828_, 0, v___x_6823_);
return v___x_6828_;
}
}
}
v___jp_6831_:
{
lean_object* v_fileName_6840_; lean_object* v_fileMap_6841_; lean_object* v___x_6842_; lean_object* v___x_6843_; lean_object* v_a_6844_; lean_object* v___x_6846_; uint8_t v_isShared_6847_; uint8_t v_isSharedCheck_6857_; 
v_fileName_6840_ = lean_ctor_get(v___y_6835_, 0);
v_fileMap_6841_ = lean_ctor_get(v___y_6835_, 1);
v___x_6842_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_6788_);
v___x_6843_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5(v___x_6842_, v___y_6791_, v___y_6792_);
v_a_6844_ = lean_ctor_get(v___x_6843_, 0);
v_isSharedCheck_6857_ = !lean_is_exclusive(v___x_6843_);
if (v_isSharedCheck_6857_ == 0)
{
v___x_6846_ = v___x_6843_;
v_isShared_6847_ = v_isSharedCheck_6857_;
goto v_resetjp_6845_;
}
else
{
lean_inc(v_a_6844_);
lean_dec(v___x_6843_);
v___x_6846_ = lean_box(0);
v_isShared_6847_ = v_isSharedCheck_6857_;
goto v_resetjp_6845_;
}
v_resetjp_6845_:
{
lean_object* v___x_6848_; lean_object* v___x_6849_; lean_object* v___x_6850_; lean_object* v___x_6851_; 
lean_inc_ref_n(v_fileMap_6841_, 2);
v___x_6848_ = l_Lean_FileMap_toPosition(v_fileMap_6841_, v___y_6838_);
lean_dec(v___y_6838_);
v___x_6849_ = l_Lean_FileMap_toPosition(v_fileMap_6841_, v___y_6839_);
lean_dec(v___y_6839_);
v___x_6850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6850_, 0, v___x_6849_);
v___x_6851_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___closed__0));
if (v___y_6834_ == 0)
{
lean_del_object(v___x_6846_);
lean_dec_ref(v___y_6833_);
v___y_6795_ = v_fileName_6840_;
v___y_6796_ = v___x_6848_;
v___y_6797_ = v___x_6851_;
v___y_6798_ = v___y_6836_;
v___y_6799_ = v_a_6844_;
v___y_6800_ = v___x_6850_;
v___y_6801_ = v___y_6837_;
v_toCold_6802_ = v___y_6832_;
v___y_6803_ = v___y_6792_;
goto v___jp_6794_;
}
else
{
uint8_t v___x_6852_; 
lean_inc(v_a_6844_);
v___x_6852_ = l_Lean_MessageData_hasTag(v___y_6833_, v_a_6844_);
if (v___x_6852_ == 0)
{
lean_object* v___x_6853_; lean_object* v___x_6855_; 
lean_dec_ref_known(v___x_6850_, 1);
lean_dec_ref(v___x_6848_);
lean_dec(v_a_6844_);
v___x_6853_ = lean_box(0);
if (v_isShared_6847_ == 0)
{
lean_ctor_set(v___x_6846_, 0, v___x_6853_);
v___x_6855_ = v___x_6846_;
goto v_reusejp_6854_;
}
else
{
lean_object* v_reuseFailAlloc_6856_; 
v_reuseFailAlloc_6856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6856_, 0, v___x_6853_);
v___x_6855_ = v_reuseFailAlloc_6856_;
goto v_reusejp_6854_;
}
v_reusejp_6854_:
{
return v___x_6855_;
}
}
else
{
lean_del_object(v___x_6846_);
v___y_6795_ = v_fileName_6840_;
v___y_6796_ = v___x_6848_;
v___y_6797_ = v___x_6851_;
v___y_6798_ = v___y_6836_;
v___y_6799_ = v_a_6844_;
v___y_6800_ = v___x_6850_;
v___y_6801_ = v___y_6837_;
v_toCold_6802_ = v___y_6832_;
v___y_6803_ = v___y_6792_;
goto v___jp_6794_;
}
}
}
}
v___jp_6858_:
{
lean_object* v___x_6866_; 
v___x_6866_ = l_Lean_Syntax_getTailPos_x3f(v___y_6862_, v___y_6863_);
lean_dec(v___y_6862_);
if (lean_obj_tag(v___x_6866_) == 0)
{
lean_inc(v___y_6865_);
v___y_6832_ = v___y_6860_;
v___y_6833_ = v___y_6861_;
v___y_6834_ = v___y_6859_;
v___y_6835_ = v___y_6860_;
v___y_6836_ = v___y_6863_;
v___y_6837_ = v___y_6864_;
v___y_6838_ = v___y_6865_;
v___y_6839_ = v___y_6865_;
goto v___jp_6831_;
}
else
{
lean_object* v_val_6867_; 
v_val_6867_ = lean_ctor_get(v___x_6866_, 0);
lean_inc(v_val_6867_);
lean_dec_ref_known(v___x_6866_, 1);
v___y_6832_ = v___y_6860_;
v___y_6833_ = v___y_6861_;
v___y_6834_ = v___y_6859_;
v___y_6835_ = v___y_6860_;
v___y_6836_ = v___y_6863_;
v___y_6837_ = v___y_6864_;
v___y_6838_ = v___y_6865_;
v___y_6839_ = v_val_6867_;
goto v___jp_6831_;
}
}
v___jp_6868_:
{
lean_object* v_toCold_6871_; lean_object* v_ref_6872_; uint8_t v_suppressElabErrors_6873_; lean_object* v___x_6874_; lean_object* v___f_6875_; lean_object* v_ref_6876_; lean_object* v___x_6877_; 
v_toCold_6871_ = lean_ctor_get(v___y_6791_, 0);
v_ref_6872_ = lean_ctor_get(v___y_6791_, 2);
v_suppressElabErrors_6873_ = lean_ctor_get_uint8(v___y_6791_, sizeof(void*)*3 + 2);
v___x_6874_ = lean_box(v_suppressElabErrors_6873_);
v___f_6875_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___boxed), 2, 1);
lean_closure_set(v___f_6875_, 0, v___x_6874_);
v_ref_6876_ = l_Lean_replaceRef(v_ref_6787_, v_ref_6872_);
v___x_6877_ = l_Lean_Syntax_getPos_x3f(v_ref_6876_, v___y_6869_);
if (lean_obj_tag(v___x_6877_) == 0)
{
lean_object* v___x_6878_; 
v___x_6878_ = lean_unsigned_to_nat(0u);
v___y_6859_ = v_suppressElabErrors_6873_;
v___y_6860_ = v_toCold_6871_;
v___y_6861_ = v___f_6875_;
v___y_6862_ = v_ref_6876_;
v___y_6863_ = v___y_6869_;
v___y_6864_ = v___y_6870_;
v___y_6865_ = v___x_6878_;
goto v___jp_6858_;
}
else
{
lean_object* v_val_6879_; 
v_val_6879_ = lean_ctor_get(v___x_6877_, 0);
lean_inc(v_val_6879_);
lean_dec_ref_known(v___x_6877_, 1);
v___y_6859_ = v_suppressElabErrors_6873_;
v___y_6860_ = v_toCold_6871_;
v___y_6861_ = v___f_6875_;
v___y_6862_ = v_ref_6876_;
v___y_6863_ = v___y_6869_;
v___y_6864_ = v___y_6870_;
v___y_6865_ = v_val_6879_;
goto v___jp_6858_;
}
}
v___jp_6881_:
{
uint8_t v___x_6883_; uint8_t v___x_6884_; 
v___x_6883_ = 1;
v___x_6884_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6789_, v___x_6883_);
if (v___x_6884_ == 0)
{
v___y_6869_ = v___y_6882_;
v___y_6870_ = v_severity_6789_;
goto v___jp_6868_;
}
else
{
lean_object* v___x_6885_; lean_object* v___x_6886_; uint8_t v___x_6887_; 
v___x_6885_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_6791_);
v___x_6886_ = l_Lean_warningAsError;
v___x_6887_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7_spec__9(v___x_6885_, v___x_6886_);
lean_dec_ref(v___x_6885_);
if (v___x_6887_ == 0)
{
v___y_6869_ = v___y_6882_;
v___y_6870_ = v_severity_6789_;
goto v___jp_6868_;
}
else
{
v___y_6869_ = v___y_6882_;
v___y_6870_ = v___x_6880_;
goto v___jp_6868_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_ref_6892_, lean_object* v_msgData_6893_, lean_object* v_severity_6894_, lean_object* v_isSilent_6895_, lean_object* v___y_6896_, lean_object* v___y_6897_, lean_object* v___y_6898_){
_start:
{
uint8_t v_severity_boxed_6899_; uint8_t v_isSilent_boxed_6900_; lean_object* v_res_6901_; 
v_severity_boxed_6899_ = lean_unbox(v_severity_6894_);
v_isSilent_boxed_6900_ = lean_unbox(v_isSilent_6895_);
v_res_6901_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4(v_ref_6892_, v_msgData_6893_, v_severity_boxed_6899_, v_isSilent_boxed_6900_, v___y_6896_, v___y_6897_);
lean_dec(v___y_6897_);
lean_dec_ref(v___y_6896_);
lean_dec(v_ref_6892_);
return v_res_6901_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2(lean_object* v_msgData_6902_, uint8_t v_severity_6903_, uint8_t v_isSilent_6904_, lean_object* v___y_6905_, lean_object* v___y_6906_){
_start:
{
lean_object* v_ref_6908_; lean_object* v___x_6909_; 
v_ref_6908_ = lean_ctor_get(v___y_6905_, 2);
v___x_6909_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4(v_ref_6908_, v_msgData_6902_, v_severity_6903_, v_isSilent_6904_, v___y_6905_, v___y_6906_);
return v___x_6909_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_6910_, lean_object* v_severity_6911_, lean_object* v_isSilent_6912_, lean_object* v___y_6913_, lean_object* v___y_6914_, lean_object* v___y_6915_){
_start:
{
uint8_t v_severity_boxed_6916_; uint8_t v_isSilent_boxed_6917_; lean_object* v_res_6918_; 
v_severity_boxed_6916_ = lean_unbox(v_severity_6911_);
v_isSilent_boxed_6917_ = lean_unbox(v_isSilent_6912_);
v_res_6918_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2(v_msgData_6910_, v_severity_boxed_6916_, v_isSilent_boxed_6917_, v___y_6913_, v___y_6914_);
lean_dec(v___y_6914_);
lean_dec_ref(v___y_6913_);
return v_res_6918_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0(lean_object* v_msgData_6919_, lean_object* v___y_6920_, lean_object* v___y_6921_){
_start:
{
uint8_t v___x_6923_; uint8_t v___x_6924_; lean_object* v___x_6925_; 
v___x_6923_ = 2;
v___x_6924_ = 0;
v___x_6925_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2(v_msgData_6919_, v___x_6923_, v___x_6924_, v___y_6920_, v___y_6921_);
return v___x_6925_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0___boxed(lean_object* v_msgData_6926_, lean_object* v___y_6927_, lean_object* v___y_6928_, lean_object* v___y_6929_){
_start:
{
lean_object* v_res_6930_; 
v_res_6930_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0(v_msgData_6926_, v___y_6927_, v___y_6928_);
lean_dec(v___y_6928_);
lean_dec_ref(v___y_6927_);
return v_res_6930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0(lean_object* v_f_6931_, lean_object* v___y_6932_, lean_object* v___y_6933_){
_start:
{
lean_object* v_module_6935_; lean_object* v_const_6936_; lean_object* v_exception_6937_; lean_object* v___x_6938_; lean_object* v___x_6939_; lean_object* v___x_6940_; lean_object* v___x_6941_; lean_object* v___x_6942_; lean_object* v___x_6943_; lean_object* v___x_6944_; lean_object* v___x_6945_; lean_object* v___x_6946_; lean_object* v___x_6947_; lean_object* v___x_6948_; lean_object* v___x_6949_; 
v_module_6935_ = lean_ctor_get(v_f_6931_, 0);
lean_inc(v_module_6935_);
v_const_6936_ = lean_ctor_get(v_f_6931_, 1);
lean_inc(v_const_6936_);
v_exception_6937_ = lean_ctor_get(v_f_6931_, 2);
lean_inc_ref(v_exception_6937_);
lean_dec_ref(v_f_6931_);
v___x_6938_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1);
v___x_6939_ = l_Lean_MessageData_ofName(v_const_6936_);
v___x_6940_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6940_, 0, v___x_6938_);
lean_ctor_set(v___x_6940_, 1, v___x_6939_);
v___x_6941_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3);
v___x_6942_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6942_, 0, v___x_6940_);
lean_ctor_set(v___x_6942_, 1, v___x_6941_);
v___x_6943_ = l_Lean_MessageData_ofName(v_module_6935_);
v___x_6944_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6944_, 0, v___x_6942_);
lean_ctor_set(v___x_6944_, 1, v___x_6943_);
v___x_6945_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5);
v___x_6946_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6946_, 0, v___x_6944_);
lean_ctor_set(v___x_6946_, 1, v___x_6945_);
v___x_6947_ = l_Lean_Exception_toMessageData(v_exception_6937_);
v___x_6948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6948_, 0, v___x_6946_);
lean_ctor_set(v___x_6948_, 1, v___x_6947_);
v___x_6949_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0(v___x_6948_, v___y_6932_, v___y_6933_);
return v___x_6949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0___boxed(lean_object* v_f_6950_, lean_object* v___y_6951_, lean_object* v___y_6952_, lean_object* v___y_6953_){
_start:
{
lean_object* v_res_6954_; 
v_res_6954_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0(v_f_6950_, v___y_6951_, v___y_6952_);
lean_dec(v___y_6952_);
lean_dec_ref(v___y_6951_);
return v_res_6954_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2(lean_object* v_as_6955_, size_t v_i_6956_, size_t v_stop_6957_, lean_object* v_b_6958_, lean_object* v___y_6959_, lean_object* v___y_6960_){
_start:
{
uint8_t v___x_6962_; 
v___x_6962_ = lean_usize_dec_eq(v_i_6956_, v_stop_6957_);
if (v___x_6962_ == 0)
{
lean_object* v___x_6963_; lean_object* v___x_6964_; 
v___x_6963_ = lean_array_uget_borrowed(v_as_6955_, v_i_6956_);
lean_inc(v___x_6963_);
v___x_6964_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0(v___x_6963_, v___y_6959_, v___y_6960_);
if (lean_obj_tag(v___x_6964_) == 0)
{
lean_object* v_a_6965_; size_t v___x_6966_; size_t v___x_6967_; 
v_a_6965_ = lean_ctor_get(v___x_6964_, 0);
lean_inc(v_a_6965_);
lean_dec_ref_known(v___x_6964_, 1);
v___x_6966_ = ((size_t)1ULL);
v___x_6967_ = lean_usize_add(v_i_6956_, v___x_6966_);
v_i_6956_ = v___x_6967_;
v_b_6958_ = v_a_6965_;
goto _start;
}
else
{
return v___x_6964_;
}
}
else
{
lean_object* v___x_6969_; 
v___x_6969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6969_, 0, v_b_6958_);
return v___x_6969_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2___boxed(lean_object* v_as_6970_, lean_object* v_i_6971_, lean_object* v_stop_6972_, lean_object* v_b_6973_, lean_object* v___y_6974_, lean_object* v___y_6975_, lean_object* v___y_6976_){
_start:
{
size_t v_i_boxed_6977_; size_t v_stop_boxed_6978_; lean_object* v_res_6979_; 
v_i_boxed_6977_ = lean_unbox_usize(v_i_6971_);
lean_dec(v_i_6971_);
v_stop_boxed_6978_ = lean_unbox_usize(v_stop_6972_);
lean_dec(v_stop_6972_);
v_res_6979_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2(v_as_6970_, v_i_boxed_6977_, v_stop_boxed_6978_, v_b_6973_, v___y_6974_, v___y_6975_);
lean_dec(v___y_6975_);
lean_dec_ref(v___y_6974_);
lean_dec_ref(v_as_6970_);
return v_res_6979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(lean_object* v_entriesForConst_6980_, lean_object* v_a_6981_, lean_object* v_a_6982_){
_start:
{
lean_object* v___x_6984_; lean_object* v_env_6985_; lean_object* v___x_6986_; lean_object* v_a_6987_; lean_object* v___x_6989_; uint8_t v_isShared_6990_; uint8_t v_isSharedCheck_7014_; 
v___x_6984_ = lean_st_ref_get(v_a_6982_);
v_env_6985_ = lean_ctor_get(v___x_6984_, 0);
lean_inc_ref(v_env_6985_);
lean_dec(v___x_6984_);
v___x_6986_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(v_a_6982_);
v_a_6987_ = lean_ctor_get(v___x_6986_, 0);
v_isSharedCheck_7014_ = !lean_is_exclusive(v___x_6986_);
if (v_isSharedCheck_7014_ == 0)
{
v___x_6989_ = v___x_6986_;
v_isShared_6990_ = v_isSharedCheck_7014_;
goto v_resetjp_6988_;
}
else
{
lean_inc(v_a_6987_);
lean_dec(v___x_6986_);
v___x_6989_ = lean_box(0);
v_isShared_6990_ = v_isSharedCheck_7014_;
goto v_resetjp_6988_;
}
v_resetjp_6988_:
{
lean_object* v___x_6991_; lean_object* v___x_6992_; lean_object* v___x_6998_; lean_object* v___x_6999_; lean_object* v___x_7000_; uint8_t v___x_7001_; 
v___x_6991_ = l_Lean_Meta_LazyDiscrTree_ImportData_new();
lean_inc_ref(v_a_6981_);
v___x_6992_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(v_a_6981_, v_a_6987_, v_env_6985_, v___x_6991_, v_entriesForConst_6980_);
v___x_6998_ = lean_st_ref_get(v___x_6991_);
lean_dec(v___x_6991_);
v___x_6999_ = lean_unsigned_to_nat(0u);
v___x_7000_ = lean_array_get_size(v___x_6998_);
v___x_7001_ = lean_nat_dec_lt(v___x_6999_, v___x_7000_);
if (v___x_7001_ == 0)
{
lean_dec(v___x_6998_);
goto v___jp_6993_;
}
else
{
lean_object* v___x_7002_; size_t v___x_7003_; size_t v___x_7004_; lean_object* v___x_7005_; 
v___x_7002_ = lean_box(0);
v___x_7003_ = ((size_t)0ULL);
v___x_7004_ = lean_usize_of_nat(v___x_7000_);
v___x_7005_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2(v___x_6998_, v___x_7003_, v___x_7004_, v___x_7002_, v_a_6981_, v_a_6982_);
lean_dec(v___x_6998_);
if (lean_obj_tag(v___x_7005_) == 0)
{
lean_dec_ref_known(v___x_7005_, 1);
goto v___jp_6993_;
}
else
{
lean_object* v_a_7006_; lean_object* v___x_7008_; uint8_t v_isShared_7009_; uint8_t v_isSharedCheck_7013_; 
lean_dec_ref(v___x_6992_);
lean_del_object(v___x_6989_);
v_a_7006_ = lean_ctor_get(v___x_7005_, 0);
v_isSharedCheck_7013_ = !lean_is_exclusive(v___x_7005_);
if (v_isSharedCheck_7013_ == 0)
{
v___x_7008_ = v___x_7005_;
v_isShared_7009_ = v_isSharedCheck_7013_;
goto v_resetjp_7007_;
}
else
{
lean_inc(v_a_7006_);
lean_dec(v___x_7005_);
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
v___jp_6993_:
{
lean_object* v___x_6994_; lean_object* v___x_6996_; 
v___x_6994_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v___x_6992_);
if (v_isShared_6990_ == 0)
{
lean_ctor_set(v___x_6989_, 0, v___x_6994_);
v___x_6996_ = v___x_6989_;
goto v_reusejp_6995_;
}
else
{
lean_object* v_reuseFailAlloc_6997_; 
v_reuseFailAlloc_6997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6997_, 0, v___x_6994_);
v___x_6996_ = v_reuseFailAlloc_6997_;
goto v_reusejp_6995_;
}
v_reusejp_6995_:
{
return v___x_6996_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg___boxed(lean_object* v_entriesForConst_7015_, lean_object* v_a_7016_, lean_object* v_a_7017_, lean_object* v_a_7018_){
_start:
{
lean_object* v_res_7019_; 
v_res_7019_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(v_entriesForConst_7015_, v_a_7016_, v_a_7017_);
lean_dec(v_a_7017_);
lean_dec_ref(v_a_7016_);
return v_res_7019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree(lean_object* v_00_u03b1_7020_, lean_object* v_entriesForConst_7021_, lean_object* v_a_7022_, lean_object* v_a_7023_){
_start:
{
lean_object* v___x_7025_; 
v___x_7025_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(v_entriesForConst_7021_, v_a_7022_, v_a_7023_);
return v___x_7025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___boxed(lean_object* v_00_u03b1_7026_, lean_object* v_entriesForConst_7027_, lean_object* v_a_7028_, lean_object* v_a_7029_, lean_object* v_a_7030_){
_start:
{
lean_object* v_res_7031_; 
v_res_7031_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree(v_00_u03b1_7026_, v_entriesForConst_7027_, v_a_7028_, v_a_7029_);
lean_dec(v_a_7029_);
lean_dec_ref(v_a_7028_);
return v_res_7031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0(lean_object* v_entriesForConst_7032_, lean_object* v_droppedEntriesRef_7033_, lean_object* v_droppedKeys_7034_, lean_object* v___y_7035_, lean_object* v___y_7036_, lean_object* v___y_7037_, lean_object* v___y_7038_){
_start:
{
lean_object* v_t_7041_; lean_object* v___x_7044_; 
v___x_7044_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(v_entriesForConst_7032_, v___y_7037_, v___y_7038_);
if (lean_obj_tag(v___x_7044_) == 0)
{
if (lean_obj_tag(v_droppedEntriesRef_7033_) == 1)
{
lean_object* v_a_7045_; lean_object* v_val_7046_; lean_object* v___x_7048_; uint8_t v_isShared_7049_; uint8_t v_isSharedCheck_7072_; 
v_a_7045_ = lean_ctor_get(v___x_7044_, 0);
lean_inc(v_a_7045_);
lean_dec_ref_known(v___x_7044_, 1);
v_val_7046_ = lean_ctor_get(v_droppedEntriesRef_7033_, 0);
v_isSharedCheck_7072_ = !lean_is_exclusive(v_droppedEntriesRef_7033_);
if (v_isSharedCheck_7072_ == 0)
{
v___x_7048_ = v_droppedEntriesRef_7033_;
v_isShared_7049_ = v_isSharedCheck_7072_;
goto v_resetjp_7047_;
}
else
{
lean_inc(v_val_7046_);
lean_dec(v_droppedEntriesRef_7033_);
v___x_7048_ = lean_box(0);
v_isShared_7049_ = v_isSharedCheck_7072_;
goto v_resetjp_7047_;
}
v_resetjp_7047_:
{
lean_object* v___x_7050_; 
v___x_7050_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_a_7045_, v_droppedKeys_7034_, v___y_7035_, v___y_7036_, v___y_7037_, v___y_7038_);
lean_dec(v_droppedKeys_7034_);
if (lean_obj_tag(v___x_7050_) == 0)
{
lean_object* v_a_7051_; lean_object* v_fst_7052_; lean_object* v_snd_7053_; lean_object* v___x_7054_; lean_object* v___y_7056_; 
v_a_7051_ = lean_ctor_get(v___x_7050_, 0);
lean_inc(v_a_7051_);
lean_dec_ref_known(v___x_7050_, 1);
v_fst_7052_ = lean_ctor_get(v_a_7051_, 0);
lean_inc(v_fst_7052_);
v_snd_7053_ = lean_ctor_get(v_a_7051_, 1);
lean_inc(v_snd_7053_);
lean_dec(v_a_7051_);
v___x_7054_ = lean_st_ref_get(v_val_7046_);
if (lean_obj_tag(v___x_7054_) == 0)
{
lean_object* v___x_7062_; 
v___x_7062_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___redArg___closed__0));
v___y_7056_ = v___x_7062_;
goto v___jp_7055_;
}
else
{
lean_object* v_val_7063_; 
v_val_7063_ = lean_ctor_get(v___x_7054_, 0);
lean_inc(v_val_7063_);
lean_dec_ref_known(v___x_7054_, 1);
v___y_7056_ = v_val_7063_;
goto v___jp_7055_;
}
v___jp_7055_:
{
lean_object* v___x_7057_; lean_object* v___x_7059_; 
v___x_7057_ = l_Array_append___redArg(v___y_7056_, v_fst_7052_);
lean_dec(v_fst_7052_);
if (v_isShared_7049_ == 0)
{
lean_ctor_set(v___x_7048_, 0, v___x_7057_);
v___x_7059_ = v___x_7048_;
goto v_reusejp_7058_;
}
else
{
lean_object* v_reuseFailAlloc_7061_; 
v_reuseFailAlloc_7061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7061_, 0, v___x_7057_);
v___x_7059_ = v_reuseFailAlloc_7061_;
goto v_reusejp_7058_;
}
v_reusejp_7058_:
{
lean_object* v___x_7060_; 
v___x_7060_ = lean_st_ref_swap(v_val_7046_, v___x_7059_);
lean_dec(v_val_7046_);
lean_dec(v___x_7060_);
v_t_7041_ = v_snd_7053_;
goto v___jp_7040_;
}
}
}
else
{
lean_object* v_a_7064_; lean_object* v___x_7066_; uint8_t v_isShared_7067_; uint8_t v_isSharedCheck_7071_; 
lean_del_object(v___x_7048_);
lean_dec(v_val_7046_);
v_a_7064_ = lean_ctor_get(v___x_7050_, 0);
v_isSharedCheck_7071_ = !lean_is_exclusive(v___x_7050_);
if (v_isSharedCheck_7071_ == 0)
{
v___x_7066_ = v___x_7050_;
v_isShared_7067_ = v_isSharedCheck_7071_;
goto v_resetjp_7065_;
}
else
{
lean_inc(v_a_7064_);
lean_dec(v___x_7050_);
v___x_7066_ = lean_box(0);
v_isShared_7067_ = v_isSharedCheck_7071_;
goto v_resetjp_7065_;
}
v_resetjp_7065_:
{
lean_object* v___x_7069_; 
if (v_isShared_7067_ == 0)
{
v___x_7069_ = v___x_7066_;
goto v_reusejp_7068_;
}
else
{
lean_object* v_reuseFailAlloc_7070_; 
v_reuseFailAlloc_7070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7070_, 0, v_a_7064_);
v___x_7069_ = v_reuseFailAlloc_7070_;
goto v_reusejp_7068_;
}
v_reusejp_7068_:
{
return v___x_7069_;
}
}
}
}
}
else
{
lean_object* v_a_7073_; lean_object* v___x_7074_; 
lean_dec(v_droppedEntriesRef_7033_);
v_a_7073_ = lean_ctor_get(v___x_7044_, 0);
lean_inc(v_a_7073_);
lean_dec_ref_known(v___x_7044_, 1);
v___x_7074_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_a_7073_, v_droppedKeys_7034_, v___y_7035_, v___y_7036_, v___y_7037_, v___y_7038_);
if (lean_obj_tag(v___x_7074_) == 0)
{
lean_object* v_a_7075_; 
v_a_7075_ = lean_ctor_get(v___x_7074_, 0);
lean_inc(v_a_7075_);
lean_dec_ref_known(v___x_7074_, 1);
v_t_7041_ = v_a_7075_;
goto v___jp_7040_;
}
else
{
lean_object* v_a_7076_; lean_object* v___x_7078_; uint8_t v_isShared_7079_; uint8_t v_isSharedCheck_7083_; 
v_a_7076_ = lean_ctor_get(v___x_7074_, 0);
v_isSharedCheck_7083_ = !lean_is_exclusive(v___x_7074_);
if (v_isSharedCheck_7083_ == 0)
{
v___x_7078_ = v___x_7074_;
v_isShared_7079_ = v_isSharedCheck_7083_;
goto v_resetjp_7077_;
}
else
{
lean_inc(v_a_7076_);
lean_dec(v___x_7074_);
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
lean_object* v_a_7084_; lean_object* v___x_7086_; uint8_t v_isShared_7087_; uint8_t v_isSharedCheck_7091_; 
lean_dec(v_droppedKeys_7034_);
lean_dec(v_droppedEntriesRef_7033_);
v_a_7084_ = lean_ctor_get(v___x_7044_, 0);
v_isSharedCheck_7091_ = !lean_is_exclusive(v___x_7044_);
if (v_isSharedCheck_7091_ == 0)
{
v___x_7086_ = v___x_7044_;
v_isShared_7087_ = v_isSharedCheck_7091_;
goto v_resetjp_7085_;
}
else
{
lean_inc(v_a_7084_);
lean_dec(v___x_7044_);
v___x_7086_ = lean_box(0);
v_isShared_7087_ = v_isSharedCheck_7091_;
goto v_resetjp_7085_;
}
v_resetjp_7085_:
{
lean_object* v___x_7089_; 
if (v_isShared_7087_ == 0)
{
v___x_7089_ = v___x_7086_;
goto v_reusejp_7088_;
}
else
{
lean_object* v_reuseFailAlloc_7090_; 
v_reuseFailAlloc_7090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7090_, 0, v_a_7084_);
v___x_7089_ = v_reuseFailAlloc_7090_;
goto v_reusejp_7088_;
}
v_reusejp_7088_:
{
return v___x_7089_;
}
}
}
v___jp_7040_:
{
lean_object* v___x_7042_; lean_object* v___x_7043_; 
v___x_7042_ = lean_st_mk_ref(v_t_7041_);
v___x_7043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7043_, 0, v___x_7042_);
return v___x_7043_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0___boxed(lean_object* v_entriesForConst_7092_, lean_object* v_droppedEntriesRef_7093_, lean_object* v_droppedKeys_7094_, lean_object* v___y_7095_, lean_object* v___y_7096_, lean_object* v___y_7097_, lean_object* v___y_7098_, lean_object* v___y_7099_){
_start:
{
lean_object* v_res_7100_; 
v_res_7100_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0(v_entriesForConst_7092_, v_droppedEntriesRef_7093_, v_droppedKeys_7094_, v___y_7095_, v___y_7096_, v___y_7097_, v___y_7098_);
lean_dec(v___y_7098_);
lean_dec_ref(v___y_7097_);
lean_dec(v___y_7096_);
lean_dec_ref(v___y_7095_);
return v_res_7100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(lean_object* v_entriesForConst_7102_, lean_object* v_droppedKeys_7103_, lean_object* v_droppedEntriesRef_7104_, lean_object* v_a_7105_, lean_object* v_a_7106_, lean_object* v_a_7107_, lean_object* v_a_7108_){
_start:
{
lean_object* v___f_7110_; lean_object* v___x_7111_; lean_object* v___x_7112_; lean_object* v___x_7113_; lean_object* v___x_7114_; 
v___f_7110_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_7110_, 0, v_entriesForConst_7102_);
lean_closure_set(v___f_7110_, 1, v_droppedEntriesRef_7104_);
lean_closure_set(v___f_7110_, 2, v_droppedKeys_7103_);
v___x_7111_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_7107_);
v___x_7112_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___closed__0));
v___x_7113_ = lean_box(0);
v___x_7114_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v___x_7112_, v___x_7111_, v___f_7110_, v___x_7113_, v_a_7105_, v_a_7106_, v_a_7107_, v_a_7108_);
lean_dec_ref(v___x_7111_);
return v___x_7114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___boxed(lean_object* v_entriesForConst_7115_, lean_object* v_droppedKeys_7116_, lean_object* v_droppedEntriesRef_7117_, lean_object* v_a_7118_, lean_object* v_a_7119_, lean_object* v_a_7120_, lean_object* v_a_7121_, lean_object* v_a_7122_){
_start:
{
lean_object* v_res_7123_; 
v_res_7123_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v_entriesForConst_7115_, v_droppedKeys_7116_, v_droppedEntriesRef_7117_, v_a_7118_, v_a_7119_, v_a_7120_, v_a_7121_);
lean_dec(v_a_7121_);
lean_dec_ref(v_a_7120_);
lean_dec(v_a_7119_);
lean_dec_ref(v_a_7118_);
return v_res_7123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef(lean_object* v_00_u03b1_7124_, lean_object* v_entriesForConst_7125_, lean_object* v_droppedKeys_7126_, lean_object* v_droppedEntriesRef_7127_, lean_object* v_a_7128_, lean_object* v_a_7129_, lean_object* v_a_7130_, lean_object* v_a_7131_){
_start:
{
lean_object* v___x_7133_; 
v___x_7133_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v_entriesForConst_7125_, v_droppedKeys_7126_, v_droppedEntriesRef_7127_, v_a_7128_, v_a_7129_, v_a_7130_, v_a_7131_);
return v___x_7133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___boxed(lean_object* v_00_u03b1_7134_, lean_object* v_entriesForConst_7135_, lean_object* v_droppedKeys_7136_, lean_object* v_droppedEntriesRef_7137_, lean_object* v_a_7138_, lean_object* v_a_7139_, lean_object* v_a_7140_, lean_object* v_a_7141_, lean_object* v_a_7142_){
_start:
{
lean_object* v_res_7143_; 
v_res_7143_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef(v_00_u03b1_7134_, v_entriesForConst_7135_, v_droppedKeys_7136_, v_droppedEntriesRef_7137_, v_a_7138_, v_a_7139_, v_a_7140_, v_a_7141_);
lean_dec(v_a_7141_);
lean_dec_ref(v_a_7140_);
lean_dec(v_a_7139_);
lean_dec_ref(v_a_7138_);
return v_res_7143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0(lean_object* v_moduleRef_7144_, lean_object* v_ty_7145_, lean_object* v___y_7146_, lean_object* v___y_7147_, lean_object* v___y_7148_, lean_object* v___y_7149_){
_start:
{
lean_object* v___x_7151_; lean_object* v___x_7152_; 
v___x_7151_ = lean_st_ref_get(v_moduleRef_7144_);
v___x_7152_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v___x_7151_, v_ty_7145_, v___y_7146_, v___y_7147_, v___y_7148_, v___y_7149_);
if (lean_obj_tag(v___x_7152_) == 0)
{
lean_object* v_a_7153_; lean_object* v___x_7155_; uint8_t v_isShared_7156_; uint8_t v_isSharedCheck_7163_; 
v_a_7153_ = lean_ctor_get(v___x_7152_, 0);
v_isSharedCheck_7163_ = !lean_is_exclusive(v___x_7152_);
if (v_isSharedCheck_7163_ == 0)
{
v___x_7155_ = v___x_7152_;
v_isShared_7156_ = v_isSharedCheck_7163_;
goto v_resetjp_7154_;
}
else
{
lean_inc(v_a_7153_);
lean_dec(v___x_7152_);
v___x_7155_ = lean_box(0);
v_isShared_7156_ = v_isSharedCheck_7163_;
goto v_resetjp_7154_;
}
v_resetjp_7154_:
{
lean_object* v_fst_7157_; lean_object* v_snd_7158_; lean_object* v___x_7159_; lean_object* v___x_7161_; 
v_fst_7157_ = lean_ctor_get(v_a_7153_, 0);
lean_inc(v_fst_7157_);
v_snd_7158_ = lean_ctor_get(v_a_7153_, 1);
lean_inc(v_snd_7158_);
lean_dec(v_a_7153_);
v___x_7159_ = lean_st_ref_swap(v_moduleRef_7144_, v_snd_7158_);
lean_dec(v___x_7159_);
if (v_isShared_7156_ == 0)
{
lean_ctor_set(v___x_7155_, 0, v_fst_7157_);
v___x_7161_ = v___x_7155_;
goto v_reusejp_7160_;
}
else
{
lean_object* v_reuseFailAlloc_7162_; 
v_reuseFailAlloc_7162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7162_, 0, v_fst_7157_);
v___x_7161_ = v_reuseFailAlloc_7162_;
goto v_reusejp_7160_;
}
v_reusejp_7160_:
{
return v___x_7161_;
}
}
}
else
{
lean_object* v_a_7164_; lean_object* v___x_7166_; uint8_t v_isShared_7167_; uint8_t v_isSharedCheck_7171_; 
v_a_7164_ = lean_ctor_get(v___x_7152_, 0);
v_isSharedCheck_7171_ = !lean_is_exclusive(v___x_7152_);
if (v_isSharedCheck_7171_ == 0)
{
v___x_7166_ = v___x_7152_;
v_isShared_7167_ = v_isSharedCheck_7171_;
goto v_resetjp_7165_;
}
else
{
lean_inc(v_a_7164_);
lean_dec(v___x_7152_);
v___x_7166_ = lean_box(0);
v_isShared_7167_ = v_isSharedCheck_7171_;
goto v_resetjp_7165_;
}
v_resetjp_7165_:
{
lean_object* v___x_7169_; 
if (v_isShared_7167_ == 0)
{
v___x_7169_ = v___x_7166_;
goto v_reusejp_7168_;
}
else
{
lean_object* v_reuseFailAlloc_7170_; 
v_reuseFailAlloc_7170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7170_, 0, v_a_7164_);
v___x_7169_ = v_reuseFailAlloc_7170_;
goto v_reusejp_7168_;
}
v_reusejp_7168_:
{
return v___x_7169_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0___boxed(lean_object* v_moduleRef_7172_, lean_object* v_ty_7173_, lean_object* v___y_7174_, lean_object* v___y_7175_, lean_object* v___y_7176_, lean_object* v___y_7177_, lean_object* v___y_7178_){
_start:
{
lean_object* v_res_7179_; 
v_res_7179_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0(v_moduleRef_7172_, v_ty_7173_, v___y_7174_, v___y_7175_, v___y_7176_, v___y_7177_);
lean_dec(v___y_7177_);
lean_dec_ref(v___y_7176_);
lean_dec(v___y_7175_);
lean_dec_ref(v___y_7174_);
lean_dec(v_moduleRef_7172_);
return v_res_7179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(lean_object* v_moduleRef_7181_, lean_object* v_ty_7182_, lean_object* v_a_7183_, lean_object* v_a_7184_, lean_object* v_a_7185_, lean_object* v_a_7186_){
_start:
{
lean_object* v___f_7188_; lean_object* v___x_7189_; lean_object* v___x_7190_; lean_object* v___x_7191_; lean_object* v___x_7192_; 
v___f_7188_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_7188_, 0, v_moduleRef_7181_);
lean_closure_set(v___f_7188_, 1, v_ty_7182_);
v___x_7189_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_7185_);
v___x_7190_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___closed__0));
v___x_7191_ = lean_box(0);
v___x_7192_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v___x_7190_, v___x_7189_, v___f_7188_, v___x_7191_, v_a_7183_, v_a_7184_, v_a_7185_, v_a_7186_);
lean_dec_ref(v___x_7189_);
return v___x_7192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___boxed(lean_object* v_moduleRef_7193_, lean_object* v_ty_7194_, lean_object* v_a_7195_, lean_object* v_a_7196_, lean_object* v_a_7197_, lean_object* v_a_7198_, lean_object* v_a_7199_){
_start:
{
lean_object* v_res_7200_; 
v_res_7200_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(v_moduleRef_7193_, v_ty_7194_, v_a_7195_, v_a_7196_, v_a_7197_, v_a_7198_);
lean_dec(v_a_7198_);
lean_dec_ref(v_a_7197_);
lean_dec(v_a_7196_);
lean_dec_ref(v_a_7195_);
return v_res_7200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches(lean_object* v_00_u03b1_7201_, lean_object* v_moduleRef_7202_, lean_object* v_ty_7203_, lean_object* v_a_7204_, lean_object* v_a_7205_, lean_object* v_a_7206_, lean_object* v_a_7207_){
_start:
{
lean_object* v___x_7209_; 
v___x_7209_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(v_moduleRef_7202_, v_ty_7203_, v_a_7204_, v_a_7205_, v_a_7206_, v_a_7207_);
return v___x_7209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___boxed(lean_object* v_00_u03b1_7210_, lean_object* v_moduleRef_7211_, lean_object* v_ty_7212_, lean_object* v_a_7213_, lean_object* v_a_7214_, lean_object* v_a_7215_, lean_object* v_a_7216_, lean_object* v_a_7217_){
_start:
{
lean_object* v_res_7218_; 
v_res_7218_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches(v_00_u03b1_7210_, v_moduleRef_7211_, v_ty_7212_, v_a_7213_, v_a_7214_, v_a_7215_, v_a_7216_);
lean_dec(v_a_7216_);
lean_dec_ref(v_a_7215_);
lean_dec(v_a_7214_);
lean_dec_ref(v_a_7213_);
return v_res_7218_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(lean_object* v_adjustResult_7219_, lean_object* v_j_7220_, size_t v_sz_7221_, size_t v_i_7222_, lean_object* v_bs_7223_){
_start:
{
uint8_t v___x_7224_; 
v___x_7224_ = lean_usize_dec_lt(v_i_7222_, v_sz_7221_);
if (v___x_7224_ == 0)
{
lean_dec(v_j_7220_);
lean_dec(v_adjustResult_7219_);
return v_bs_7223_;
}
else
{
lean_object* v_v_7225_; lean_object* v___x_7226_; lean_object* v_bs_x27_7227_; lean_object* v___x_7228_; size_t v___x_7229_; size_t v___x_7230_; lean_object* v___x_7231_; 
v_v_7225_ = lean_array_uget(v_bs_7223_, v_i_7222_);
v___x_7226_ = lean_unsigned_to_nat(0u);
v_bs_x27_7227_ = lean_array_uset(v_bs_7223_, v_i_7222_, v___x_7226_);
lean_inc(v_adjustResult_7219_);
lean_inc(v_j_7220_);
v___x_7228_ = lean_apply_2(v_adjustResult_7219_, v_j_7220_, v_v_7225_);
v___x_7229_ = ((size_t)1ULL);
v___x_7230_ = lean_usize_add(v_i_7222_, v___x_7229_);
v___x_7231_ = lean_array_uset(v_bs_x27_7227_, v_i_7222_, v___x_7228_);
v_i_7222_ = v___x_7230_;
v_bs_7223_ = v___x_7231_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg___boxed(lean_object* v_adjustResult_7233_, lean_object* v_j_7234_, lean_object* v_sz_7235_, lean_object* v_i_7236_, lean_object* v_bs_7237_){
_start:
{
size_t v_sz_boxed_7238_; size_t v_i_boxed_7239_; lean_object* v_res_7240_; 
v_sz_boxed_7238_ = lean_unbox_usize(v_sz_7235_);
lean_dec(v_sz_7235_);
v_i_boxed_7239_ = lean_unbox_usize(v_i_7236_);
lean_dec(v_i_7236_);
v_res_7240_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(v_adjustResult_7233_, v_j_7234_, v_sz_boxed_7238_, v_i_boxed_7239_, v_bs_7237_);
return v_res_7240_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(lean_object* v_adjustResult_7241_, lean_object* v_j_7242_, lean_object* v_as_7243_, size_t v_i_7244_, size_t v_stop_7245_, lean_object* v_b_7246_){
_start:
{
uint8_t v___x_7247_; 
v___x_7247_ = lean_usize_dec_eq(v_i_7244_, v_stop_7245_);
if (v___x_7247_ == 0)
{
lean_object* v___x_7248_; size_t v_sz_7249_; size_t v___x_7250_; lean_object* v___x_7251_; lean_object* v___x_7252_; size_t v___x_7253_; size_t v___x_7254_; 
v___x_7248_ = lean_array_uget_borrowed(v_as_7243_, v_i_7244_);
v_sz_7249_ = lean_array_size(v___x_7248_);
v___x_7250_ = ((size_t)0ULL);
lean_inc(v___x_7248_);
lean_inc(v_j_7242_);
lean_inc(v_adjustResult_7241_);
v___x_7251_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(v_adjustResult_7241_, v_j_7242_, v_sz_7249_, v___x_7250_, v___x_7248_);
v___x_7252_ = l_Array_append___redArg(v_b_7246_, v___x_7251_);
lean_dec_ref(v___x_7251_);
v___x_7253_ = ((size_t)1ULL);
v___x_7254_ = lean_usize_add(v_i_7244_, v___x_7253_);
v_i_7244_ = v___x_7254_;
v_b_7246_ = v___x_7252_;
goto _start;
}
else
{
lean_dec(v_j_7242_);
lean_dec(v_adjustResult_7241_);
return v_b_7246_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg___boxed(lean_object* v_adjustResult_7256_, lean_object* v_j_7257_, lean_object* v_as_7258_, lean_object* v_i_7259_, lean_object* v_stop_7260_, lean_object* v_b_7261_){
_start:
{
size_t v_i_boxed_7262_; size_t v_stop_boxed_7263_; lean_object* v_res_7264_; 
v_i_boxed_7262_ = lean_unbox_usize(v_i_7259_);
lean_dec(v_i_7259_);
v_stop_boxed_7263_ = lean_unbox_usize(v_stop_7260_);
lean_dec(v_stop_7260_);
v_res_7264_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7256_, v_j_7257_, v_as_7258_, v_i_boxed_7262_, v_stop_boxed_7263_, v_b_7261_);
lean_dec_ref(v_as_7258_);
return v_res_7264_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(lean_object* v_n_7265_, lean_object* v_aa_7266_, lean_object* v_adjustResult_7267_, lean_object* v_n_7268_, lean_object* v_j_7269_, lean_object* v_a_7270_){
_start:
{
lean_object* v_zero_7271_; uint8_t v_isZero_7272_; 
v_zero_7271_ = lean_unsigned_to_nat(0u);
v_isZero_7272_ = lean_nat_dec_eq(v_j_7269_, v_zero_7271_);
if (v_isZero_7272_ == 1)
{
lean_dec(v_j_7269_);
lean_dec(v_adjustResult_7267_);
return v_a_7270_;
}
else
{
lean_object* v_one_7273_; lean_object* v_n_7274_; lean_object* v___x_7275_; lean_object* v___x_7276_; lean_object* v_j_7277_; lean_object* v_b_7278_; lean_object* v___x_7279_; uint8_t v___x_7280_; 
v_one_7273_ = lean_unsigned_to_nat(1u);
v_n_7274_ = lean_nat_sub(v_j_7269_, v_one_7273_);
v___x_7275_ = lean_nat_sub(v_n_7268_, v_j_7269_);
lean_dec(v_j_7269_);
v___x_7276_ = lean_nat_sub(v_n_7265_, v_one_7273_);
v_j_7277_ = lean_nat_sub(v___x_7276_, v___x_7275_);
lean_dec(v___x_7275_);
lean_dec(v___x_7276_);
v_b_7278_ = lean_array_fget_borrowed(v_aa_7266_, v_j_7277_);
v___x_7279_ = lean_array_get_size(v_b_7278_);
v___x_7280_ = lean_nat_dec_lt(v_zero_7271_, v___x_7279_);
if (v___x_7280_ == 0)
{
lean_dec(v_j_7277_);
v_j_7269_ = v_n_7274_;
goto _start;
}
else
{
size_t v___x_7282_; size_t v___x_7283_; lean_object* v___x_7284_; 
v___x_7282_ = ((size_t)0ULL);
v___x_7283_ = lean_usize_of_nat(v___x_7279_);
lean_inc(v_adjustResult_7267_);
v___x_7284_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7267_, v_j_7277_, v_b_7278_, v___x_7282_, v___x_7283_, v_a_7270_);
v_j_7269_ = v_n_7274_;
v_a_7270_ = v___x_7284_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_n_7286_, lean_object* v_aa_7287_, lean_object* v_adjustResult_7288_, lean_object* v_n_7289_, lean_object* v_j_7290_, lean_object* v_a_7291_){
_start:
{
lean_object* v_res_7292_; 
v_res_7292_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7286_, v_aa_7287_, v_adjustResult_7288_, v_n_7289_, v_j_7290_, v_a_7291_);
lean_dec(v_n_7289_);
lean_dec_ref(v_aa_7287_);
lean_dec(v_n_7286_);
return v_res_7292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(lean_object* v_n_7293_, lean_object* v_adjustResult_7294_, lean_object* v_aa_7295_, lean_object* v_n_7296_, lean_object* v_j_7297_, lean_object* v_a_7298_){
_start:
{
lean_object* v_zero_7299_; uint8_t v_isZero_7300_; 
v_zero_7299_ = lean_unsigned_to_nat(0u);
v_isZero_7300_ = lean_nat_dec_eq(v_j_7297_, v_zero_7299_);
if (v_isZero_7300_ == 1)
{
lean_dec(v_adjustResult_7294_);
return v_a_7298_;
}
else
{
lean_object* v_one_7301_; lean_object* v_n_7302_; lean_object* v___x_7303_; lean_object* v___x_7304_; lean_object* v_j_7305_; lean_object* v_b_7306_; lean_object* v___x_7307_; uint8_t v___x_7308_; 
v_one_7301_ = lean_unsigned_to_nat(1u);
v_n_7302_ = lean_nat_sub(v_j_7297_, v_one_7301_);
v___x_7303_ = lean_nat_sub(v_n_7296_, v_j_7297_);
v___x_7304_ = lean_nat_sub(v_n_7293_, v_one_7301_);
v_j_7305_ = lean_nat_sub(v___x_7304_, v___x_7303_);
lean_dec(v___x_7303_);
lean_dec(v___x_7304_);
v_b_7306_ = lean_array_fget_borrowed(v_aa_7295_, v_j_7305_);
v___x_7307_ = lean_array_get_size(v_b_7306_);
v___x_7308_ = lean_nat_dec_lt(v_zero_7299_, v___x_7307_);
if (v___x_7308_ == 0)
{
lean_object* v___x_7309_; 
lean_dec(v_j_7305_);
v___x_7309_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7293_, v_aa_7295_, v_adjustResult_7294_, v_n_7296_, v_n_7302_, v_a_7298_);
return v___x_7309_;
}
else
{
size_t v___x_7310_; size_t v___x_7311_; lean_object* v___x_7312_; lean_object* v___x_7313_; 
v___x_7310_ = ((size_t)0ULL);
v___x_7311_ = lean_usize_of_nat(v___x_7307_);
lean_inc(v_adjustResult_7294_);
v___x_7312_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7294_, v_j_7305_, v_b_7306_, v___x_7310_, v___x_7311_, v_a_7298_);
v___x_7313_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7293_, v_aa_7295_, v_adjustResult_7294_, v_n_7296_, v_n_7302_, v___x_7312_);
return v___x_7313_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg___boxed(lean_object* v_n_7314_, lean_object* v_adjustResult_7315_, lean_object* v_aa_7316_, lean_object* v_n_7317_, lean_object* v_j_7318_, lean_object* v_a_7319_){
_start:
{
lean_object* v_res_7320_; 
v_res_7320_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(v_n_7314_, v_adjustResult_7315_, v_aa_7316_, v_n_7317_, v_j_7318_, v_a_7319_);
lean_dec(v_j_7318_);
lean_dec(v_n_7317_);
lean_dec_ref(v_aa_7316_);
lean_dec(v_n_7314_);
return v_res_7320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(lean_object* v_adjustResult_7321_, lean_object* v_mr_7322_, lean_object* v_a_7323_){
_start:
{
lean_object* v_n_7324_; lean_object* v___x_7325_; 
v_n_7324_ = lean_array_get_size(v_mr_7322_);
v___x_7325_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(v_n_7324_, v_adjustResult_7321_, v_mr_7322_, v_n_7324_, v_n_7324_, v_a_7323_);
return v___x_7325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg___boxed(lean_object* v_adjustResult_7326_, lean_object* v_mr_7327_, lean_object* v_a_7328_){
_start:
{
lean_object* v_res_7329_; 
v_res_7329_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7326_, v_mr_7327_, v_a_7328_);
lean_dec_ref(v_mr_7327_);
return v_res_7329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(lean_object* v_moduleTreeRef_7330_, lean_object* v_ref_7331_, lean_object* v_addEntry_7332_, lean_object* v_droppedKeys_7333_, lean_object* v_constantsPerTask_7334_, lean_object* v_droppedEntriesRef_7335_, lean_object* v_adjustResult_7336_, lean_object* v_ty_7337_, lean_object* v_a_7338_, lean_object* v_a_7339_, lean_object* v_a_7340_, lean_object* v_a_7341_){
_start:
{
lean_object* v___x_7343_; 
lean_inc_ref(v_ty_7337_);
v___x_7343_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(v_moduleTreeRef_7330_, v_ty_7337_, v_a_7338_, v_a_7339_, v_a_7340_, v_a_7341_);
if (lean_obj_tag(v___x_7343_) == 0)
{
lean_object* v_a_7344_; lean_object* v___x_7345_; 
v_a_7344_ = lean_ctor_get(v___x_7343_, 0);
lean_inc(v_a_7344_);
lean_dec_ref_known(v___x_7343_, 1);
v___x_7345_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(v_ref_7331_, v_addEntry_7332_, v_droppedKeys_7333_, v_constantsPerTask_7334_, v_droppedEntriesRef_7335_, v_ty_7337_, v_a_7338_, v_a_7339_, v_a_7340_, v_a_7341_);
if (lean_obj_tag(v___x_7345_) == 0)
{
lean_object* v_a_7346_; lean_object* v___x_7348_; uint8_t v_isShared_7349_; uint8_t v_isSharedCheck_7359_; 
v_a_7346_ = lean_ctor_get(v___x_7345_, 0);
v_isSharedCheck_7359_ = !lean_is_exclusive(v___x_7345_);
if (v_isSharedCheck_7359_ == 0)
{
v___x_7348_ = v___x_7345_;
v_isShared_7349_ = v_isSharedCheck_7359_;
goto v_resetjp_7347_;
}
else
{
lean_inc(v_a_7346_);
lean_dec(v___x_7345_);
v___x_7348_ = lean_box(0);
v_isShared_7349_ = v_isSharedCheck_7359_;
goto v_resetjp_7347_;
}
v_resetjp_7347_:
{
lean_object* v___x_7350_; lean_object* v___x_7351_; lean_object* v___x_7352_; lean_object* v___x_7353_; lean_object* v___x_7354_; lean_object* v___x_7355_; lean_object* v___x_7357_; 
v___x_7350_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_a_7344_);
v___x_7351_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_a_7346_);
v___x_7352_ = lean_nat_add(v___x_7350_, v___x_7351_);
lean_dec(v___x_7351_);
lean_dec(v___x_7350_);
v___x_7353_ = lean_mk_empty_array_with_capacity(v___x_7352_);
lean_dec(v___x_7352_);
lean_inc(v_adjustResult_7336_);
v___x_7354_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7336_, v_a_7344_, v___x_7353_);
lean_dec(v_a_7344_);
v___x_7355_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7336_, v_a_7346_, v___x_7354_);
lean_dec(v_a_7346_);
if (v_isShared_7349_ == 0)
{
lean_ctor_set(v___x_7348_, 0, v___x_7355_);
v___x_7357_ = v___x_7348_;
goto v_reusejp_7356_;
}
else
{
lean_object* v_reuseFailAlloc_7358_; 
v_reuseFailAlloc_7358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7358_, 0, v___x_7355_);
v___x_7357_ = v_reuseFailAlloc_7358_;
goto v_reusejp_7356_;
}
v_reusejp_7356_:
{
return v___x_7357_;
}
}
}
else
{
lean_object* v_a_7360_; lean_object* v___x_7362_; uint8_t v_isShared_7363_; uint8_t v_isSharedCheck_7367_; 
lean_dec(v_a_7344_);
lean_dec(v_adjustResult_7336_);
v_a_7360_ = lean_ctor_get(v___x_7345_, 0);
v_isSharedCheck_7367_ = !lean_is_exclusive(v___x_7345_);
if (v_isSharedCheck_7367_ == 0)
{
v___x_7362_ = v___x_7345_;
v_isShared_7363_ = v_isSharedCheck_7367_;
goto v_resetjp_7361_;
}
else
{
lean_inc(v_a_7360_);
lean_dec(v___x_7345_);
v___x_7362_ = lean_box(0);
v_isShared_7363_ = v_isSharedCheck_7367_;
goto v_resetjp_7361_;
}
v_resetjp_7361_:
{
lean_object* v___x_7365_; 
if (v_isShared_7363_ == 0)
{
v___x_7365_ = v___x_7362_;
goto v_reusejp_7364_;
}
else
{
lean_object* v_reuseFailAlloc_7366_; 
v_reuseFailAlloc_7366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7366_, 0, v_a_7360_);
v___x_7365_ = v_reuseFailAlloc_7366_;
goto v_reusejp_7364_;
}
v_reusejp_7364_:
{
return v___x_7365_;
}
}
}
}
else
{
lean_object* v_a_7368_; lean_object* v___x_7370_; uint8_t v_isShared_7371_; uint8_t v_isSharedCheck_7375_; 
lean_dec_ref(v_ty_7337_);
lean_dec(v_adjustResult_7336_);
lean_dec(v_droppedEntriesRef_7335_);
lean_dec(v_constantsPerTask_7334_);
lean_dec(v_droppedKeys_7333_);
lean_dec_ref(v_addEntry_7332_);
v_a_7368_ = lean_ctor_get(v___x_7343_, 0);
v_isSharedCheck_7375_ = !lean_is_exclusive(v___x_7343_);
if (v_isSharedCheck_7375_ == 0)
{
v___x_7370_ = v___x_7343_;
v_isShared_7371_ = v_isSharedCheck_7375_;
goto v_resetjp_7369_;
}
else
{
lean_inc(v_a_7368_);
lean_dec(v___x_7343_);
v___x_7370_ = lean_box(0);
v_isShared_7371_ = v_isSharedCheck_7375_;
goto v_resetjp_7369_;
}
v_resetjp_7369_:
{
lean_object* v___x_7373_; 
if (v_isShared_7371_ == 0)
{
v___x_7373_ = v___x_7370_;
goto v_reusejp_7372_;
}
else
{
lean_object* v_reuseFailAlloc_7374_; 
v_reuseFailAlloc_7374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7374_, 0, v_a_7368_);
v___x_7373_ = v_reuseFailAlloc_7374_;
goto v_reusejp_7372_;
}
v_reusejp_7372_:
{
return v___x_7373_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg___boxed(lean_object* v_moduleTreeRef_7376_, lean_object* v_ref_7377_, lean_object* v_addEntry_7378_, lean_object* v_droppedKeys_7379_, lean_object* v_constantsPerTask_7380_, lean_object* v_droppedEntriesRef_7381_, lean_object* v_adjustResult_7382_, lean_object* v_ty_7383_, lean_object* v_a_7384_, lean_object* v_a_7385_, lean_object* v_a_7386_, lean_object* v_a_7387_, lean_object* v_a_7388_){
_start:
{
lean_object* v_res_7389_; 
v_res_7389_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_moduleTreeRef_7376_, v_ref_7377_, v_addEntry_7378_, v_droppedKeys_7379_, v_constantsPerTask_7380_, v_droppedEntriesRef_7381_, v_adjustResult_7382_, v_ty_7383_, v_a_7384_, v_a_7385_, v_a_7386_, v_a_7387_);
lean_dec(v_a_7387_);
lean_dec_ref(v_a_7386_);
lean_dec(v_a_7385_);
lean_dec_ref(v_a_7384_);
lean_dec(v_ref_7377_);
return v_res_7389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt(lean_object* v_00_u03b1_7390_, lean_object* v_00_u03b2_7391_, lean_object* v_moduleTreeRef_7392_, lean_object* v_ref_7393_, lean_object* v_addEntry_7394_, lean_object* v_droppedKeys_7395_, lean_object* v_constantsPerTask_7396_, lean_object* v_droppedEntriesRef_7397_, lean_object* v_adjustResult_7398_, lean_object* v_ty_7399_, lean_object* v_a_7400_, lean_object* v_a_7401_, lean_object* v_a_7402_, lean_object* v_a_7403_){
_start:
{
lean_object* v___x_7405_; 
v___x_7405_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_moduleTreeRef_7392_, v_ref_7393_, v_addEntry_7394_, v_droppedKeys_7395_, v_constantsPerTask_7396_, v_droppedEntriesRef_7397_, v_adjustResult_7398_, v_ty_7399_, v_a_7400_, v_a_7401_, v_a_7402_, v_a_7403_);
return v___x_7405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___boxed(lean_object* v_00_u03b1_7406_, lean_object* v_00_u03b2_7407_, lean_object* v_moduleTreeRef_7408_, lean_object* v_ref_7409_, lean_object* v_addEntry_7410_, lean_object* v_droppedKeys_7411_, lean_object* v_constantsPerTask_7412_, lean_object* v_droppedEntriesRef_7413_, lean_object* v_adjustResult_7414_, lean_object* v_ty_7415_, lean_object* v_a_7416_, lean_object* v_a_7417_, lean_object* v_a_7418_, lean_object* v_a_7419_, lean_object* v_a_7420_){
_start:
{
lean_object* v_res_7421_; 
v_res_7421_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt(v_00_u03b1_7406_, v_00_u03b2_7407_, v_moduleTreeRef_7408_, v_ref_7409_, v_addEntry_7410_, v_droppedKeys_7411_, v_constantsPerTask_7412_, v_droppedEntriesRef_7413_, v_adjustResult_7414_, v_ty_7415_, v_a_7416_, v_a_7417_, v_a_7418_, v_a_7419_);
lean_dec(v_a_7419_);
lean_dec_ref(v_a_7418_);
lean_dec(v_a_7417_);
lean_dec_ref(v_a_7416_);
lean_dec(v_ref_7409_);
return v_res_7421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0(lean_object* v_00_u03b1_7422_, lean_object* v_00_u03b2_7423_, lean_object* v_adjustResult_7424_, lean_object* v_mr_7425_, lean_object* v_a_7426_){
_start:
{
lean_object* v___x_7427_; 
v___x_7427_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7424_, v_mr_7425_, v_a_7426_);
return v___x_7427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___boxed(lean_object* v_00_u03b1_7428_, lean_object* v_00_u03b2_7429_, lean_object* v_adjustResult_7430_, lean_object* v_mr_7431_, lean_object* v_a_7432_){
_start:
{
lean_object* v_res_7433_; 
v_res_7433_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0(v_00_u03b1_7428_, v_00_u03b2_7429_, v_adjustResult_7430_, v_mr_7431_, v_a_7432_);
lean_dec_ref(v_mr_7431_);
return v_res_7433_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0(lean_object* v_00_u03b1_7434_, lean_object* v_00_u03b2_7435_, lean_object* v_adjustResult_7436_, lean_object* v_j_7437_, size_t v_sz_7438_, size_t v_i_7439_, lean_object* v_bs_7440_){
_start:
{
lean_object* v___x_7441_; 
v___x_7441_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(v_adjustResult_7436_, v_j_7437_, v_sz_7438_, v_i_7439_, v_bs_7440_);
return v___x_7441_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___boxed(lean_object* v_00_u03b1_7442_, lean_object* v_00_u03b2_7443_, lean_object* v_adjustResult_7444_, lean_object* v_j_7445_, lean_object* v_sz_7446_, lean_object* v_i_7447_, lean_object* v_bs_7448_){
_start:
{
size_t v_sz_boxed_7449_; size_t v_i_boxed_7450_; lean_object* v_res_7451_; 
v_sz_boxed_7449_ = lean_unbox_usize(v_sz_7446_);
lean_dec(v_sz_7446_);
v_i_boxed_7450_ = lean_unbox_usize(v_i_7447_);
lean_dec(v_i_7447_);
v_res_7451_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0(v_00_u03b1_7442_, v_00_u03b2_7443_, v_adjustResult_7444_, v_j_7445_, v_sz_boxed_7449_, v_i_boxed_7450_, v_bs_7448_);
return v_res_7451_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1(lean_object* v_00_u03b1_7452_, lean_object* v_00_u03b2_7453_, lean_object* v_adjustResult_7454_, lean_object* v_j_7455_, lean_object* v_as_7456_, size_t v_i_7457_, size_t v_stop_7458_, lean_object* v_b_7459_){
_start:
{
lean_object* v___x_7460_; 
v___x_7460_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7454_, v_j_7455_, v_as_7456_, v_i_7457_, v_stop_7458_, v_b_7459_);
return v___x_7460_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___boxed(lean_object* v_00_u03b1_7461_, lean_object* v_00_u03b2_7462_, lean_object* v_adjustResult_7463_, lean_object* v_j_7464_, lean_object* v_as_7465_, lean_object* v_i_7466_, lean_object* v_stop_7467_, lean_object* v_b_7468_){
_start:
{
size_t v_i_boxed_7469_; size_t v_stop_boxed_7470_; lean_object* v_res_7471_; 
v_i_boxed_7469_ = lean_unbox_usize(v_i_7466_);
lean_dec(v_i_7466_);
v_stop_boxed_7470_ = lean_unbox_usize(v_stop_7467_);
lean_dec(v_stop_7467_);
v_res_7471_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1(v_00_u03b1_7461_, v_00_u03b2_7462_, v_adjustResult_7463_, v_j_7464_, v_as_7465_, v_i_boxed_7469_, v_stop_boxed_7470_, v_b_7468_);
lean_dec_ref(v_as_7465_);
return v_res_7471_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2(lean_object* v_00_u03b2_7472_, lean_object* v_n_7473_, lean_object* v_00_u03b1_7474_, lean_object* v_adjustResult_7475_, lean_object* v_aa_7476_, lean_object* v_n_7477_, lean_object* v_j_7478_, lean_object* v_a_7479_, lean_object* v_a_7480_){
_start:
{
lean_object* v___x_7481_; 
v___x_7481_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(v_n_7473_, v_adjustResult_7475_, v_aa_7476_, v_n_7477_, v_j_7478_, v_a_7480_);
return v___x_7481_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___boxed(lean_object* v_00_u03b2_7482_, lean_object* v_n_7483_, lean_object* v_00_u03b1_7484_, lean_object* v_adjustResult_7485_, lean_object* v_aa_7486_, lean_object* v_n_7487_, lean_object* v_j_7488_, lean_object* v_a_7489_, lean_object* v_a_7490_){
_start:
{
lean_object* v_res_7491_; 
v_res_7491_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2(v_00_u03b2_7482_, v_n_7483_, v_00_u03b1_7484_, v_adjustResult_7485_, v_aa_7486_, v_n_7487_, v_j_7488_, v_a_7489_, v_a_7490_);
lean_dec(v_j_7488_);
lean_dec(v_n_7487_);
lean_dec_ref(v_aa_7486_);
lean_dec(v_n_7483_);
return v_res_7491_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_7492_, lean_object* v_n_7493_, lean_object* v_00_u03b1_7494_, lean_object* v_aa_7495_, lean_object* v_adjustResult_7496_, lean_object* v_n_7497_, lean_object* v_j_7498_, lean_object* v_a_7499_, lean_object* v_a_7500_){
_start:
{
lean_object* v___x_7501_; 
v___x_7501_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7493_, v_aa_7495_, v_adjustResult_7496_, v_n_7497_, v_j_7498_, v_a_7500_);
return v___x_7501_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b2_7502_, lean_object* v_n_7503_, lean_object* v_00_u03b1_7504_, lean_object* v_aa_7505_, lean_object* v_adjustResult_7506_, lean_object* v_n_7507_, lean_object* v_j_7508_, lean_object* v_a_7509_, lean_object* v_a_7510_){
_start:
{
lean_object* v_res_7511_; 
v_res_7511_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3(v_00_u03b2_7502_, v_n_7503_, v_00_u03b1_7504_, v_aa_7505_, v_adjustResult_7506_, v_n_7507_, v_j_7508_, v_a_7509_, v_a_7510_);
lean_dec(v_n_7507_);
lean_dec_ref(v_aa_7505_);
lean_dec(v_n_7503_);
return v_res_7511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg___lam__0(lean_object* v_x_7512_, lean_object* v_v_7513_){
_start:
{
lean_inc(v_v_7513_);
return v_v_7513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg___lam__0___boxed(lean_object* v_x_7514_, lean_object* v_v_7515_){
_start:
{
lean_object* v_res_7516_; 
v_res_7516_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg___lam__0(v_x_7514_, v_v_7515_);
lean_dec(v_v_7515_);
lean_dec(v_x_7514_);
return v_res_7516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg(lean_object* v_ref_7518_, lean_object* v_addEntry_7519_, lean_object* v_droppedKeys_7520_, lean_object* v_constantsPerTask_7521_, lean_object* v_droppedEntriesRef_7522_, lean_object* v_ty_7523_, lean_object* v_a_7524_, lean_object* v_a_7525_, lean_object* v_a_7526_, lean_object* v_a_7527_){
_start:
{
lean_object* v___f_7529_; lean_object* v___x_7530_; 
v___f_7529_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_findMatches___redArg___closed__0));
lean_inc(v_droppedEntriesRef_7522_);
lean_inc(v_droppedKeys_7520_);
lean_inc_ref(v_addEntry_7519_);
v___x_7530_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v_addEntry_7519_, v_droppedKeys_7520_, v_droppedEntriesRef_7522_, v_a_7524_, v_a_7525_, v_a_7526_, v_a_7527_);
if (lean_obj_tag(v___x_7530_) == 0)
{
lean_object* v_a_7531_; lean_object* v___x_7532_; 
v_a_7531_ = lean_ctor_get(v___x_7530_, 0);
lean_inc(v_a_7531_);
lean_dec_ref_known(v___x_7530_, 1);
v___x_7532_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_a_7531_, v_ref_7518_, v_addEntry_7519_, v_droppedKeys_7520_, v_constantsPerTask_7521_, v_droppedEntriesRef_7522_, v___f_7529_, v_ty_7523_, v_a_7524_, v_a_7525_, v_a_7526_, v_a_7527_);
return v___x_7532_;
}
else
{
lean_object* v_a_7533_; lean_object* v___x_7535_; uint8_t v_isShared_7536_; uint8_t v_isSharedCheck_7540_; 
lean_dec_ref(v_ty_7523_);
lean_dec(v_droppedEntriesRef_7522_);
lean_dec(v_constantsPerTask_7521_);
lean_dec(v_droppedKeys_7520_);
lean_dec_ref(v_addEntry_7519_);
v_a_7533_ = lean_ctor_get(v___x_7530_, 0);
v_isSharedCheck_7540_ = !lean_is_exclusive(v___x_7530_);
if (v_isSharedCheck_7540_ == 0)
{
v___x_7535_ = v___x_7530_;
v_isShared_7536_ = v_isSharedCheck_7540_;
goto v_resetjp_7534_;
}
else
{
lean_inc(v_a_7533_);
lean_dec(v___x_7530_);
v___x_7535_ = lean_box(0);
v_isShared_7536_ = v_isSharedCheck_7540_;
goto v_resetjp_7534_;
}
v_resetjp_7534_:
{
lean_object* v___x_7538_; 
if (v_isShared_7536_ == 0)
{
v___x_7538_ = v___x_7535_;
goto v_reusejp_7537_;
}
else
{
lean_object* v_reuseFailAlloc_7539_; 
v_reuseFailAlloc_7539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7539_, 0, v_a_7533_);
v___x_7538_ = v_reuseFailAlloc_7539_;
goto v_reusejp_7537_;
}
v_reusejp_7537_:
{
return v___x_7538_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg___boxed(lean_object* v_ref_7541_, lean_object* v_addEntry_7542_, lean_object* v_droppedKeys_7543_, lean_object* v_constantsPerTask_7544_, lean_object* v_droppedEntriesRef_7545_, lean_object* v_ty_7546_, lean_object* v_a_7547_, lean_object* v_a_7548_, lean_object* v_a_7549_, lean_object* v_a_7550_, lean_object* v_a_7551_){
_start:
{
lean_object* v_res_7552_; 
v_res_7552_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg(v_ref_7541_, v_addEntry_7542_, v_droppedKeys_7543_, v_constantsPerTask_7544_, v_droppedEntriesRef_7545_, v_ty_7546_, v_a_7547_, v_a_7548_, v_a_7549_, v_a_7550_);
lean_dec(v_a_7550_);
lean_dec_ref(v_a_7549_);
lean_dec(v_a_7548_);
lean_dec_ref(v_a_7547_);
lean_dec(v_ref_7541_);
return v_res_7552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches(lean_object* v_00_u03b1_7553_, lean_object* v_ref_7554_, lean_object* v_addEntry_7555_, lean_object* v_droppedKeys_7556_, lean_object* v_constantsPerTask_7557_, lean_object* v_droppedEntriesRef_7558_, lean_object* v_ty_7559_, lean_object* v_a_7560_, lean_object* v_a_7561_, lean_object* v_a_7562_, lean_object* v_a_7563_){
_start:
{
lean_object* v___x_7565_; 
v___x_7565_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg(v_ref_7554_, v_addEntry_7555_, v_droppedKeys_7556_, v_constantsPerTask_7557_, v_droppedEntriesRef_7558_, v_ty_7559_, v_a_7560_, v_a_7561_, v_a_7562_, v_a_7563_);
return v___x_7565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___boxed(lean_object* v_00_u03b1_7566_, lean_object* v_ref_7567_, lean_object* v_addEntry_7568_, lean_object* v_droppedKeys_7569_, lean_object* v_constantsPerTask_7570_, lean_object* v_droppedEntriesRef_7571_, lean_object* v_ty_7572_, lean_object* v_a_7573_, lean_object* v_a_7574_, lean_object* v_a_7575_, lean_object* v_a_7576_, lean_object* v_a_7577_){
_start:
{
lean_object* v_res_7578_; 
v_res_7578_ = l_Lean_Meta_LazyDiscrTree_findMatches(v_00_u03b1_7566_, v_ref_7567_, v_addEntry_7568_, v_droppedKeys_7569_, v_constantsPerTask_7570_, v_droppedEntriesRef_7571_, v_ty_7572_, v_a_7573_, v_a_7574_, v_a_7575_, v_a_7576_);
lean_dec(v_a_7576_);
lean_dec_ref(v_a_7575_);
lean_dec(v_a_7574_);
lean_dec_ref(v_a_7573_);
lean_dec(v_ref_7567_);
return v_res_7578_;
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
